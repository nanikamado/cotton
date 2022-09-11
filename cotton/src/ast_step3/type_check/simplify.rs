use crate::ast_step2::{
    self,
    decl_id::DeclId,
    types::{
        unwrap_or_clone, Type, TypeMatchable, TypeMatchableRef, TypeUnit,
        TypeVariable,
    },
    IncompleteType, PatternForRestriction, PatternRestrictions,
    PatternUnitForRestriction, SubtypeRelations, TypeConstructor,
};
use fxhash::{FxHashMap, FxHashSet};
use hashbag::HashBag;
use itertools::Itertools;
use petgraph::{self, algo::tarjan_scc, graphmap::DiGraphMap};
use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    fmt::Display,
    iter::Extend,
    vec,
};

use super::VariableRequirement;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct TypeVariableMap<'a>(BTreeMap<TypeVariable, Type<'a>>);

impl<'a> TypeVariableMap<'a> {
    pub fn find(&mut self, key: TypeVariable) -> Type<'a> {
        if let Some(t) = self.0.get(&key).cloned() {
            let t_new = self.normalize_type(t.clone());
            if t_new == t {
                t
            } else {
                self.0.insert(key, t_new.clone());
                t_new
            }
        } else {
            TypeUnit::Variable(key).into()
        }
    }

    pub fn normalize_type(&mut self, t: Type<'a>) -> Type<'a> {
        let tus: Vec<_> = t
            .into_iter()
            .flat_map(|tu| match unwrap_or_clone(tu) {
                TypeUnit::Fn(arg, rtn) => TypeUnit::Fn(
                    self.normalize_type(arg),
                    self.normalize_type(rtn),
                )
                .into(),
                TypeUnit::Variable(v) => self.find(v),
                TypeUnit::RecursiveAlias { body } => {
                    let body = self.normalize_type(body);
                    match body.matchable() {
                        TypeMatchable::RecursiveAlias { body } => {
                            TypeUnit::RecursiveAlias {
                                body: body.decrement_recursive_index(1),
                            }
                            .into()
                        }
                        body => TypeUnit::RecursiveAlias { body: body.into() }
                            .into(),
                    }
                }
                TypeUnit::Normal { name, args, id } => TypeUnit::Normal {
                    name,
                    args: args
                        .into_iter()
                        .map(|t| self.normalize_type(t))
                        .collect(),
                    id,
                }
                .into(),
            })
            .collect::<Type>()
            .into_iter()
            .collect();
        let mut needless = HashSet::new();
        for (a, b) in tus.iter().tuple_combinations() {
            if let Some(r) = simplify_subtype_rel(
                a.clone().into(),
                b.clone().into(),
                &mut Default::default(),
            ) {
                if r.is_empty() {
                    needless.insert(a.clone());
                    continue;
                }
            }
            if let Some(r) = simplify_subtype_rel(
                b.clone().into(),
                a.clone().into(),
                &mut Default::default(),
            ) {
                if r.is_empty() {
                    needless.insert(b.clone());
                }
            }
        }
        tus.into_iter().filter(|t| !needless.contains(t)).collect()
    }

    fn normalize_pattern_unit(
        &mut self,
        pattern_unit: PatternUnitForRestriction<'a>,
    ) -> PatternUnitForRestriction<'a> {
        use PatternUnitForRestriction::*;
        match pattern_unit {
            I64 => I64,
            Str => Str,
            Constructor { id, name, args } => Constructor {
                id,
                name,
                args: args
                    .into_iter()
                    .map(|a| self.normalize_pattern_unit(a))
                    .collect(),
            },
            Binder(t, decl_id) => Binder(self.normalize_type(t), decl_id),
        }
    }

    fn _insert_type(
        &mut self,
        subtype: &mut SubtypeRelations<'a>,
        key: Type<'a>,
        value: Type<'a>,
    ) {
        if key == value {
            return;
        }
        use TypeMatchableRef::*;
        let (key, value) = match (key.matchable_ref(), value.matchable_ref()) {
            (Variable(key), Variable(value)) => {
                if value < key {
                    (value, TypeUnit::Variable(key).into())
                } else {
                    (key, TypeUnit::Variable(value).into())
                }
            }
            (Variable(key), _)
                if !value.all_type_variables().contains(&key) =>
            {
                (key, value)
            }
            (_, Variable(value))
                if !key.all_type_variables().contains(&value) =>
            {
                (value, key)
            }
            (Variable(_), _) | (_, Variable(_)) => {
                panic!("recursion is not allowed.",)
            }
            _ => {
                subtype.add_subtype_rel(key.clone(), value.clone());
                subtype.add_subtype_rel(value, key);
                return;
            }
        };
        if let Some(old) = self.0.get(&key) {
            log::error!("{key} is already pointing to {old}. ignored");
        } else {
            self.0.insert(key, value);
        }
    }

    pub fn insert_type(
        &mut self,
        subtype: &mut SubtypeRelations<'a>,
        k: Type<'a>,
        v: Type<'a>,
    ) {
        let key = self.normalize_type(k.clone());
        let value = self.normalize_type(v.clone());
        log::debug!(
            "{k} {} ----> {v} {}",
            if k == key {
                "".to_string()
            } else {
                format!("({})", key)
            },
            if v == value {
                "".to_string()
            } else {
                format!("({})", value)
            }
        );
        self._insert_type(subtype, key, value)
    }

    pub fn insert(
        &mut self,
        subtype: &mut SubtypeRelations<'a>,
        k: TypeVariable,
        v: Type<'a>,
    ) {
        let key = self.find(k);
        let value = self.normalize_type(v.clone());
        log::debug!(
            "{k} {} ----> {v} {}",
            match key.matchable_ref() {
                TypeMatchableRef::Variable(key) if k == key => "".to_string(),
                _ => format!("({})", key),
            },
            if v == value {
                "".to_string()
            } else {
                format!("({})", value)
            }
        );
        self._insert_type(subtype, key, value)
    }
}

impl<'a> SubtypeRelations<'a> {
    pub fn merge(mut self, other: Self) -> Self {
        self.add_subtype_rels(other.0);
        self
    }

    pub fn possible_strongest(
        &mut self,
        map: &mut TypeVariableMap<'a>,
        t: TypeVariable,
        pattern_restrictions: &PatternRestrictions<'a>,
        variable_requirements: &[VariableRequirement],
    ) -> Option<Type<'a>> {
        let t = map.find(t);
        if let TypeMatchableRef::Variable(v) = t.matchable_ref() {
            possible_strongest(
                v,
                &self.0,
                pattern_restrictions,
                variable_requirements,
            )
        } else {
            Some(t)
        }
    }

    pub fn possible_weakest(
        &mut self,
        map: &mut TypeVariableMap<'a>,
        t: TypeVariable,
        pattern_restrictions: &PatternRestrictions<'a>,
        variable_requirements: &[VariableRequirement],
    ) -> Option<Type<'a>> {
        let t = map.find(t);
        if let TypeMatchableRef::Variable(v) = t.matchable_ref() {
            possible_weakest(
                v,
                &self.0,
                variable_requirements,
                pattern_restrictions,
            )
        } else {
            Some(t)
        }
    }

    pub fn type_variables_in_sub_rel<T: FromIterator<TypeVariable>>(
        &self,
    ) -> T {
        self.iter()
            .flat_map(|(a, b)| {
                a.all_type_variables()
                    .into_iter()
                    .chain(b.all_type_variables())
            })
            .collect()
    }

    pub fn normalize(
        mut self,
        map: &mut TypeVariableMap<'a>,
        already_considered_relations: &mut SubtypeRelations<'a>,
    ) -> Option<Self> {
        self = self.normalize_subtype_rel(map, already_considered_relations)?;
        let eqs = find_eq_types(&self);
        let eqs_is_empty = eqs.is_empty();
        for (from, to) in eqs {
            map.insert(&mut self, from, to);
        }
        if eqs_is_empty {
            Some(self)
        } else {
            self.normalize(map, already_considered_relations)
        }
    }

    fn normalize_subtype_rel(
        mut self,
        map: &mut TypeVariableMap<'a>,
        already_considered_relations: &mut SubtypeRelations<'a>,
    ) -> Option<Self> {
        self = self
            .into_iter()
            .map(|(a, b)| {
                let a = map.normalize_type(a);
                let b = map.normalize_type(b);
                let r = simplify_subtype_rel(
                    a.clone(),
                    b.clone(),
                    already_considered_relations,
                );
                if r.is_none() {
                    log::debug!("a !<: b");
                    log::debug!("a = {a}");
                    log::debug!("b = {b}");
                }
                r
            })
            .collect::<Option<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect();
        Some(self)
    }

    pub fn add_subtype_rel(&mut self, sub: Type<'a>, sup: Type<'a>) {
        self.insert((sub, sup));
    }

    pub fn add_subtype_rels<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = (Type<'a>, Type<'a>)>,
    {
        self.extend(iter)
    }
}

pub fn simplify_type<'a, T: TypeConstructor<'a>>(
    map: &mut TypeVariableMap<'a>,
    mut t: IncompleteType<'a, T>,
) -> Option<IncompleteType<'a, T>> {
    let mut i = 0;
    loop {
        i += 1;
        let updated;
        let old_t = t.clone();
        (t, updated) = _simplify_type(map, t)?;
        if !updated {
            debug_assert_eq!(
                t.clone().normalize(map),
                _simplify_type(map, t.clone()).unwrap().0.normalize(map)
            );
            break;
        } else if i == 100 {
            log::error!("loop count is about to reach the limit.");
            log::debug!("old_t = {old_t}");
            log::debug!("t = {t}");
        } else if i > 100 {
            log::error!("loop count reached the limit.");
            log::debug!("old_t = {old_t}");
            log::debug!("t = {t}");
            assert_ne!(old_t, t);
            break;
        }
    }
    t.normalize(map)
}

fn _simplify_type<'a, T: TypeConstructor<'a>>(
    map: &mut TypeVariableMap<'a>,
    mut t: IncompleteType<'a, T>,
) -> Option<(IncompleteType<'a, T>, bool)> {
    let hash_before_simplify = fxhash::hash(&t);
    log::debug!("t = {}", t);
    // log::trace!("map = {}", map);
    t = t.normalize(map)?;
    log::trace!("t{{0.5}} = {}", t);
    for cov in mk_covariant_candidates(&t) {
        if !mk_contravariant_candidates(&t).contains(&cov) {
            if let Some(s) = t.subtype_relations.possible_strongest(
                map,
                cov,
                &t.pattern_restrictions,
                &t.variable_requirements,
            ) {
                if s.len() == 0 {
                    log::trace!("t{{0.5}} = {}", t);
                }
                map.insert(&mut t.subtype_relations, cov, s);
                t = t.normalize(map)?;
                return Some((t, true));
            }
        }
    }
    log::trace!("t{{1}} = {}", t);
    for cont in mk_contravariant_candidates(&t) {
        if !mk_covariant_candidates(&t).contains(&cont) {
            if let Some(s) = t.subtype_relations.possible_weakest(
                map,
                cont,
                &t.pattern_restrictions,
                &t.variable_requirements,
            ) {
                map.insert(&mut t.subtype_relations, cont, s);
                t = t.normalize(map)?;
                return Some((t, true));
            }
        }
    }
    log::trace!("t' = {}", t);
    let type_variables_in_sub_rel: FxHashSet<TypeVariable> =
        t.subtype_relations.type_variables_in_sub_rel();
    for a in &type_variables_in_sub_rel {
        let vs = t.type_variables_in_constructors_or_variable_requirements();
        let st = t.subtype_relations.possible_strongest(
            map,
            *a,
            &t.pattern_restrictions,
            &t.variable_requirements,
        );
        let we = t.subtype_relations.possible_weakest(
            map,
            *a,
            &t.pattern_restrictions,
            &t.variable_requirements,
        );
        match (st, we) {
            (Some(st), Some(we)) if st == we => {
                if st.len() == 0 {
                    log::debug!("t'{{1}} = {t}");
                }
                map.insert(&mut t.subtype_relations, *a, st);
                t = t.normalize(map)?;
                return Some((t, true));
            }
            (Some(st), _) if !vs.contains(a) => {
                if st.len() == 0 {
                    log::debug!("t'{{1}} = {t}");
                }
                map.insert(&mut t.subtype_relations, *a, st);
                t = t.normalize(map)?;
                return Some((t, true));
            }
            (_, Some(we)) if we.len() == 0 => {
                map.insert(
                    &mut t.subtype_relations,
                    *a,
                    TypeMatchable::Empty.into(),
                );
                t = t.normalize(map)?;
                return Some((t, true));
            }
            _ => (),
        }
    }
    log::trace!("t'' = {}", t);
    let covariant_candidates = mk_covariant_candidates(&t);
    let contravariant_candidates = mk_contravariant_candidates(&t);
    let type_variables_in_sub_rel: HashBag<TypeVariable> =
        t.subtype_relations.type_variables_in_sub_rel();
    for (v, count) in type_variables_in_sub_rel {
        if count == 1
            && !covariant_candidates.contains(&v)
            && !contravariant_candidates.contains(&v)
        {
            if let Some(new_t) = t.subtype_relations.possible_strongest(
                map,
                v,
                &t.pattern_restrictions,
                &t.variable_requirements,
            ) {
                map.insert(&mut t.subtype_relations, v, new_t);
                t = t.normalize(map)?;
                return Some((t, true));
            }
        }
    }
    for (i, (ts, patterns)) in t.pattern_restrictions.iter().enumerate() {
        if patterns.len() == 1
            && ts
                .clone()
                .arguments_from_argument_tuple()
                .iter()
                .zip(&patterns[0].clone().arguments_from_argument_tuple())
                .all(|(t, p)| {
                    if let PatternUnitForRestriction::Binder(p_t, _) = p {
                        t == p_t
                    } else {
                        false
                    }
                })
        {
            t.pattern_restrictions.remove(i);
            return Some((t, true));
        }
    }
    log::trace!("t{{4}} = {}", t);
    let mut updated = false;
    t.subtype_relations = t
        .subtype_relations
        .clone()
        .into_iter()
        .map(|(sub, sup)| {
            let sup = if sup.len() >= 2 {
                sup.clone()
                    .into_iter()
                    .filter(|s| {
                        if let TypeUnit::Variable(s) = &**s {
                            if let Some(s) =
                                t.subtype_relations.possible_weakest(
                                    map,
                                    *s,
                                    &t.pattern_restrictions,
                                    &t.variable_requirements,
                                )
                            {
                                let b = simplify_subtype_rel(
                                    sub.clone(),
                                    s,
                                    &mut t.already_considered_relations.clone(),
                                )
                                .is_some();
                                if !b {
                                    updated = true;
                                }
                                b
                            } else {
                                true
                            }
                        } else {
                            true
                        }
                    })
                    .collect()
            } else {
                sup
            };
            (sub.clone(), sup)
        })
        .collect();
    if updated {
        return Some((t, true));
    }
    log::trace!("t{{5}} = {}", t);
    for (pattern_ts, pattern) in &t.pattern_restrictions {
        let subtype = apply_type_to_pattern(pattern_ts.clone(), pattern)?;
        if !subtype.0.is_empty() {
            let mut t_normalized = t.clone();
            t_normalized.subtype_relations.extend(subtype);
            t_normalized = t_normalized.normalize(map)?;
            if t_normalized != t {
                return Some((t_normalized, true));
            }
        }
    }
    log::trace!("t{{6}} = {}", t);
    if t.variable_requirements.is_empty() {
        let c = t.constructor.clone();
        for v in t.constructor.all_type_variables() {
            if let (Some(we), Some(st)) = (
                t.subtype_relations.possible_weakest(
                    map,
                    v,
                    &t.pattern_restrictions,
                    &t.variable_requirements,
                ),
                t.subtype_relations.possible_strongest(
                    map,
                    v,
                    &t.pattern_restrictions,
                    &t.variable_requirements,
                ),
            ) {
                let replaced_with_we = c
                    .clone()
                    .replace_num(v, &we)
                    .map_type(|t| map.normalize_type(t));
                let replaced_with_st = c
                    .clone()
                    .replace_num(v, &st)
                    .map_type(|t| map.normalize_type(t));
                if replaced_with_we == replaced_with_st {
                    map.insert(&mut t.subtype_relations, v, st);
                    return Some((t, true));
                }
            }
        }
        log::trace!("t{{6}} = {}", t);
        let contravariant_candidates = mk_contravariant_candidates(&t);
        t.pattern_restrictions =
            t.pattern_restrictions
                .into_iter()
                .map(|(pattern_ts, pattern)| {
                    let pattern_ts: Vec<_> =
                        pattern_ts
                            .arguments_from_argument_tuple()
                            .iter()
                            .map(|pattern_t| {
                                if pattern_t.all_type_variables().iter().all(
                                    |v| !contravariant_candidates.contains(v),
                                ) {
                                    possible_strongest_t(
                                        pattern_t.clone(),
                                        &t.subtype_relations,
                                    )
                                } else {
                                    pattern_t.clone()
                                }
                            })
                            .collect();
                    (Type::argument_tuple_from_arguments(pattern_ts), pattern)
                })
                .collect();
        for (pattern_ts, pattern) in &t.pattern_restrictions {
            let subtype = apply_type_to_pattern(pattern_ts.clone(), pattern)?;
            if !subtype.0.is_empty() {
                let mut t_normalized = t.clone();
                t_normalized.subtype_relations.extend(subtype);
                t_normalized = t_normalized.normalize(map)?;
                if t_normalized != t {
                    return Some((t_normalized, true));
                }
            }
        }
        log::trace!("t{{9}} = {}", t);
        let old_pattern_restrictions = t.pattern_restrictions;
        t.pattern_restrictions = Vec::new();
        let pattern_restrictions = old_pattern_restrictions
            .clone()
            .into_iter()
            .map(|(pattern_t, pattern)| {
                let pattern = pattern
                    .into_iter()
                    .map(|p| {
                        p.map_type(|mut t_in_p| {
                            for v in t_in_p.all_type_variables() {
                                if let (Some(we), Some(st)) = (
                                    t.subtype_relations.possible_weakest(
                                        map,
                                        v,
                                        &t.pattern_restrictions,
                                        &t.variable_requirements,
                                    ),
                                    t.subtype_relations.possible_strongest(
                                        map,
                                        v,
                                        &t.pattern_restrictions,
                                        &t.variable_requirements,
                                    ),
                                ) {
                                    let replaced_with_we = c
                                        .clone()
                                        .replace_num(v, &we)
                                        .map_type(|t| map.normalize_type(t));
                                    let replaced_with_st = c
                                        .clone()
                                        .replace_num(v, &st)
                                        .map_type(|t| map.normalize_type(t));
                                    if replaced_with_we == replaced_with_st {
                                        t_in_p = t_in_p.replace_num(v, &st);
                                    }
                                }
                            }
                            t_in_p
                        })
                    })
                    .collect();
                (pattern_t, pattern)
            })
            .collect();
        if old_pattern_restrictions != pattern_restrictions {
            t.pattern_restrictions = pattern_restrictions;
            return Some((t, true));
        }
        // log::trace!("t{{7}} = {}", t);
        // let mut bounded_v = None;
        // for (a, b) in &t.subtype_relations {
        //     if let TypeMatchableRef::Variable(v) = b.matchable_ref() {
        //         bounded_v = Some((a.clone(), b.clone(), v));
        //         break;
        //     }
        // }
        // if let Some((a, b, v)) = bounded_v {
        //     log::trace!("t{{8}} = {}", t);
        //     log::trace!("map = {map}");
        //     t.subtype_relations.remove(&(a.clone(), b));
        //     let a = a
        //         .into_iter()
        //         .chain(std::iter::once(TypeUnit::new_variable()))
        //         .collect();
        //     map.insert(&mut t.subtype_relations, v, a);
        //     return Some((t, true));
        // }
    }
    t = t.conjunctive();
    let updated = fxhash::hash(&t) != hash_before_simplify;
    Some((t, updated))
}

fn find_eq_types<'a>(
    subtype_rel: &SubtypeRelations<'a>,
) -> Vec<(TypeVariable, Type<'a>)> {
    use TypeUnit::*;
    let g = mk_graph(subtype_rel);
    let eq_types = tarjan_scc(&g);
    let mut r = Vec::new();
    for eqs in eq_types {
        let (eq_variable, eq_cons): (Vec<_>, Vec<_>) = eqs
            .into_iter()
            .map(|ts| {
                if let TypeMatchableRef::Variable(n) = ts.matchable_ref() {
                    Ok(n)
                } else {
                    Err(ts)
                }
            })
            .partition_result();
        if eq_cons.is_empty() {
            for a in &eq_variable[1..] {
                r.push((*a, Variable(eq_variable[0]).into()));
            }
        } else {
            for a in eq_variable {
                r.push((a, eq_cons[0].clone()));
            }
        }
    }
    r
}

pub fn simplify_subtype_rel<'a>(
    sub: Type<'a>,
    sup: Type<'a>,
    already_considered_relations: &mut SubtypeRelations<'a>,
) -> Option<Vec<(Type<'a>, Type<'a>)>> {
    if sub == sup
        || already_considered_relations.contains(&(sub.clone(), sup.clone()))
    {
        return Some(Vec::new());
    }
    use TypeMatchable::*;
    match (sub.matchable(), sup.matchable()) {
        (Fn(a1, r1), Fn(a2, r2)) => Some(
            [
                simplify_subtype_rel(r1, r2, already_considered_relations)?,
                simplify_subtype_rel(a2, a1, already_considered_relations)?,
            ]
            .concat(),
        ),
        (
            Normal {
                id: n1, args: cs1, ..
            },
            Normal {
                id: n2, args: cs2, ..
            },
        ) => {
            if n1 == n2 {
                assert_eq!(cs1.len(), cs2.len());
                Some(
                    cs1.into_iter()
                        .zip(cs2)
                        .map(|(a, b)| {
                            simplify_subtype_rel(
                                a,
                                b,
                                already_considered_relations,
                            )
                        })
                        .collect::<Option<Vec<_>>>()?
                        .concat(),
                )
            } else {
                None
            }
        }
        (Fn(_, _), Normal { .. })
        | (Normal { .. }, Fn(_, _))
        | (Fn(_, _), Empty)
        | (Normal { .. }, Empty) => None,
        (Union(cs), b) => Some(
            cs.into_iter()
                .map(|c| {
                    simplify_subtype_rel(
                        c.into(),
                        b.clone().into(),
                        already_considered_relations,
                    )
                })
                .collect::<Option<Vec<_>>>()?
                .concat(),
        ),
        (Empty, _) => Some(Vec::new()),
        (a, Union(u))
            if u.iter().any(|b| {
                simplify_subtype_rel(
                    a.clone().into(),
                    b.clone().into(),
                    &mut already_considered_relations.clone(),
                )
                .map(|s| s.is_empty())
                .unwrap_or(false)
            }) =>
        {
            Some(Vec::new())
        }
        (a, RecursiveAlias { body }) if body.contains(&a.clone().into()) => {
            Some(Vec::new())
        }
        (a @ (Normal { .. } | Fn(_, _)), RecursiveAlias { body }) => {
            simplify_subtype_rel(
                a.into(),
                unwrap_recursive_alias(body),
                already_considered_relations,
            )
        }
        (
            RecursiveAlias { body },
            b @ (Normal { .. } | Fn(_, _) | Union(_) | RecursiveAlias { .. }),
        ) => {
            let b: Type = b.into();
            if b.find_recursive_alias().is_some() {
                already_considered_relations.insert((
                    RecursiveAlias { body: body.clone() }.into(),
                    b.clone(),
                ));
            }
            simplify_subtype_rel(
                unwrap_recursive_alias(body),
                b,
                already_considered_relations,
            )
        }
        (Normal { id, name, args }, Union(tus)) => {
            let t: Type = Normal { id, name, args }.into();
            let td = t.clone().disjunctive();
            if t != td {
                simplify_subtype_rel(
                    td,
                    tus.into_iter().collect(),
                    already_considered_relations,
                )
            } else {
                let new_tus = tus
                    .clone()
                    .into_iter()
                    .filter(|tu| {
                        (if let TypeUnit::Normal { id: id2, .. } = &**tu {
                            id == *id2
                        } else {
                            true
                        }) && (simplify_subtype_rel(
                            t.clone(),
                            tu.clone().into(),
                            already_considered_relations,
                        )
                        .is_some())
                    })
                    .collect();
                if tus != new_tus {
                    simplify_subtype_rel(
                        td,
                        new_tus,
                        already_considered_relations,
                    )
                } else {
                    Some(vec![(t, tus)])
                }
            }
        }
        (Variable(a), b)
            if Type::from(b.clone()).contains_variable(a)
                && !a.is_recursive_index() =>
        {
            let b = Type::from(b).replace_num(
                a,
                &TypeUnit::Variable(TypeVariable::recursive_index_zero())
                    .into(),
            );
            simplify_subtype_rel(
                TypeUnit::Variable(a).into(),
                TypeUnit::RecursiveAlias { body: b }.into(),
                already_considered_relations,
            )
        }
        (sub, sup) => {
            let sup: Type = sup.into();
            let c_sup = sup.clone().conjunctive();
            if sup == c_sup {
                Some(vec![(sub.into(), sup)])
            } else {
                simplify_subtype_rel(
                    sub.into(),
                    c_sup,
                    already_considered_relations,
                )
            }
        }
    }
}

fn unwrap_recursive_alias(body: Type) -> Type {
    body.clone().replace_num(
        TypeVariable::RecursiveIndex(0),
        &(TypeUnit::RecursiveAlias { body }).into(),
    )
}

fn possible_weakest<'a>(
    t: TypeVariable,
    subtype_relation: &BTreeSet<(Type<'a>, Type<'a>)>,
    variable_requirements: &[VariableRequirement],
    pattern_restrictions: &PatternRestrictions<'a>,
) -> Option<Type<'a>> {
    if variable_requirements
        .iter()
        .any(|req| req.required_type.contains_variable(t))
    {
        return None;
    }
    let mut up = FxHashSet::default();
    for (sub, sup) in subtype_relation
        .iter()
        .map(|(a, b)| (a.clone(), b.clone()))
        .chain(pattern_restrictions.iter().flat_map(|(match_t, pattern)| {
            match_t
                .clone()
                .arguments_from_argument_tuple()
                .into_iter()
                .zip(type_from_pattern_for_restriction(pattern))
        }))
    {
        if sup.contravariant_type_variables().contains(&t) {
            return None;
        } else if sub == TypeUnit::Variable(t).into() {
            up.insert(sup);
        } else if sub.covariant_type_variables().contains(&t) {
            return None;
        }
    }
    if up.len() == 1 {
        let up = up.into_iter().next().unwrap().clone();
        Some(if up.contains_variable(t) {
            TypeUnit::RecursiveAlias {
                body: up.replace_num(
                    t,
                    &TypeUnit::Variable(TypeVariable::RecursiveIndex(0)).into(),
                ),
            }
            .into()
        } else {
            up
        })
    } else if up.is_empty() {
        None
    } else {
        let mut up = up.into_iter();
        let mut t = up.next().unwrap().clone();
        for up in up {
            t = type_intersection(t, up.clone())?;
        }
        Some(t)
    }
}

fn type_from_pattern_for_restriction<'a>(
    pattern: &PatternForRestriction<'a>,
) -> Vec<Type<'a>> {
    let r = pattern
        .iter()
        .map(|p| p.arguments_from_argument_tuple_ref())
        .collect_vec();
    transpose(r)
        .into_iter()
        .map(|a| a.into_iter().flat_map(Type::from).collect())
        .collect()
}

fn transpose<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>> {
    let len = v[0].len();
    let mut iters: Vec<_> = v.into_iter().map(|n| n.into_iter()).collect();
    (0..len)
        .map(|_| {
            iters
                .iter_mut()
                .map(|n| n.next().unwrap())
                .collect::<Vec<T>>()
        })
        .collect()
}

impl<'a> From<&PatternUnitForRestriction<'a>> for Type<'a> {
    fn from(p: &PatternUnitForRestriction<'a>) -> Self {
        match p {
            PatternUnitForRestriction::I64 => Type::from_str("I64"),
            PatternUnitForRestriction::Str => Type::from_str("Str"),
            PatternUnitForRestriction::Constructor { id, name, args } => {
                TypeUnit::Normal {
                    name,
                    args: args.iter().map(Type::from).collect(),
                    id: *id,
                }
                .into()
            }
            PatternUnitForRestriction::Binder(t, _decl_id) => t.clone(),
        }
    }
}

fn type_intersection<'a>(a: Type<'a>, b: Type<'a>) -> Option<Type<'a>> {
    use TypeMatchable::*;
    match (a.matchable(), b.matchable()) {
        (Normal { .. }, Fn(_, _)) | (Fn(_, _), Normal { .. }) => {
            Some(TypeMatchable::Empty.into())
        }
        (
            Normal {
                name: n1,
                args: args1,
                id: id1,
            },
            Normal {
                name: _,
                args: args2,
                id: id2,
            },
        ) => {
            if id1 == id2 {
                Some(
                    TypeUnit::Normal {
                        name: n1,
                        args: args1
                            .into_iter()
                            .zip_eq(args2)
                            .map(|(a1, a2)| type_intersection(a1, a2))
                            .collect::<Option<_>>()?,
                        id: id1,
                    }
                    .into(),
                )
            } else {
                Some(TypeMatchable::Empty.into())
            }
        }
        (Fn(a1, r1), Fn(a2, r2)) => Some(
            TypeUnit::Fn(
                a1.into_iter().chain(a2.into_iter()).collect(),
                type_intersection(r1, r2)?,
            )
            .into(),
        ),
        (a, b) => {
            let a: Type = a.into();
            let b: Type = b.into();
            let ab = simplify_subtype_rel(
                a.clone(),
                b.clone(),
                &mut Default::default(),
            );
            if let Some(ab) = ab {
                if ab.is_empty() {
                    return Some(a);
                }
            }
            let ba =
                simplify_subtype_rel(b.clone(), a, &mut Default::default());
            if let Some(ba) = ba {
                if ba.is_empty() {
                    return Some(b);
                }
            }
            None
        }
    }
}

fn possible_strongest<'a>(
    t: TypeVariable,
    subtype_relation: &BTreeSet<(Type<'a>, Type<'a>)>,
    pattern_restrictions: &PatternRestrictions<'a>,
    variable_requirements: &[VariableRequirement],
) -> Option<Type<'a>> {
    let mut down = Vec::new();
    if variable_requirements
        .iter()
        .any(|req| req.required_type.contains_variable(t))
    {
        return None;
    }
    for (sub, sup) in subtype_relation {
        if sub.contravariant_type_variables().contains(&t) {
            return None;
        } else if *sup == TypeUnit::Variable(t).into() {
            down.push(sub);
        } else if sup.covariant_type_variables().contains(&t) {
            return None;
        }
    }
    for (_, pattern) in pattern_restrictions {
        if pattern
            .iter()
            .any(|p| p.covariant_type_variables().contains(&t))
        {
            return None;
        }
    }
    let result = if down.len() == 1 {
        down[0].clone()
    } else if down.is_empty() {
        TypeMatchable::Empty.into()
    } else {
        down.iter().copied().cloned().flatten().collect()
    };
    if down.iter().any(|d| d.contains_variable(t)) {
        Some(
            TypeUnit::RecursiveAlias {
                body: result.replace_num(
                    t,
                    &TypeUnit::Variable(TypeVariable::RecursiveIndex(0)).into(),
                ),
            }
            .into(),
        )
    } else {
        Some(result)
    }
}

fn possible_strongest_t<'a>(
    t: Type<'a>,
    subtype_relation: &SubtypeRelations<'a>,
) -> Type<'a> {
    let t = t.disjunctive();
    let mut down_up: Type = TypeMatchable::Empty.into();
    let mut down_down: Type = TypeMatchable::Empty.into();
    for (a, b) in subtype_relation {
        if a.all_type_variables().is_empty() {
            let b = b.clone().disjunctive();
            if t.contains(&b) {
                down_up = down_up.union(b);
                down_down = down_down.union(a.clone());
            }
        }
    }
    if down_up.len() > 0 {
        t.into_iter()
            .filter(|t| !down_up.contains_unit(t))
            .chain(down_down)
            .collect()
    } else {
        t
    }
}

fn mk_contravariant_candidates<'a, T: TypeConstructor<'a>>(
    t: &IncompleteType<'a, T>,
) -> FxHashSet<TypeVariable> {
    let mut rst: Vec<TypeVariable> =
        t.constructor.contravariant_type_variables();
    for req in &t.variable_requirements {
        rst.append(&mut req.required_type.covariant_type_variables());
    }
    rst.into_iter().collect()
}

fn mk_covariant_candidates<'a, T: TypeConstructor<'a>>(
    t: &IncompleteType<'a, T>,
) -> FxHashSet<TypeVariable> {
    let mut rst: Vec<TypeVariable> = t.constructor.covariant_type_variables();
    for req in &t.variable_requirements {
        rst.append(&mut req.required_type.contravariant_type_variables());
    }
    rst.into_iter().collect()
}

impl<'a, T> IncompleteType<'a, T>
where
    T: TypeConstructor<'a>,
{
    pub fn normalize(mut self, map: &mut TypeVariableMap<'a>) -> Option<Self> {
        self.subtype_relations = self
            .subtype_relations
            .normalize(map, &mut self.already_considered_relations)?;
        Some(Self {
            constructor: self
                .constructor
                .map_type(|t| map.normalize_type(t))
                .normalize_contravariant_candidates_from_annotation(
                map,
            )?,
            variable_requirements: self
                .variable_requirements
                .into_iter()
                .map(|mut req| {
                    req.required_type = map.normalize_type(req.required_type);
                    req
                })
                .collect(),
            subtype_relations: self
                .subtype_relations
                .into_iter()
                .map(|(a, b)| (map.normalize_type(a), map.normalize_type(b)))
                .collect(),
            pattern_restrictions: self
                .pattern_restrictions
                .into_iter()
                .map(|(t, p)| {
                    (
                        map.normalize_type(t),
                        p.into_iter()
                            .map(|p| map.normalize_pattern_unit(p))
                            .collect(),
                    )
                })
                .collect(),
            already_considered_relations: self.already_considered_relations,
        })
    }
}

fn apply_type_to_pattern<'a>(
    t: Type<'a>,
    pattern: &Vec<PatternUnitForRestriction<'a>>,
) -> Option<SubtypeRelations<'a>> {
    log::trace!("ts = ({})", t.iter().map(|t| format!("{t}")).join(", "));
    log::trace!(
        "pattern = {}",
        pattern.iter().map(|p| format!("{}", p)).join(" | ")
    );
    let mut ts = t.clone().disjunctive();
    let decl_type_map_in_pattern: FxHashMap<DeclId, Type> = pattern
        .iter()
        .flat_map(|p| p.decl_type_map())
        .map(|(d, t)| (d, t.clone()))
        .collect();
    let mut subtype_rels = SubtypeRelations::default();
    let mut not_sure = false;
    for p in pattern {
        let TypeDestructResult {
            remained,
            matched,
            bind_matched,
            kind,
        } = destruct_type_by_pattern(ts.clone(), p);
        let subtype_r: SubtypeRelations = bind_matched
            .iter()
            .flat_map(|v| {
                v.iter().map(|(decl_id, t)| {
                    (t.clone(), decl_type_map_in_pattern[decl_id].clone())
                })
            })
            .collect();
        match kind {
            DestructResultKind::NotSure => {
                subtype_rels.add_subtype_rels(subtype_r);
                let matched_t = matched.unwrap().disjunctive();
                ts = remained
                    .into_iter()
                    .filter(|t| !matched_t.contains_unit(t))
                    .collect();
                not_sure = true;
            }
            DestructResultKind::Fail => (),
            DestructResultKind::Ok => {
                subtype_rels.add_subtype_rels(subtype_r);
                let mut decl_match_map: FxHashMap<DeclId, Type> =
                    Default::default();
                for (decl_id, t) in bind_matched.unwrap() {
                    decl_match_map
                        .entry(decl_id)
                        .or_default()
                        .union_in_place(t);
                }
                for (decl_id, t) in decl_match_map {
                    subtype_rels.add_subtype_rel(
                        decl_type_map_in_pattern[&decl_id].clone(),
                        t,
                    )
                }
                let matched_t = matched.unwrap().disjunctive();
                ts = remained
                    .into_iter()
                    .filter(|t| !matched_t.contains_unit(t))
                    .collect();
            }
        }
    }
    if ts.len() != 0 && !not_sure {
        log::debug!("missing type = {ts}");
        None
    } else {
        if not_sure {
            let pattern_t = pattern_to_type(pattern);
            subtype_rels.add_subtype_rels(simplify_subtype_rel(
                t,
                pattern_t.conjunctive(),
                &mut Default::default(),
            )?);
        }
        Some(subtype_rels)
    }
}

fn pattern_unit_to_type<'a>(p: &PatternUnitForRestriction<'a>) -> Type<'a> {
    use PatternUnitForRestriction::*;
    match p {
        I64 => Type::from_str("I64"),
        Str => Type::from_str("String"),
        Constructor { id, args, name } => TypeUnit::Normal {
            name,
            args: args.iter().map(|t| pattern_to_type(&[t.clone()])).collect(),
            id: *id,
        }
        .into(),
        Binder(t, _) => t.clone(),
    }
}

fn pattern_to_type<'a>(p: &[PatternUnitForRestriction<'a>]) -> Type<'a> {
    let mut t = Type::default();
    for p in p {
        t = t.union(pattern_unit_to_type(p));
    }
    t
}

#[derive(Debug)]
enum DestructResultKind {
    Ok,
    NotSure,
    Fail,
}

struct TypeDestructResult<'a> {
    remained: Type<'a>,
    matched: Option<Type<'a>>,
    bind_matched: Option<Vec<(DeclId, Type<'a>)>>,
    kind: DestructResultKind,
}

fn destruct_type_by_pattern<'a>(
    t: Type<'a>,
    pattern: &PatternUnitForRestriction<'a>,
) -> TypeDestructResult<'a> {
    let mut remained: Type = TypeMatchable::Empty.into();
    let mut destructed = false;
    let mut not_sure = false;
    let mut matched: Type = TypeMatchable::Empty.into();
    let mut bind_matched = Vec::new();
    for tu in t {
        let TypeDestructResult {
            remained: r,
            matched: m,
            bind_matched: bm,
            kind,
        } = destruct_type_unit_by_pattern(unwrap_or_clone(tu), pattern);
        match kind {
            DestructResultKind::NotSure => {
                matched = matched.union(m.unwrap());
                not_sure = true;
            }
            DestructResultKind::Fail => (),
            DestructResultKind::Ok => {
                let mut dm = bm.unwrap();
                matched = matched.union(m.unwrap());
                destructed = true;
                bind_matched.append(&mut dm);
            }
        }
        remained = remained.union(r);
    }
    if not_sure {
        TypeDestructResult {
            remained,
            matched: Some(matched),
            bind_matched: Some(bind_matched),
            kind: DestructResultKind::NotSure,
        }
    } else if destructed {
        TypeDestructResult {
            remained,
            matched: Some(matched),
            bind_matched: Some(bind_matched),
            kind: DestructResultKind::Ok,
        }
    } else {
        TypeDestructResult {
            remained,
            matched: None,
            bind_matched: None,
            kind: DestructResultKind::Fail,
        }
    }
}

fn destruct_type_unit_by_pattern<'a>(
    t: TypeUnit<'a>,
    pattern: &PatternUnitForRestriction<'a>,
) -> TypeDestructResult<'a> {
    match (t, pattern) {
        (
            t,
            PatternUnitForRestriction::I64 | PatternUnitForRestriction::Str,
        ) => TypeDestructResult {
            remained: t.into(),
            matched: Some(TypeMatchable::Empty.into()),
            bind_matched: Some(Vec::new()),
            kind: DestructResultKind::Ok,
        },
        (
            TypeUnit::Normal {
                args: t_args,
                id: t_id,
                name,
            },
            PatternUnitForRestriction::Constructor {
                id: p_id,
                args: p_args,
                ..
            },
        ) if *p_id == t_id => {
            if t_args.is_empty() {
                TypeDestructResult {
                    remained: TypeUnit::Normal {
                        args: t_args.clone(),
                        id: t_id,
                        name,
                    }
                    .into(),
                    matched: Some(
                        TypeUnit::Normal {
                            args: t_args,
                            id: t_id,
                            name,
                        }
                        .into(),
                    ),
                    bind_matched: Some(Vec::new()),
                    kind: DestructResultKind::Ok,
                }
            } else {
                let mut destructed = Some(Vec::new());
                let mut args = Vec::new();
                let mut decl_match = Some(Vec::new());
                let mut not_sure = false;
                for (t, p) in t_args.clone().into_iter().zip_eq(p_args) {
                    let TypeDestructResult {
                        remained,
                        matched,
                        bind_matched,
                        kind,
                    } = destruct_type_by_pattern(t, p);
                    let d = match kind {
                        DestructResultKind::NotSure => {
                            not_sure = true;
                            matched.unwrap()
                        }
                        DestructResultKind::Fail => {
                            return TypeDestructResult {
                                remained: TypeUnit::Normal {
                                    args: t_args,
                                    id: t_id,
                                    name,
                                }
                                .into(),
                                matched: None,
                                bind_matched: Some(Vec::new()),
                                kind: DestructResultKind::Fail,
                            };
                        }
                        DestructResultKind::Ok => matched.unwrap(),
                    };
                    destructed = destructed.map(|mut destructed| {
                        destructed.push(d);
                        destructed
                    });
                    decl_match = decl_match.and_then(|mut d| {
                        bind_matched.map(|mut d2| {
                            d.append(&mut d2);
                            d
                        })
                    });
                    args.push(
                        remained.into_iter().map(Type::from).collect_vec(),
                    );
                }
                TypeDestructResult {
                    remained: args
                        .into_iter()
                        .multi_cartesian_product()
                        .map(|args| TypeUnit::Normal {
                            name,
                            args,
                            id: t_id,
                        })
                        .collect(),
                    matched: destructed.map(|t| {
                        TypeUnit::Normal {
                            name,
                            args: t,
                            id: t_id,
                        }
                        .into()
                    }),
                    bind_matched: decl_match,
                    kind: if not_sure {
                        DestructResultKind::NotSure
                    } else {
                        DestructResultKind::Ok
                    },
                }
            }
        }
        (t, PatternUnitForRestriction::Binder(_, decl_id)) => {
            let t = Type::from(t);
            TypeDestructResult {
                remained: t.clone(),
                matched: Some(t.clone()),
                bind_matched: Some(vec![(*decl_id, t)]),
                kind: DestructResultKind::Ok,
            }
        }
        (TypeUnit::Variable(v), _) => TypeDestructResult {
            remained: TypeUnit::Variable(v).into(),
            matched: Some(TypeUnit::Variable(v).into()),
            bind_matched: None,
            kind: DestructResultKind::NotSure,
        },
        (TypeUnit::RecursiveAlias { body }, p) => {
            destruct_type_by_pattern(unwrap_recursive_alias(body), p)
        }
        (t, _) => TypeDestructResult {
            remained: t.into(),
            matched: None,
            bind_matched: None,
            kind: DestructResultKind::Fail,
        },
    }
}

fn mk_graph<'a, 'b>(
    subtype_relations: &'b SubtypeRelations<'a>,
) -> DiGraphMap<&'b Type<'a>, ()> {
    let mut g = DiGraphMap::new();
    for (a, b) in subtype_relations {
        g.add_edge(a, b, ());
    }
    g
}

#[test]
fn replace_type_test0() {
    use TypeUnit::*;
    let zero = TypeVariable::new();
    let one = TypeVariable::new();
    assert_eq!(
        Variable(zero).replace_num(zero, &Variable(one).into()),
        Variable(one).into()
    );
}

#[test]
fn replace_type_test1() {
    use TypeUnit::*;
    let zero = TypeVariable::new();
    let one = TypeVariable::new();
    let two = TypeVariable::new();
    assert_eq!(
        Fn(Variable(zero).into(), Variable(two).into())
            .replace_num(zero, &Variable(one).into()),
        Fn(Variable(one).into(), Variable(two).into()).into()
    );
}

impl<'a, T: TypeConstructor<'a>> IncompleteType<'a, T> {
    fn type_variables_in_constructors_or_variable_requirements(
        &self,
    ) -> FxHashSet<TypeVariable> {
        let mut s = self.constructor.all_type_variables();
        for req in &self.variable_requirements {
            s.extend(req.required_type.all_type_variables())
        }
        s
    }
}

impl Display for VariableRequirement<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "  {:<3}  ?{} : {} , env = ",
            self.ident, self.name, self.required_type
        )?;
        for (name, _, _) in &self.local_env {
            write!(f, "{}, ", name)?;
        }
        Ok(())
    }
}

impl<'a, T: TypeConstructor<'a>> Display for ast_step2::IncompleteType<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{} forall", self.constructor)?;
        for (a, b) in &self.subtype_relations {
            writeln!(f, "    {} < {},", a, b)?;
        }
        for req in &self.variable_requirements {
            writeln!(f, "{},", req)?;
        }
        for (a, b) in &self.pattern_restrictions {
            writeln!(
                f,
                "    ({}) = pat[{}],",
                a.iter().map(|a| format!("{a}")).join(", "),
                b.iter().map(|p| format!("({})", p)).join(" | ")
            )?;
        }
        if !self.already_considered_relations.is_empty() {
            writeln!(f, "already_considered_relations:")?;
            write!(f, "{}", self.already_considered_relations)?;
        }
        write!(f, "--")?;
        Ok(())
    }
}

impl<'a> Display for SubtypeRelations<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (a, b) in self {
            writeln!(f, "    {} < {},", a, b)?;
        }
        Ok(())
    }
}

impl<'a> Display for TypeVariableMap<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (a, b) in &self.0 {
            write!(f, "{a} : {b}, ")?;
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use super::destruct_type_by_pattern;
    use crate::{
        ast_step1, ast_step2,
        ast_step2::{
            decl_id::DeclId,
            types::{Type, TypeMatchable, TypeUnit, TypeVariable},
            IncompleteType, PatternUnitForRestriction, TypeId,
        },
        ast_step3::type_check::simplify::{
            apply_type_to_pattern, simplify_subtype_rel, simplify_type,
            TypeDestructResult, TypeVariableMap,
        },
        intrinsics::IntrinsicType,
    };
    use stripmargin::StripMargin;

    #[test]
    fn simplify1() {
        let src = r#"data a /\ b
        infixl 3 /\
        main : () -> ()
        = | () => ()
        test : I64 /\ I64 ->
        ((I64 /\ I64 | I64 /\ t1 | t2 /\ I64 | t3 /\ t4) -> I64 | String)
        -> I64 | String forall {t1, t2, t3, t4}
        = ()
        dot : a -> (a -> b) -> b forall {a, b} = ()
        "#;
        let ast = parse::parse(src);
        let ast: ast_step1::Ast = (&ast).into();
        let ast: ast_step2::Ast = ast.into();
        let req_t = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "test")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        let dot = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "dot")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        let t = IncompleteType {
            constructor: Type::from_str("I64")
                .arrow(Type::from_str("I64").union(Type::from_str("String"))),
            subtype_relations: vec![(dot, req_t)].into_iter().collect(),
            ..Default::default()
        };
        let mut map: TypeVariableMap = Default::default();
        let st = simplify_type(&mut map, t).unwrap();
        assert_eq!(format!("{}", st), "I64 -> {I64 | String} forall\n--");
    }

    #[test]
    fn simplify3() {
        let src = r#"data a /\ b
        infixl 3 /\
        main : () -> () =
            | () => ()
        test1 : (False /\ False /\ False) = ()
        test2 : (True /\ a /\ b) |
            (c /\ True /\ d) |
            (e /\ f /\ True) forall {a,b,c,d,e,f} = ()
        "#;
        let ast = parse::parse(src);
        let ast: ast_step1::Ast = (&ast).into();
        let ast: ast_step2::Ast = ast.into();
        let t1 = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "test1")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        let t2 = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "test2")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        let t = simplify_subtype_rel(
            t1.clone(),
            t2.clone(),
            &mut Default::default(),
        );
        assert_eq!(format!("{:?}", t), "None");
    }

    #[test]
    fn destruct_type_0() {
        let src = r#"data a /\ b
        infixl 3 /\
        main : () -> () =
            | () => ()
        test1 : ((True | False) /\ (True | False)) = ()
        "#;
        let ast = parse::parse(src);
        let ast: ast_step1::Ast = (&ast).into();
        let ast: ast_step2::Ast = ast.into();
        let t1 = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "test1")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        if let TypeUnit::Normal { name, id, .. } = &**t1.iter().next().unwrap()
        {
            let p = PatternUnitForRestriction::Constructor {
                id: *id,
                name,
                args: vec![
                    PatternUnitForRestriction::Constructor {
                        id: TypeId::Intrinsic(IntrinsicType::False),
                        name: "False",
                        args: Vec::new(),
                    },
                    PatternUnitForRestriction::Constructor {
                        id: TypeId::Intrinsic(IntrinsicType::False),
                        name: "False",
                        args: Vec::new(),
                    },
                ],
            };
            let TypeDestructResult {
                remained,
                matched,
                bind_matched: _,
                kind: _,
            } = destruct_type_by_pattern(t1, &p);
            assert_eq!(
                format!("{remained}"),
                r#"{/\(False, False) | /\(False, True) | /\(True, False) | /\(True, True)}"#
            );
            assert_eq!(format!("{}", matched.unwrap()), r#"/\(False, False)"#)
        } else {
            panic!()
        }
    }

    #[test]
    fn destruct_type_1() {
        let src = r#"data a /\ b
        infixl 3 /\
        main : () -> () =
            | () => ()
        data E
        data T(c, n, t, t)
        type Tree = E | T[A, Tree[A], Tree[A]] forall { A }
        test1 : Tree[()] = ()
        "#;
        let ast = parse::parse(src);
        let ast: ast_step1::Ast = (&ast).into();
        let ast: ast_step2::Ast = ast.into();
        let t_id = ast
            .data_decl
            .iter()
            .find(|d| d.name == "T")
            .unwrap()
            .decl_id;
        let t_id = TypeId::DeclId(t_id);
        let t1 = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "test1")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        let p = PatternUnitForRestriction::Constructor {
            id: t_id,
            name: "",
            args: vec![
                PatternUnitForRestriction::Binder(
                    TypeMatchable::Empty.into(),
                    DeclId::new(),
                ),
                PatternUnitForRestriction::Constructor {
                    id: t_id,
                    name: "",
                    args: vec![
                        PatternUnitForRestriction::Binder(
                            TypeMatchable::Empty.into(),
                            DeclId::new(),
                        ),
                        PatternUnitForRestriction::Binder(
                            TypeMatchable::Empty.into(),
                            DeclId::new(),
                        ),
                        PatternUnitForRestriction::Binder(
                            TypeMatchable::Empty.into(),
                            DeclId::new(),
                        ),
                    ],
                },
                PatternUnitForRestriction::Binder(
                    TypeMatchable::Empty.into(),
                    DeclId::new(),
                ),
            ],
        };
        let TypeDestructResult {
            remained,
            matched,
            bind_matched: _,
            kind: _,
        } = destruct_type_by_pattern(t1, &p);
        assert_eq!(
            format!("{remained}"),
            r#"{E | T((), E, rec[{E | T((), d0, d0)}]) 
              || T((), T((), rec[{E | T((), d0, d0)}], 
              |rec[{E | T((), d0, d0)}]), 
              |rec[{E | T((), d0, d0)}])}"#
                .strip_margin()
                .replace('\n', "")
        );
        assert_eq!(
            format!("{}", matched.unwrap()),
            r#"T((), T((), rec[{E | T((), d0, d0)}], 
              |rec[{E | T((), d0, d0)}]), 
              |rec[{E | T((), d0, d0)}])"#
                .strip_margin()
                .replace('\n', "")
        )
    }

    #[test]
    fn apply_type_to_pattern_0() {
        let v1 = TypeUnit::new_variable();
        let t1 = Type::from_str("I64").union(v1.clone().into());
        let v2 = TypeVariable::new();
        let r = apply_type_to_pattern(
            Type::argument_tuple_from_arguments(vec![t1]),
            &PatternUnitForRestriction::argument_tuple_from_arguments(vec![
                vec![PatternUnitForRestriction::I64],
                vec![PatternUnitForRestriction::Binder(
                    TypeUnit::Variable(v2).into(),
                    DeclId::new(),
                )],
            ]),
        );
        let subtype_rels = r.unwrap();
        assert_eq!(
            format!("{}", subtype_rels),
            format!(
                r#"    I64 < {0},
                  |    {1} < {0},
                  |    t1 < {{I64 | {1}}},
                  |"#,
                v2, v1,
            )
            .strip_margin()
        )
    }

    #[test]
    fn apply_type_to_pattern_1() {
        let src = r#"data a /\ b
        infixl 3 /\
        main : () -> () =
            | () => ()
        data A
        data B
        test1 : A = A
        "#;
        let ast = parse::parse(src);
        let ast: ast_step1::Ast = (&ast).into();
        let ast: ast_step2::Ast = ast.into();
        let b_id = ast
            .data_decl
            .iter()
            .find(|d| d.name == "B")
            .unwrap()
            .decl_id;
        let b_id = TypeId::DeclId(b_id);
        let t1 = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "test1")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        let v2 = TypeVariable::new();
        let r = apply_type_to_pattern(
            Type::argument_tuple_from_arguments(vec![t1.clone(), t1]),
            &PatternUnitForRestriction::argument_tuple_from_arguments(vec![
                vec![
                    PatternUnitForRestriction::Constructor {
                        id: b_id,
                        name: "B",
                        args: Vec::new(),
                    },
                    PatternUnitForRestriction::Binder(
                        TypeUnit::Variable(v2).into(),
                        DeclId::new(),
                    ),
                ],
            ]),
        );
        assert_eq!(r, None)
    }
}
