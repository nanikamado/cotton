use crate::ast_step2::{
    self,
    decl_id::DeclId,
    types::{
        marge_vec, unwrap_or_clone, Type, TypeMatchable, TypeMatchableRef,
        TypeUnit, TypeVariable,
    },
    IncompleteType, PatternForRestriction, PatternRestrictions,
    PatternUnitForRestriction, SubtypeRelations, TypeConstructor,
};
use fxhash::{FxHashMap, FxHashSet};
use hashbag::HashBag;
use itertools::Itertools;
use petgraph::{self, algo::tarjan_scc, graphmap::DiGraphMap};
use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, HashSet},
    fmt::Display,
    hash::Hash,
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
                TypeUnit::Const { name, id } => {
                    TypeUnit::Const { name, id }.into()
                }
                TypeUnit::Tuple(a, b) => TypeUnit::Tuple(
                    self.normalize_type(a),
                    self.normalize_type(b),
                )
                .into(),
            })
            .collect::<Type>()
            .into_iter()
            .collect();
        let mut needless = HashSet::new();
        for (a, b) in tus.iter().tuple_combinations() {
            if let Ok(r) = simplify_subtype_rel(
                a.clone().into(),
                b.clone().into(),
                Some(&mut Default::default()),
            ) {
                if r.is_empty() {
                    needless.insert(a.clone());
                    continue;
                }
            }
            if let Ok(r) = simplify_subtype_rel(
                b.clone().into(),
                a.clone().into(),
                Some(&mut Default::default()),
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
            Tuple(a, b) => Tuple(
                self.normalize_pattern_unit(*a).into(),
                self.normalize_pattern_unit(*b).into(),
            ),
            Binder(t, decl_id) => Binder(self.normalize_type(t), decl_id),
            Const { name, id } => Const { name, id },
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
                match simplify_subtype_rel(
                    a.clone(),
                    b.clone(),
                    Some(already_considered_relations),
                ) {
                    Ok(r) => Some(r),
                    Err(r) => {
                        log::debug!("a !<: b");
                        log::debug!("a = {a}");
                        log::debug!("b = {b}");
                        log::debug!(
                            "{}",
                            r.into_iter().rev().format_with(
                                "\n",
                                |(a, b), f| f(&format_args!(
                                    "because `{}` is not subtype of `{}`",
                                    a, b
                                ))
                            )
                        );
                        None
                    }
                }
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
        } else {
            assert_ne!(old_t, t);
            match i.cmp(&100) {
                Ordering::Equal => {
                    log::error!("loop count is about to reach the limit.");
                    log::debug!("old_t = {old_t}");
                    log::debug!("t = {t}");
                }
                Ordering::Greater => {
                    log::error!("loop count reached the limit.");
                    log::debug!("old_t = {old_t}");
                    log::debug!("t = {t}");
                    assert_ne!(old_t, t);
                    break;
                }
                _ => (),
            }
        }
    }
    t.normalize(map)
}

fn _simplify_type<'a, T: TypeConstructor<'a>>(
    map: &mut TypeVariableMap<'a>,
    mut t: IncompleteType<'a, T>,
) -> Option<(IncompleteType<'a, T>, bool)> {
    let t_before_simplify = t.clone();
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
                if s.is_empty() {
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
                if st.is_empty() {
                    log::debug!("t'{{1}} = {t}");
                }
                map.insert(&mut t.subtype_relations, *a, st);
                t = t.normalize(map)?;
                return Some((t, true));
            }
            (Some(st), _) if !vs.contains(a) => {
                if st.is_empty() {
                    log::debug!("t'{{1}} = {t}");
                }
                map.insert(&mut t.subtype_relations, *a, st);
                t = t.normalize(map)?;
                return Some((t, true));
            }
            (_, Some(we)) if we.is_empty() => {
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
                                    Some(
                                        &mut t
                                            .already_considered_relations
                                            .clone(),
                                    ),
                                )
                                .is_ok();
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
                if t_normalized != t_before_simplify {
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
    let updated = t != t_before_simplify;
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

type SubtypeRelationsVec<'a> = Vec<(Type<'a>, Type<'a>)>;

pub fn simplify_subtype_rel<'a>(
    sub: Type<'a>,
    sup: Type<'a>,
    mut already_considered_relations: Option<&mut SubtypeRelations<'a>>,
) -> Result<SubtypeRelationsVec<'a>, SubtypeRelationsVec<'a>> {
    let subsup = (sub, sup);
    let c = already_considered_relations
        .as_deref()
        .map(|a| a.contains(&subsup))
        .unwrap_or(false);
    let (sub, sup) = subsup;
    if c || sub == sup {
        return Ok(Vec::new());
    }
    use TypeMatchable::*;
    match (sub.clone().matchable(), sup.clone().matchable()) {
        (Fn(a1, r1), Fn(a2, r2)) => {
            let a = simplify_subtype_rel(
                a2,
                a1,
                already_considered_relations.as_deref_mut(),
            )
            .map_err(|mut a| {
                a.push((sub.clone(), sup.clone()));
                a
            })?;
            let r = simplify_subtype_rel(
                r1,
                r2,
                already_considered_relations.as_deref_mut(),
            )
            .map_err(|mut a| {
                a.push((sub, sup));
                a
            })?;
            Ok(marge_vec(a, r))
        }
        (Tuple(a1, b1), Tuple(a2, b2)) => {
            let mut r = simplify_subtype_rel(
                a1,
                a2,
                already_considered_relations.as_deref_mut(),
            )
            .map_err(|mut a| {
                a.push((sub.clone(), sup.clone()));
                a
            })?;
            r.append(
                &mut simplify_subtype_rel(b1, b2, already_considered_relations)
                    .map_err(|mut a| {
                        a.push((sub, sup));
                        a
                    })?,
            );
            Ok(r)
        }
        (Const { id: id1, .. }, Const { id: id2, .. }) => {
            if id1 == id2 {
                Ok(Vec::new())
            } else {
                Err(vec![(sub, sup)])
            }
        }
        (Fn(_, _), Tuple { .. } | Const { .. })
        | (Tuple { .. } | Const { .. }, Fn(_, _))
        | (Tuple(..), Const { .. })
        | (Const { .. }, Tuple(..))
        | (Fn(_, _) | Tuple { .. } | Const { .. }, Empty) => {
            Err(vec![(sub, sup)])
        }
        (Union(cs), b) => Ok(cs
            .into_iter()
            .map(|c| {
                simplify_subtype_rel(
                    c.into(),
                    b.clone().into(),
                    already_considered_relations.as_deref_mut(),
                )
            })
            .collect::<Result<Vec<_>, Vec<_>>>()
            .map_err(|mut a| {
                a.push((sub, sup));
                a
            })?
            .concat()),
        (Empty, _) => Ok(Vec::new()),
        (a, RecursiveAlias { body })
            if Type::from(a.clone()).is_subtype_of_with_rels(
                body.clone(),
                already_considered_relations
                    .as_deref_mut()
                    .cloned()
                    .as_mut(),
            ) =>
        {
            Ok(Vec::new())
        }
        (
            a @ (Tuple { .. } | Fn(_, _) | Const { .. }),
            RecursiveAlias { body },
        ) if already_considered_relations.is_some() => {
            let a = Type::from(a);
            if a.find_recursive_alias().is_some() {
                already_considered_relations
                    .as_deref_mut()
                    .unwrap()
                    .insert((sub.clone(), sup.clone()));
            }
            simplify_subtype_rel(
                a,
                unwrap_recursive_alias(body),
                already_considered_relations,
            )
            .map_err(|mut a| {
                a.push((sub, sup));
                a
            })
        }
        (
            RecursiveAlias { body },
            b @ (Tuple { .. }
            | Fn(_, _)
            | Union(_)
            | RecursiveAlias { .. }
            | Const { .. }),
        ) if already_considered_relations.is_some() => {
            let b: Type = b.into();
            if b.find_recursive_alias().is_some() {
                already_considered_relations
                    .as_deref_mut()
                    .unwrap()
                    .insert((
                        RecursiveAlias { body: body.clone() }.into(),
                        b.clone(),
                    ));
            }
            simplify_subtype_rel(
                unwrap_recursive_alias(body),
                b,
                already_considered_relations,
            )
            .map_err(|mut a| {
                a.push((sub, sup));
                a
            })
        }
        (Tuple(h, t), Union(b))
            if b.iter().all(|u| {
                if let TypeUnit::Tuple(u, _) = &**u {
                    u == &h
                } else {
                    false
                }
            }) =>
        {
            Ok(vec![(
                t,
                b.into_iter()
                    .flat_map(|u| {
                        if let TypeUnit::Tuple(_, u) = unwrap_or_clone(u) {
                            u
                        } else {
                            panic!()
                        }
                    })
                    .collect(),
            )])
        }
        (a @ Tuple(..), Union(b)) => {
            let a: Type = a.into();
            let mut new_bs = Type::default();
            let mut updated = false;
            for b in b.iter() {
                if a.clone().is_subtype_of_with_rels(
                    b.clone().into(),
                    already_considered_relations
                        .as_deref_mut()
                        .cloned()
                        .as_mut(),
                ) {
                    return Ok(Vec::new());
                }
                let (_, _, b_in, b_out) = a
                    .clone()
                    .intersection_and_difference_broad((*b).clone().into());
                new_bs.union_in_place(b_in);
                if !b_out.is_empty() {
                    updated = true;
                }
            }
            if updated {
                simplify_subtype_rel(a, new_bs, already_considered_relations)
                    .map_err(|mut a| {
                        a.push((sub, sup));
                        a
                    })
            } else if already_considered_relations.is_some()
                && b.iter()
                    .any(|u| matches!(&**u, TypeUnit::RecursiveAlias { .. }))
            {
                if a.find_recursive_alias().is_some() {
                    already_considered_relations
                        .as_deref_mut()
                        .unwrap()
                        .insert((sub.clone(), sup.clone()));
                }
                let b = b
                    .into_iter()
                    .flat_map(|u| match unwrap_or_clone(u) {
                        TypeUnit::RecursiveAlias { body } => {
                            unwrap_recursive_alias(body)
                        }
                        u => u.into(),
                    })
                    .collect();
                simplify_subtype_rel(a, b, already_considered_relations)
                    .map_err(|mut a| {
                        a.push((sub, sup));
                        a
                    })
            } else {
                match a.disjunctive() {
                    Ok(a) => Ok(a
                        .into_iter()
                        .map(|a| {
                            simplify_subtype_rel(
                                unwrap_or_clone(a).into(),
                                b.clone(),
                                already_considered_relations.as_deref_mut(),
                            )
                        })
                        .collect::<Result<Vec<_>, Vec<_>>>()
                        .map_err(|mut a| {
                            a.push((sub, sup));
                            a
                        })?
                        .concat()),
                    Err(a) => Ok(vec![(a.into(), b)]),
                }
            }
        }
        (a, Union(u))
            if u.iter().any(|b| {
                Type::from(a.clone()).is_subtype_of_with_rels(
                    b.clone().into(),
                    already_considered_relations
                        .as_deref_mut()
                        .cloned()
                        .as_mut(),
                )
            }) =>
        {
            Ok(Vec::new())
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
            .map_err(|mut a| {
                a.push((sub, sup));
                a
            })
        }
        (sub, sup) => Ok(vec![(sub.into(), sup.into())]),
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
            PatternUnitForRestriction::Binder(t, _decl_id) => t.clone(),
            PatternUnitForRestriction::Const { name, id } => {
                TypeUnit::Const { name, id: *id }.into()
            }
            PatternUnitForRestriction::Tuple(a, b) => {
                TypeUnit::Tuple((&**a).into(), (&**b).into()).into()
            }
        }
    }
}

fn type_intersection<'a>(a: Type<'a>, b: Type<'a>) -> Option<Type<'a>> {
    use TypeMatchable::*;
    match (a.matchable(), b.matchable()) {
        (Tuple { .. }, Fn(_, _)) | (Fn(_, _), Tuple { .. }) => {
            Some(TypeMatchable::Empty.into())
        }
        (Tuple(a1, b1), Tuple(a2, b2)) => Some(
            TypeUnit::Tuple(
                type_intersection(a1, a2)?,
                type_intersection(b1, b2)?,
            )
            .into(),
        ),
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
                Some(&mut Default::default()),
            );
            if let Ok(ab) = ab {
                if ab.is_empty() {
                    return Some(a);
                }
            }
            let ba = simplify_subtype_rel(
                b.clone(),
                a,
                Some(&mut Default::default()),
            );
            if let Ok(ba) = ba {
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
    let mut down_up: Type = TypeMatchable::Empty.into();
    let mut down_down: Type = TypeMatchable::Empty.into();
    for (a, b) in subtype_relation {
        if a.all_type_variables().is_empty()
            && b.clone().is_subtype_of(t.clone())
        {
            down_up = down_up.union(b.clone());
            down_down = down_down.union(a.clone());
        }
    }
    if !down_up.is_empty() {
        t.diff(&down_up).union(down_down)
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
    let mut remained = t.clone();
    let decl_type_map_in_pattern: FxHashMap<DeclId, Type> = pattern
        .iter()
        .flat_map(|p| p.decl_type_map())
        .map(|(d, t)| (d, t.clone()))
        .collect();
    let mut subtype_rels = SubtypeRelations::default();
    let mut not_sure = false;
    for p in pattern {
        let TypeDestructResult {
            remained: r,
            matched: _,
            bind_matched,
            kind,
        } = destruct_type_by_pattern(remained, p);
        remained = r;
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
            }
        }
    }
    if !remained.is_empty() && !not_sure {
        log::debug!("missing type = {}", remained);
        None
    } else {
        if not_sure {
            let pattern_t = pattern_to_type(pattern);
            let r = simplify_subtype_rel(
                t,
                pattern_t,
                Some(&mut Default::default()),
            )
            .ok()?;
            subtype_rels.add_subtype_rels(r);
        }
        Some(subtype_rels)
    }
}

fn pattern_unit_to_type<'a>(p: &PatternUnitForRestriction<'a>) -> Type<'a> {
    use PatternUnitForRestriction::*;
    match p {
        I64 => Type::from_str("I64"),
        Str => Type::from_str("String"),
        Binder(t, _) => t.clone(),
        Const { name, id } => TypeUnit::Const { name, id: *id }.into(),
        Tuple(a, b) => TypeUnit::Tuple((&**a).into(), (&**b).into()).into(),
    }
}

fn pattern_to_type<'a>(p: &[PatternUnitForRestriction<'a>]) -> Type<'a> {
    let mut t = Type::default();
    for p in p {
        t = t.union(pattern_unit_to_type(p));
    }
    t
}

#[derive(Debug, PartialEq, Eq)]
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
        remained = remained.union(r);
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
            TypeUnit::Const { id: id1, name },
            PatternUnitForRestriction::Const { id: id2, .. },
        ) if id1 == *id2 => TypeDestructResult {
            remained: Type::default(),
            matched: Some(TypeUnit::Const { id: id1, name }.into()),
            bind_matched: Some(Vec::new()),
            kind: DestructResultKind::Ok,
        },
        (TypeUnit::Tuple(a1, a2), PatternUnitForRestriction::Tuple(p1, p2)) => {
            let r1 = destruct_type_by_pattern(a1, p1);
            if r1.kind == DestructResultKind::Fail {
                TypeDestructResult {
                    remained: TypeUnit::Tuple(r1.remained, a2).into(),
                    matched: None,
                    bind_matched: None,
                    kind: DestructResultKind::Fail,
                }
            } else {
                let r2 = destruct_type_by_pattern(a2, p2);
                if r2.kind == DestructResultKind::Fail {
                    TypeDestructResult {
                        remained: TypeUnit::Tuple(
                            r1.remained.union(r1.matched.unwrap()),
                            r2.remained,
                        )
                        .into(),
                        matched: None,
                        bind_matched: None,
                        kind: DestructResultKind::Fail,
                    }
                } else {
                    let not_sure = r1.kind == DestructResultKind::NotSure
                        || r2.kind == DestructResultKind::NotSure;
                    TypeDestructResult {
                        remained: Type::default()
                            .union_unit(TypeUnit::Tuple(
                                r1.remained.clone(),
                                r2.remained.clone(),
                            ))
                            .union_unit(TypeUnit::Tuple(
                                r1.remained.clone(),
                                r2.matched.clone().unwrap(),
                            ))
                            .union_unit(TypeUnit::Tuple(
                                r1.matched.clone().unwrap(),
                                r2.remained,
                            )),

                        matched: Some(
                            TypeUnit::Tuple(
                                r1.matched.unwrap(),
                                r2.matched.unwrap(),
                            )
                            .into(),
                        ),
                        bind_matched: Some(marge_vec(
                            r1.bind_matched.unwrap(),
                            r2.bind_matched.unwrap(),
                        )),
                        kind: if not_sure {
                            DestructResultKind::NotSure
                        } else {
                            DestructResultKind::Ok
                        },
                    }
                }
            }
        }
        (t, PatternUnitForRestriction::Binder(_, decl_id)) => {
            let t = Type::from(t);
            TypeDestructResult {
                remained: Type::default(),
                matched: Some(t.clone()),
                bind_matched: Some(vec![(*decl_id, t)]),
                kind: DestructResultKind::Ok,
            }
        }
        (TypeUnit::Variable(v), _) => TypeDestructResult {
            remained: Type::default(),
            matched: Some(TypeUnit::Variable(v).into()),
            bind_matched: None,
            kind: DestructResultKind::NotSure,
        },
        (TypeUnit::RecursiveAlias { body }, p) => {
            destruct_type_by_pattern(unwrap_recursive_alias(body), p)
        }
        (remained, _) => TypeDestructResult {
            remained: remained.into(),
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
            types::{
                Type, TypeMatchable, TypeMatchableRef, TypeUnit, TypeVariable,
            },
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
        assert_eq!(format!("{}", st), "I64 -> [{:I64 | :String}] forall\n--");
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
            Some(&mut Default::default()),
        );
        assert!(t.is_err());
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
        if let TypeUnit::Tuple(h, _) = &**t1.iter().next().unwrap() {
            if let TypeMatchableRef::Const { name, id } = h.matchable_ref() {
                let false_ =
                    PatternUnitForRestriction::argument_tuple_from_arguments(
                        vec![PatternUnitForRestriction::Const {
                            id: TypeId::Intrinsic(IntrinsicType::False),
                            name: "False",
                        }],
                    );
                let p = PatternUnitForRestriction::Tuple(
                    PatternUnitForRestriction::Const { name, id }.into(),
                    PatternUnitForRestriction::argument_tuple_from_arguments(
                        vec![false_.clone(), false_],
                    )
                    .into(),
                );
                let TypeDestructResult {
                    remained,
                    matched,
                    bind_matched: _,
                    kind: _,
                } = destruct_type_by_pattern(t1, &p);
                assert_eq!(
                    format!("{}", remained),
                    r#"/\[{[False, True] | [True, [{:False | :True}]]}]"#
                );
                assert_eq!(
                    format!("{}", matched.unwrap()),
                    r#"/\[False, False]"#
                )
            } else {
                panic!()
            }
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
        data T(C, N, T1, T2) forall { C, N, T1, T2 }
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
        let p = PatternUnitForRestriction::Tuple(
            PatternUnitForRestriction::Const { name: "", id: t_id }.into(),
            PatternUnitForRestriction::argument_tuple_from_arguments(vec![
                PatternUnitForRestriction::Binder(
                    TypeMatchable::Empty.into(),
                    DeclId::new(),
                ),
                PatternUnitForRestriction::Tuple(
                    PatternUnitForRestriction::Const { id: t_id, name: "" }
                        .into(),
                    PatternUnitForRestriction::argument_tuple_from_arguments(
                        vec![
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
                    )
                    .into(),
                ),
                PatternUnitForRestriction::Binder(
                    TypeMatchable::Empty.into(),
                    DeclId::new(),
                ),
            ])
            .into(),
        );
        let TypeDestructResult {
            remained,
            matched,
            bind_matched: _,
            kind: _,
        } = destruct_type_by_pattern(t1, &p);
        assert_eq!(
            format!("{}", remained),
            r#"{E | T[(), E, rec[{E | T[(), d0, d0]}]]}"#
                .strip_margin()
                .replace('\n', "")
        );
        assert_eq!(
            format!("{}", matched.unwrap()),
            r#"T[(), T[(), rec[{E | T[(), d0, d0]}], rec[{E | T[(), d0, d0]}]], rec[{E | T[(), d0, d0]}]]"#
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
            &vec![
                PatternUnitForRestriction::argument_tuple_from_arguments(vec![
                    PatternUnitForRestriction::I64,
                ]),
                PatternUnitForRestriction::argument_tuple_from_arguments(vec![
                    PatternUnitForRestriction::Binder(
                        TypeUnit::Variable(v2).into(),
                        DeclId::new(),
                    ),
                ]),
            ],
        );
        let subtype_rels = r.unwrap();
        assert_eq!(
            format!("{}", subtype_rels),
            format!(
                r#"    {1} < {0},
                  |    t1 < {{{1} | I64}},
                  |    I64 < {0},
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
            &vec![PatternUnitForRestriction::argument_tuple_from_arguments(
                vec![
                    PatternUnitForRestriction::Const {
                        id: b_id,
                        name: "B",
                    },
                    PatternUnitForRestriction::Binder(
                        TypeUnit::Variable(v2).into(),
                        DeclId::new(),
                    ),
                ],
            )],
        );
        assert_eq!(r, None)
    }
}
