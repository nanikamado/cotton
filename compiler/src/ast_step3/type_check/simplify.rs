use super::match_operand::{
    close_type, disclose_type, disclose_type_unit, MatchOperand,
    MatchOperandUnit,
};
use super::VariableRequirement;
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::merge_span;
use crate::ast_step2::types::{
    merge_vec, unwrap_or_clone, Type, TypeConstructor, TypeMatchable,
    TypeMatchableRef, TypeUnit, TypeVariable,
};
use crate::ast_step2::{
    self, Field, PatternRestriction, PatternRestrictions,
    PatternUnitForRestriction, RelOrigin, SubtypeRelations, TypeId,
    TypeWithEnv,
};
use crate::errors::{CompileError, NotSubtypeReason};
use doki::intrinsics::IntrinsicType;
use fxhash::{FxHashMap, FxHashSet};
use hashbag::HashBag;
use itertools::Itertools;
use parser::Span;
use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;
use std::hash::Hash;
use std::iter::Extend;
use std::vec;
use tracing_mutex::stdsync::TracingRwLock as RwLock;

const LOOP_LIMIT: i32 = 8;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct TypeVariableMap(BTreeMap<TypeVariable, Type>);

impl TypeVariableMap {
    pub fn find(&mut self, key: TypeVariable) -> Type {
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

    pub fn normalize_type(&mut self, t: Type) -> Type {
        let tus: Vec<_> = t
            .into_iter()
            .flat_map(|tu| match unwrap_or_clone(tu) {
                TypeUnit::Variable(v) => self.find(v),
                TypeUnit::RecursiveAlias { body } => {
                    let body = self.normalize_type(body);
                    debug_assert!(body.iter().all(|t| {
                        **t != TypeUnit::Variable(TypeVariable::RecursiveIndex(
                            0,
                        ))
                    }));
                    match body.matchable() {
                        TypeMatchable::RecursiveAlias { body } => {
                            TypeUnit::RecursiveAlias {
                                body: body.increment_recursive_index(1, -1),
                            }
                            .into()
                        }
                        body => TypeUnit::RecursiveAlias { body: body.into() }
                            .into(),
                    }
                }
                TypeUnit::Const { id } => TypeUnit::Const { id }.into(),
                TypeUnit::Tuple(a, bs) => {
                    #[cfg(debug_assertions)]
                    if let TypeMatchableRef::Const {
                        id: TypeId::Intrinsic(IntrinsicType::Fn),
                    } = a.matchable_ref()
                    {
                        for b in bs.iter() {
                            if let TypeUnit::Tuple(b, _) = &**b
                            {
                                for b in b.iter() {
                                    debug_assert!(matches!(
                                        **b,
                                        TypeUnit::Variance(
                                            ast_step2::types::Variance::Contravariant,
                                            _
                                        )
                                    ))
                                }
                            } else {
                                panic!()
                            }
                        }
                    };
                    TypeUnit::Tuple(
                        self.normalize_type(a),
                        self.normalize_type(bs),
                    )
                    .into()
                }
                TypeUnit::TypeLevelFn(f) => {
                    TypeUnit::TypeLevelFn(self.normalize_type(f)).into()
                }
                TypeUnit::TypeLevelApply { f, a } => self
                    .normalize_type(f)
                    .type_level_function_apply(self.normalize_type(a)),
                TypeUnit::Restrictions {
                    t,
                    variable_requirements,
                    subtype_relations,
                } => TypeUnit::Restrictions {
                    t: self.normalize_type(t),
                    variable_requirements: variable_requirements
                        .into_iter()
                        .map(|(name, req)| (name, self.normalize_type(req)))
                        .collect(),
                    subtype_relations: subtype_relations
                        .into_iter()
                        .map(|(a, b)| {
                            (self.normalize_type(a), self.normalize_type(b))
                        })
                        .collect(),
                }
                .into(),
                TypeUnit::Any => TypeUnit::Any.into(),
                TypeUnit::Variance(v, t) => {
                    TypeUnit::Variance(v, self.normalize_type(t)).into()
                }
            })
            .collect::<Type>()
            .into_iter()
            .collect();
        let mut needless = FxHashSet::default();
        for (a, b) in tus.iter().tuple_combinations() {
            if let Ok(r) =
                simplify_subtype_rel(a.clone().into(), b.clone().into(), None)
            {
                if r.is_empty() {
                    needless.insert(a.clone());
                    continue;
                }
            }
            if let Ok(r) =
                simplify_subtype_rel(b.clone().into(), a.clone().into(), None)
            {
                if r.is_empty() {
                    needless.insert(b.clone());
                }
            }
        }
        tus.into_iter().filter(|t| !needless.contains(t)).collect()
    }

    fn normalize_pattern_unit(
        &mut self,
        pattern_unit: PatternUnitForRestriction,
    ) -> PatternUnitForRestriction {
        use PatternUnitForRestriction::*;
        match pattern_unit {
            I64 => I64,
            Str => Str,
            Tuple(a, b) => Tuple(
                self.normalize_pattern_unit(*a).into(),
                self.normalize_pattern_unit(*b).into(),
            ),
            Binder(t, decl_id) => Binder(self.normalize_type(t), decl_id),
            Const { id } => Const { id },
            TypeRestriction(p, t) => {
                TypeRestriction(Box::new(self.normalize_pattern_unit(*p)), t)
            }
            Apply(p) => Apply(Box::new(self.normalize_pattern_unit(*p))),
        }
    }

    fn _insert_type(
        &mut self,
        subtype: &mut SubtypeRelations,
        key: Type,
        value: Type,
        origin: Option<RelOrigin>,
        log: bool,
    ) {
        if key == value {
            return;
        }
        use TypeMatchableRef::*;
        let (key, value) = match (key.matchable_ref(), value.matchable_ref()) {
            (Variable(key), Variable(value)) => {
                if key < value {
                    (value, TypeUnit::Variable(key).into())
                } else {
                    (key, TypeUnit::Variable(value).into())
                }
            }
            (Variable(key), Union(value))
                if value.iter().any(
                    |v| matches!(&**v, TypeUnit::Variable(v) if *v == key),
                ) =>
            {
                panic!()
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
            (Variable(v), _) if value.is_wrapped_by_const() => {
                let value = value.clone().replace_num(
                    v,
                    &TypeUnit::Variable(TypeVariable::RecursiveIndex(0)).into(),
                );
                (v, TypeUnit::RecursiveAlias { body: value }.into())
            }
            (_, Variable(v)) if key.is_wrapped_by_const() => {
                let key = key.clone().replace_num(
                    v,
                    &TypeUnit::Variable(TypeVariable::RecursiveIndex(0)).into(),
                );
                (v, TypeUnit::RecursiveAlias { body: key }.into())
            }
            (
                TypeLevelApply { f: a_f, a: a_a },
                TypeLevelApply { f: b_f, a: b_a },
            ) => {
                self._insert_type(
                    subtype,
                    a_f.clone(),
                    b_f.clone(),
                    origin.clone(),
                    log,
                );
                self._insert_type(
                    subtype,
                    a_a.clone(),
                    b_a.clone(),
                    origin,
                    log,
                );
                return;
            }
            (Tuple(a1, b1), Tuple(a2, b2)) => {
                self._insert_type(
                    subtype,
                    a1.clone(),
                    a2.clone(),
                    origin.clone(),
                    log,
                );
                self._insert_type(subtype, b1.clone(), b2.clone(), origin, log);
                return;
            }
            (Variance(va, a), Variance(vb, b)) if va == vb => {
                self._insert_type(subtype, a.clone(), b.clone(), origin, log);
                return;
            }
            (_, TypeLevelApply { f, a }) => {
                if let TypeMatchableRef::Variable(f) = f.matchable_ref() {
                    let (replaced_key, u) =
                        key.clone().replace_type_union_with_update_flag(
                            a,
                            &TypeUnit::Variable(TypeVariable::RecursiveIndex(
                                0,
                            )),
                            0,
                        );
                    if u {
                        self.insert(
                            subtype,
                            f,
                            TypeUnit::TypeLevelFn(replaced_key).into(),
                        );
                        return;
                    }
                }
                subtype.insert((
                    key.clone(),
                    value.clone(),
                    origin.clone().unwrap(),
                ));
                let o = origin.unwrap();
                subtype.insert((
                    value,
                    key,
                    RelOrigin {
                        left: o.right,
                        right: o.left,
                        span: o.span,
                    },
                ));
                return;
            }
            _ => {
                if let Some(origin) = origin {
                    subtype.insert((
                        key.clone(),
                        value.clone(),
                        origin.clone(),
                    ));
                    subtype.insert((
                        value,
                        key,
                        RelOrigin {
                            left: origin.right,
                            right: origin.left,
                            span: origin.span,
                        },
                    ));
                } else {
                    self.force_insert_type(value, key);
                }
                return;
            }
        };
        if let Some(old) = self.0.get(&key) {
            if log {
                log::debug!("{key} is already pointing to {old}. ignored");
            }
            let key = self.find(key);
            self._insert_type(subtype, key, value, origin, log);
        } else {
            if log {
                log::debug!("{key} --> {value}");
            }
            debug_assert!(!key.is_recursive_index());
            self.0.insert(key, value);
        }
    }

    fn force_insert_type(&mut self, key: Type, value: Type) {
        let mut tmp_subtype = SubtypeRelations::default();
        tmp_subtype.insert((
            value.clone(),
            key.clone(),
            RelOrigin {
                left: Default::default(),
                right: Default::default(),
                span: Default::default(),
            },
        ));
        tmp_subtype.insert((
            key,
            value,
            RelOrigin {
                left: Default::default(),
                right: Default::default(),
                span: Default::default(),
            },
        ));
        let r = tmp_subtype
            .normalize(self, &mut Default::default())
            .unwrap();
        debug_assert!(r.is_empty());
    }

    fn insert_type_helper(
        &mut self,
        subtype: &mut SubtypeRelations,
        k: Type,
        v: Type,
        origin: Option<RelOrigin>,
        log: bool,
    ) {
        let key = self.normalize_type(k.clone());
        let value = self.normalize_type(v.clone());
        if log {
            log::debug!(
                "{k} {} ----> {v} {}",
                if k == key {
                    "".to_string()
                } else {
                    format!("({key})")
                },
                if v == value {
                    "".to_string()
                } else {
                    format!("({value})")
                }
            );
        }
        self._insert_type(subtype, key, value, origin, log)
    }

    pub fn insert_type(
        &mut self,
        subtype: &mut SubtypeRelations,
        k: Type,
        v: Type,
        origin: Option<RelOrigin>,
    ) {
        self.insert_type_helper(subtype, k, v, origin, true);
    }

    pub fn insert_type_without_log(
        &mut self,
        subtype: &mut SubtypeRelations,
        k: Type,
        v: Type,
        origin: Option<RelOrigin>,
    ) {
        self.insert_type_helper(subtype, k, v, origin, false);
    }

    pub fn insert(
        &mut self,
        subtype: &mut SubtypeRelations,
        k: TypeVariable,
        v: Type,
    ) {
        debug_assert!(!k.is_recursive_index());
        let key = self.find(k);
        let value = self.normalize_type(v.clone());
        log::debug!(
            "{k} {} ----> {v} {}",
            match key.matchable_ref() {
                TypeMatchableRef::Variable(key) if k == key => "".to_string(),
                _ => format!("({key})"),
            },
            if v == value {
                "".to_string()
            } else {
                format!("({value})")
            }
        );
        self._insert_type(subtype, key, value, None, true)
    }
}

impl SubtypeRelations {
    pub fn merge(mut self, other: Self) -> Self {
        self.extend(other.0);
        self
    }

    pub fn possible_strongest(
        &mut self,
        map: &mut TypeVariableMap,
        t: TypeVariable,
        pattern_restrictions: &PatternRestrictions,
        variable_requirements: &[VariableRequirement],
        fn_apply_dummies: &BTreeMap<Type, (Type, RelOrigin)>,
    ) -> Option<Type> {
        let t = map.find(t);
        if let TypeMatchableRef::Variable(v) = t.matchable_ref() {
            possible_strongest(
                v,
                self,
                pattern_restrictions,
                variable_requirements,
                fn_apply_dummies,
            )
        } else {
            Some(t)
        }
    }

    pub fn possible_weakest(
        &mut self,
        map: &mut TypeVariableMap,
        t: TypeVariable,
        variable_requirements: &[VariableRequirement],
        pattern_restrictions: &PatternRestrictions,
        fn_apply_dummies: &BTreeMap<Type, (Type, RelOrigin)>,
    ) -> Option<Type> {
        let t = map.find(t);
        if let TypeMatchableRef::Variable(v) = t.matchable_ref() {
            possible_weakest(
                v,
                self,
                variable_requirements,
                pattern_restrictions,
                fn_apply_dummies,
                map,
            )
        } else {
            Some(t)
        }
    }

    pub fn type_variables_in_sub_rel<T: FromIterator<TypeVariable>>(
        &self,
    ) -> T {
        self.iter()
            .flat_map(|(a, b, _)| {
                a.all_type_variables_iter()
                    .chain(b.all_type_variables_iter())
            })
            .unique()
            .collect()
    }

    pub fn normalize(
        mut self,
        map: &mut TypeVariableMap,
        already_considered_relations: &mut BTreeSet<(Type, Type)>,
    ) -> Result<Self, CompileError> {
        self = self.normalize_subtype_rel(map, already_considered_relations)?;
        let eqs = find_eq_types(&self);
        let eqs_is_empty = eqs.is_empty();
        for (from, to) in eqs {
            map.insert(&mut self, from, to);
        }
        if eqs_is_empty {
            Ok(self)
        } else {
            self.normalize(map, already_considered_relations)
        }
    }

    pub fn normalize_with_unwrapping(
        mut self,
        map: &mut TypeVariableMap,
        already_considered_relations: &mut BTreeSet<(Type, Type)>,
    ) -> Result<Self, CompileError> {
        self = self.normalize_subtype_rel_with_unwrapping(
            map,
            already_considered_relations,
        )?;
        let eqs = find_eq_types(&self);
        let eqs_is_empty = eqs.is_empty();
        for (from, to) in eqs {
            map.insert(&mut self, from, to);
        }
        if eqs_is_empty {
            Ok(self)
        } else {
            self.normalize_with_unwrapping(map, already_considered_relations)
        }
    }

    fn normalize_subtype_rel(
        self,
        map: &mut TypeVariableMap,
        _already_considered_relations: &mut BTreeSet<(Type, Type)>,
    ) -> Result<Self, CompileError> {
        let mut new_s = SubtypeRelations::default();
        for (a, b, origin) in self {
            let a = map.normalize_type(a);
            let b = map.normalize_type(b);
            if a.matchable_ref() == TypeMatchableRef::Any {
                map.insert_type(
                    &mut new_s,
                    b,
                    TypeUnit::Any.into(),
                    Some(origin),
                );
                continue;
            }
            match simplify_subtype_rel(a, b, None) {
                Ok(r) => {
                    new_s.extend(
                        r.into_iter().map(move |(a, b)| (a, b, origin.clone())),
                    );
                }
                Err(_) => {
                    let mut already_considered_relations = Default::default();
                    let origin_a = map.normalize_type(origin.left);
                    let origin_b = map.normalize_type(origin.right);
                    let r = simplify_subtype_rel(
                        origin_a.clone(),
                        origin_b.clone(),
                        Some(&mut already_considered_relations),
                    );
                    let r = match r {
                        Ok(r) => {
                            panic!("{origin_a} < {origin_b}. ({r:?})")
                        }
                        Err(r) => r,
                    };
                    return Err(CompileError::NotSubtypeOf {
                        sub_type: origin_a,
                        super_type: origin_b,
                        reason: r,
                        span: origin.span,
                    });
                }
            }
        }
        Ok(new_s)
    }

    fn normalize_subtype_rel_with_unwrapping(
        mut self,
        map: &mut TypeVariableMap,
        already_considered_relations: &mut BTreeSet<(Type, Type)>,
    ) -> Result<Self, CompileError> {
        self = self
            .into_iter()
            .map(|(a, b, origin)| {
                let a = map.normalize_type(a);
                let b = map.normalize_type(b);
                match simplify_subtype_rel(
                    a,
                    b,
                    Some(&mut already_considered_relations.clone()),
                ) {
                    Ok(r) => Ok(r
                        .into_iter()
                        .map(move |(a, b)| (a, b, origin.clone()))),
                    Err(_) => {
                        let mut already_considered_relations =
                            Default::default();
                        let origin_a = map.normalize_type(origin.left);
                        let origin_b = map.normalize_type(origin.right);
                        let r = simplify_subtype_rel(
                            origin_a.clone(),
                            origin_b.clone(),
                            Some(&mut already_considered_relations),
                        );
                        let r = match r {
                            Ok(r) => {
                                panic!("{origin_a} < {origin_b}. ({r:?})")
                            }
                            Err(r) => r,
                        };
                        Err(CompileError::NotSubtypeOf {
                            sub_type: origin_a,
                            super_type: origin_b,
                            reason: r,
                            span: origin.span,
                        })
                    }
                }
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect();
        Ok(self)
    }
}

pub fn simplify_type<T: TypeConstructor>(
    map: &mut TypeVariableMap,
    mut t: TypeWithEnv<T>,
    env: &mut Env,
) -> Result<TypeWithEnv<T>, CompileError> {
    let mut i = 0;
    t = t.normalize(map)?;
    loop {
        i += 1;
        let updated;
        let old_t = t.clone();
        (t, updated) = _simplify_type(map, t, env)?;
        t = t.normalize(map)?;
        if !updated {
            debug_assert_eq!(
                t.clone().normalize(map),
                _simplify_type(map, t.clone(), env)
                    .unwrap()
                    .0
                    .normalize(map)
            );
            break;
        } else {
            debug_assert_ne!(old_t, t);
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
                    break;
                }
                _ => (),
            }
        }
    }
    t.normalize(map)
}

fn _simplify_type<T: TypeConstructor>(
    map: &mut TypeVariableMap,
    t: TypeWithEnv<T>,
    env: &mut Env,
) -> Result<(TypeWithEnv<T>, bool), CompileError> {
    let t_before_simplify = t.clone();
    log::debug!("t = {}", t);
    let (mut t, updated) = simplify_dummies(t, map);
    if updated {
        return Ok((t, true));
    }
    log::trace!("t{{1}} = {}", t);
    for cov in mk_covariant_candidates(&t) {
        if !cov.is_recursive_index()
            && !mk_contravariant_candidates(&t).contains(&cov)
        {
            if let Some(s) = t.subtype_relations.possible_strongest(
                map,
                cov,
                &t.pattern_restrictions,
                &t.variable_requirements,
                &t.fn_apply_dummies,
            ) {
                map.insert(&mut t.subtype_relations, cov, s);
                return Ok((t, true));
            }
        }
    }
    log::trace!("t{{2}} = {}", t);
    for cont in mk_contravariant_candidates(&t) {
        if !cont.is_recursive_index()
            && !mk_covariant_candidates(&t).contains(&cont)
        {
            if let Some(s) = t.subtype_relations.possible_weakest(
                map,
                cont,
                &t.variable_requirements,
                &t.pattern_restrictions,
                &t.fn_apply_dummies,
            ) {
                map.insert(&mut t.subtype_relations, cont, s);
                return Ok((t, true));
            }
        }
    }
    let new_t = t.clone().normalize_with_unwrapping(map)?;
    if new_t != t {
        return Ok((new_t, true));
    }
    log::trace!("t{{3}} = {}", t);
    let type_variables_in_sub_rel: FxHashSet<TypeVariable> =
        t.subtype_relations.type_variables_in_sub_rel();
    for a in &type_variables_in_sub_rel {
        let vs = t.type_variables_in_env_except_for_subtype_rel();
        let st = t.subtype_relations.possible_strongest(
            map,
            *a,
            &t.pattern_restrictions,
            &t.variable_requirements,
            &t.fn_apply_dummies,
        );
        let we = t.subtype_relations.possible_weakest(
            map,
            *a,
            &t.variable_requirements,
            &t.pattern_restrictions,
            &t.fn_apply_dummies,
        );
        match (st, we) {
            (Some(st), Some(we)) if st == we => {
                if st.is_empty() {
                    log::debug!("t{{5}} = {t}");
                }
                map.insert(&mut t.subtype_relations, *a, st);
                return Ok((t, true));
            }
            (Some(swt), _) if !vs.contains(a) => {
                if swt.is_empty() {
                    log::debug!("t{{6}} = {t}");
                }
                map.insert(&mut t.subtype_relations, *a, swt);
                return Ok((t, true));
            }
            (_, Some(we)) if we.is_empty() => {
                map.insert(
                    &mut t.subtype_relations,
                    *a,
                    TypeMatchable::Empty.into(),
                );
                return Ok((t, true));
            }
            _ => (),
        }
    }
    log::trace!("t{{7}} = {}", t);
    let v_in_env = t.type_variables_in_env_except_for_subtype_rel();
    let type_variables_in_sub_rel: HashBag<TypeVariable> =
        t.subtype_relations.type_variables_in_sub_rel();
    for (v, count) in type_variables_in_sub_rel {
        if count == 1 && !v_in_env.contains(&v) {
            if let Some(new_t) = t.subtype_relations.possible_strongest(
                map,
                v,
                &t.pattern_restrictions,
                &t.variable_requirements,
                &t.fn_apply_dummies,
            ) {
                map.insert(&mut t.subtype_relations, v, new_t);
                return Ok((t, true));
            }
        }
    }
    log::trace!("t{{8}} = {}", t);
    for (
        i,
        PatternRestriction {
            type_: ts,
            pattern,
            span: _,
            allow_inexhaustive: _,
        },
    ) in t.pattern_restrictions.iter().enumerate()
    {
        if pattern.len() == 1
            && !ts.is_empty()
            && ts
                .clone()
                .arguments_from_argument_tuple()
                .iter()
                .zip(&pattern[0].0.clone().arguments_from_argument_tuple())
                .all(|(t, p)| {
                    if let PatternUnitForRestriction::Binder(p_t, _) = p {
                        t == p_t
                    } else {
                        false
                    }
                })
        {
            t.pattern_restrictions.remove(i);
            return Ok((t, true));
        }
    }
    log::trace!("t{{10}} = {}", t);
    for (i, pattern_restriction) in
        t.pattern_restrictions.clone().iter().enumerate()
    {
        let ApplyTypeToPatternResult {
            subtype_relations: subtype,
            not_sure,
            updated,
        } = apply_type_to_pattern(
            pattern_restriction,
            pattern_restriction
                .type_
                .all_type_variables_iter()
                .next()
                .is_none(),
            env,
            map,
        )?;
        if !not_sure {
            t.pattern_restrictions.remove(i);
            t.subtype_relations.extend(subtype);
            return Ok((t, true));
        } else if updated {
            let mut t_normalized = t.clone();
            t_normalized.subtype_relations.extend(subtype);
            t_normalized = t_normalized.normalize(map)?;
            if t_normalized != t {
                return Ok((t_normalized, true));
            }
        }
    }
    log::trace!("t{{11}} = {}", t);
    if t.variable_requirements.is_empty() {
        let c = t.constructor.clone();
        for v in t.constructor.all_type_variables() {
            if let (Some(we), Some(st)) = (
                t.subtype_relations.possible_weakest(
                    map,
                    v,
                    &t.variable_requirements,
                    &t.pattern_restrictions,
                    &t.fn_apply_dummies,
                ),
                t.subtype_relations.possible_strongest(
                    map,
                    v,
                    &t.pattern_restrictions,
                    &t.variable_requirements,
                    &t.fn_apply_dummies,
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
                    return Ok((t, true));
                }
            }
        }
        log::trace!("t{{12}} = {}", t);
        let contravariant_candidates = mk_contravariant_candidates(&t);
        t.pattern_restrictions = t
            .pattern_restrictions
            .into_iter()
            .map(|pattern_restriction| {
                let pattern_ts: Vec<_> = pattern_restriction
                    .type_
                    .arguments_from_argument_tuple()
                    .iter()
                    .map(|pattern_t| {
                        if pattern_t
                            .all_type_variables_iter()
                            .unique()
                            .all(|v| !contravariant_candidates.contains(&v))
                        {
                            possible_strongest_t(
                                pattern_t.clone(),
                                &t.subtype_relations,
                            )
                        } else {
                            pattern_t.clone()
                        }
                    })
                    .collect();
                PatternRestriction {
                    type_: Type::argument_tuple_from_arguments(pattern_ts),
                    ..pattern_restriction
                }
            })
            .collect();
        log::trace!("t{{13}} = {}", t);
        let mut updated = false;
        for r in &t.pattern_restrictions {
            for (p, _) in &r.pattern {
                for v in p.all_type_variables() {
                    if let (Some(we), Some(st)) = (
                        t.subtype_relations.possible_weakest(
                            map,
                            v,
                            &t.variable_requirements,
                            &t.pattern_restrictions,
                            &t.fn_apply_dummies,
                        ),
                        t.subtype_relations.possible_strongest(
                            map,
                            v,
                            &t.pattern_restrictions,
                            &t.variable_requirements,
                            &t.fn_apply_dummies,
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
                            updated = true;
                        }
                    }
                }
            }
        }
        if updated {
            return Ok((t, true));
        }
        log::trace!("t{{14}} = {}", t);
        for pattern_restriction in &t.pattern_restrictions {
            let ApplyTypeToPatternResult {
                subtype_relations: subtype,
                not_sure,
                updated,
            } = apply_type_to_pattern(pattern_restriction, true, env, map)?;
            debug_assert!(!not_sure);
            if updated {
                let mut t_normalized = t.clone();
                t_normalized.subtype_relations.extend(subtype);
                t_normalized = t_normalized.normalize(map)?;
                if t_normalized != t_before_simplify {
                    return Ok((t_normalized, true));
                }
            }
        }
        log::trace!("t{{15}} = {}", t);
        if !t.pattern_restrictions.is_empty() {
            t.pattern_restrictions.clear();
            return Ok((t, true));
        }
        log::trace!("t{{16}} = {}", t);
        if try_eq_sub(map, &mut t) {
            return Ok((t, true));
        }
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
    log::trace!("t{{18}} = {}", t);
    t = t.normalize(map)?;
    if t != t_before_simplify {
        return Ok((t, true));
    }
    let updated = t != t_before_simplify;
    if !updated {
        log::trace!("no update");
    }
    Ok((t, updated))
}

fn find_eq_types(subtype_rel: &SubtypeRelations) -> Vec<(TypeVariable, Type)> {
    use TypeUnit::*;
    let g = mk_graph(subtype_rel);
    let eq_types = tarjan_scc(&g);
    let mut r = Vec::new();
    for eqs in eq_types {
        if eqs.len() <= 1 {
            continue;
        }
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
        } else if eq_variable.is_empty() && eq_cons.len() == 2 {
            if let TypeMatchableRef::TypeLevelApply { f, a } =
                eq_cons[0].matchable_ref()
            {
                if let TypeMatchableRef::Variable(f) = f.matchable_ref() {
                    let (replaced_t, u) =
                        eq_cons[1].clone().replace_type_union_with_update_flag(
                            a,
                            &TypeUnit::Variable(TypeVariable::RecursiveIndex(
                                0,
                            )),
                            0,
                        );
                    if u {
                        r.push((f, TypeUnit::TypeLevelFn(replaced_t).into()));
                    }
                }
            }
        } else {
            for a in eq_variable {
                r.push((a, eq_cons[0].clone()));
            }
        }
    }
    r
}

type SubtypeRelationsVec = Vec<(Type, Type)>;

pub fn simplify_subtype_rel(
    sub: Type,
    sup: Type,
    already_considered_relations: Option<&mut BTreeSet<(Type, Type)>>,
) -> Result<SubtypeRelationsVec, NotSubtypeReason> {
    pub fn simplify_subtype_rel_rec(
        sub: Type,
        sup: Type,
        mut already_considered_relations: Option<&mut BTreeSet<(Type, Type)>>,
        loop_limit: i32,
    ) -> Result<SubtypeRelationsVec, NotSubtypeReason> {
        if loop_limit <= 0 {
            return Err(NotSubtypeReason::LoopLimit {
                left: sub,
                right: sup,
            });
        }
        let subsup = (sub, sup);
        let c = already_considered_relations
            .as_deref()
            .map(|a| a.contains(&subsup))
            .unwrap_or(false);
        let (sub, sup) = subsup;
        if c || sub == sup {
            return Ok(Vec::new());
        }
        let add_reason = |reason| NotSubtypeReason::NotSubtype {
            left: sub.clone(),
            right: sup.clone(),
            reasons: vec![reason],
        };
        let single_reason = NotSubtypeReason::NotSubtype {
            left: sub.clone(),
            right: sup.clone(),
            reasons: Vec::new(),
        };
        use ast_step2::types::Variance::*;
        use TypeMatchable::*;
        match (sub.clone().matchable(), sup.clone().matchable()) {
            (_, Any) => Ok(Vec::new()),
            (Tuple(a1, b1), Tuple(a2, b2)) => {
                let mut r = simplify_subtype_rel_rec(
                    a1,
                    a2,
                    already_considered_relations.as_deref_mut(),
                    loop_limit,
                )
                .map_err(add_reason)?;
                r.append(
                    &mut simplify_subtype_rel_rec(
                        b1,
                        b2,
                        already_considered_relations,
                        loop_limit,
                    )
                    .map_err(add_reason)?,
                );
                Ok(r)
            }
            (Const { id: id1, .. }, Const { id: id2, .. }) => {
                if id1 == id2 {
                    Ok(Vec::new())
                } else {
                    Err(single_reason)
                }
            }
            (Variance(Invariant, a), Variance(Invariant, b)) => {
                let r1 = simplify_subtype_rel_rec(
                    a.clone(),
                    b.clone(),
                    already_considered_relations.as_deref_mut(),
                    loop_limit,
                )
                .map_err(add_reason)?;
                let r2 = simplify_subtype_rel_rec(
                    b,
                    a,
                    already_considered_relations.as_deref_mut(),
                    loop_limit,
                )
                .map_err(add_reason)?;
                Ok(merge_vec(r1, r2))
            }
            (Variance(Contravariant, a), Variance(Contravariant, b)) => {
                let r = simplify_subtype_rel_rec(
                    b,
                    a,
                    already_considered_relations.as_deref_mut(),
                    loop_limit,
                )
                .map_err(add_reason)?;
                Ok(r)
            }
            (Tuple(..), Const { .. })
            | (Const { .. }, Tuple(..))
            | (Tuple { .. } | Const { .. }, Empty) => Err(single_reason),
            (_, Empty) if sub.is_wrapped_by_const() => Err(single_reason),
            (Any, _) if sup.is_wrapped_by_const() => Err(single_reason),
            (Union(cs), b) => Ok(cs
                .into_iter()
                .map(|c| {
                    simplify_subtype_rel_rec(
                        c.into(),
                        b.clone().into(),
                        already_considered_relations
                            .as_deref()
                            .cloned()
                            .as_mut(),
                        loop_limit,
                    )
                })
                .collect::<Result<Vec<_>, _>>()
                .map_err(add_reason)?
                .concat()),
            (Empty, _) => Ok(Vec::new()),
            (Variable(_), RecursiveAlias { body })
                if sub.clone().is_subtype_of(body.clone()) =>
            {
                Ok(Vec::new())
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
            (a, Union(u))
                if u.iter().any(|b| {
                    simplify_subtype_rel_rec(
                        Type::from(a.clone()),
                        b.clone().into(),
                        already_considered_relations.as_deref_mut(),
                        loop_limit,
                    ) == Ok(Vec::new())
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
                simplify_subtype_rel_rec(
                    TypeUnit::Variable(a).into(),
                    TypeUnit::RecursiveAlias { body: b }.into(),
                    already_considered_relations,
                    loop_limit,
                )
                .map_err(add_reason)
            }
            _ => {
                if sub.is_singleton() && sup.len() > 1 {
                    let mut new_sup = Type::default();
                    let mut reasons = Vec::new();
                    for b in sup.iter() {
                        let r = simplify_subtype_rel_rec(
                            sub.clone(),
                            b.clone().into(),
                            already_considered_relations
                                .as_deref_mut()
                                .cloned()
                                .as_mut(),
                            loop_limit,
                        );
                        match r {
                            Ok(r) => {
                                debug_assert!(!r.is_empty());
                                new_sup.insert(b.clone());
                            }
                            Err(e) => {
                                reasons.push(e);
                            }
                        }
                    }
                    if !reasons.is_empty() {
                        return simplify_subtype_rel_rec(
                            sub.clone(),
                            new_sup,
                            already_considered_relations,
                            loop_limit,
                        )
                        .map_err(|a| {
                            reasons.push(a);
                            NotSubtypeReason::NotSubtype {
                                left: sub,
                                right: sup,
                                reasons,
                            }
                        });
                    }
                }
                if sub.is_wrapped_by_const() && sup.len() > 1 {
                    let mut new_bs = Type::default();
                    let mut updated = false;
                    let mut reasons = Vec::new();
                    for b in sup.iter() {
                        let (b_out, b_in, reason) =
                            Type::from((*b).clone()).remove_disjoint_part(&sub);
                        new_bs.union_in_place(b_in.clone());
                        if !b_out.is_empty() {
                            updated = true;
                            if let Some(reason) = reason {
                                reasons.push(reason);
                            }
                        }
                    }
                    if updated {
                        return simplify_subtype_rel_rec(
                            sub.clone(),
                            new_bs,
                            already_considered_relations,
                            loop_limit,
                        )
                        .map_err(|a| {
                            reasons.push(a);
                            NotSubtypeReason::NotSubtype {
                                left: sub,
                                right: sup,
                                reasons,
                            }
                        });
                    }
                }
                if let Some(mut already_considered_relations) =
                    already_considered_relations.cloned()
                {
                    already_considered_relations
                        .insert((sub.clone(), sup.clone()));
                    let sub_is_non_polymorphic_recursive_fn_apply =
                        sub.is_non_polymorphic_recursive_fn_apply();
                    let sup_is_non_polymorphic_recursive_fn_apply =
                        sup.is_non_polymorphic_recursive_fn_apply();
                    if !matches!(
                        sup.matchable_ref(),
                        TypeMatchableRef::Variable(_)
                    ) && sub.is_recursive_fn_apply()
                    {
                        let (sub, _) = sub.clone().unwrap_recursive_fn_apply();
                        return simplify_subtype_rel_rec(
                            sub,
                            sup.clone(),
                            Some(&mut already_considered_relations),
                            if sub_is_non_polymorphic_recursive_fn_apply {
                                loop_limit - 1
                            } else {
                                loop_limit - 3
                            },
                        )
                        .map_err(add_reason);
                    } else if !matches!(
                        sub.matchable_ref(),
                        TypeMatchableRef::Variable(_)
                    ) && sup.is_recursive_fn_apply()
                    {
                        let (sup, _) = sup.clone().unwrap_recursive_fn_apply();
                        return simplify_subtype_rel_rec(
                            sub.clone(),
                            sup,
                            Some(&mut already_considered_relations),
                            if sup_is_non_polymorphic_recursive_fn_apply {
                                loop_limit - 1
                            } else {
                                loop_limit - 3
                            },
                        )
                        .map_err(add_reason);
                    }
                    use TypeMatchable::*;
                    match (sub.clone().matchable(), sup.clone().matchable()) {
                        (_, RecursiveAlias { body })
                            if sub.is_wrapped_by_const() =>
                        {
                            simplify_subtype_rel_rec(
                                sub.clone(),
                                unwrap_recursive_alias(body),
                                Some(&mut already_considered_relations),
                                loop_limit - 1,
                            )
                            .map_err(add_reason)
                        }
                        (
                            RecursiveAlias { body },
                            b @ (Tuple { .. }
                            | Union(_)
                            | RecursiveAlias { .. }
                            | Const { .. }
                            | TypeLevelApply { .. }),
                        ) => {
                            let b: Type = b.into();
                            simplify_subtype_rel_rec(
                                unwrap_recursive_alias(body),
                                b,
                                Some(&mut already_considered_relations),
                                loop_limit - 1,
                            )
                            .map_err(add_reason)
                        }
                        (_, Union(b)) if sub.is_wrapped_by_const() => {
                            let (sub_maybe_out, sub_in) = sub
                                .clone()
                                .split_slow(&sup, &mut Default::default());
                            if !sub_in.is_empty() {
                                simplify_subtype_rel_rec(
                                    sub_maybe_out,
                                    sup.clone(),
                                    Some(&mut already_considered_relations),
                                    loop_limit,
                                )
                                .map_err(add_reason)
                            } else if b.iter().any(|u| {
                                matches!(&**u, TypeUnit::RecursiveAlias { .. })
                            }) {
                                let b = b
                                    .into_iter()
                                    .flat_map(|u| match unwrap_or_clone(u) {
                                        TypeUnit::RecursiveAlias { body } => {
                                            unwrap_recursive_alias(body)
                                        }
                                        u => u.into(),
                                    })
                                    .collect();
                                simplify_subtype_rel_rec(
                                    sub.clone(),
                                    b,
                                    Some(&mut already_considered_relations),
                                    loop_limit - 1,
                                )
                                .map_err(add_reason)
                            } else {
                                match sub.clone().disjunctive() {
                                    Ok(a) => Ok(a
                                        .into_iter()
                                        .map(|a| {
                                            simplify_subtype_rel_rec(
                                                unwrap_or_clone(a).into(),
                                                b.clone(),
                                                Some(&mut already_considered_relations),
                                                loop_limit,
                                            )
                                        })
                                        .collect::<Result<Vec<_>, _>>()
                                        .map_err(add_reason)?
                                        .concat()),
                                    Err(a) => Ok(vec![(a.into(), b)]),
                                }
                            }
                        }
                        (_, _) => Ok(vec![(sub, sup)]),
                    }
                } else {
                    Ok(vec![(sub, sup)])
                }
            }
        }
    }
    simplify_subtype_rel_rec(sub, sup, already_considered_relations, LOOP_LIMIT)
}

thread_local! {
    static MEMO: RwLock<FxHashMap<Type, Type>> = RwLock::new(Default::default());
}

pub fn unwrap_recursive_alias(body: Type) -> Type {
    if let Some(t) = MEMO.with(|m| m.read().unwrap().get(&body).cloned()) {
        t
    } else {
        let result = body.clone().replace_num(
            TypeVariable::RecursiveIndex(0),
            &(TypeUnit::RecursiveAlias { body: body.clone() }).into(),
        );
        MEMO.with(|memo| memo.write().unwrap().insert(body, result.clone()));
        result
    }
}

fn possible_weakest(
    t: TypeVariable,
    subtype_relation: &SubtypeRelations,
    variable_requirements: &[VariableRequirement],
    pattern_restrictions: &PatternRestrictions,
    fn_apply_dummies: &BTreeMap<Type, (Type, RelOrigin)>,
    _map: &mut TypeVariableMap,
) -> Option<Type> {
    if variable_requirements
        .iter()
        .any(|req| req.required_type.contains_variable(t))
    {
        return None;
    }
    for (a, (v, _)) in fn_apply_dummies {
        if a.contains_variable(t) {
            return None;
        }
        debug_assert!(!v.contains_variable(t));
    }
    let mut up = FxHashSet::default();
    for pattern_restriction in pattern_restrictions {
        if pattern_restriction
            .pattern
            .iter()
            .any(|p| p.0.all_type_variables().contains(&t))
        {
            return None;
        }
    }
    for (sub, sup) in subtype_relation
        .0
        .iter()
        .map(|(a, b, _)| (a.clone(), b.clone()))
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
        let up = up.into_iter().next().unwrap();
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
    } else {
        let up = up.into_iter();
        let mut t = TypeUnit::Any.into();
        for up in up {
            t = type_intersection(t, up.clone())?;
        }
        Some(t)
    }
}

impl From<&PatternUnitForRestriction> for MatchOperand {
    fn from(p: &PatternUnitForRestriction) -> Self {
        match p {
            PatternUnitForRestriction::I64 => {
                MatchOperand::not_computed_from_type(
                    TypeUnit::Const {
                        id: TypeId::Intrinsic(IntrinsicType::I64),
                    }
                    .into(),
                )
            }
            PatternUnitForRestriction::Str => {
                MatchOperand::not_computed_from_type(
                    TypeUnit::Const {
                        id: TypeId::Intrinsic(IntrinsicType::String),
                    }
                    .into(),
                )
            }
            PatternUnitForRestriction::Binder(t, _decl_id) => {
                MatchOperand::not_computed_from_type(t.clone())
            }
            PatternUnitForRestriction::Const { id } => {
                MatchOperandUnit::Const(*id).into()
            }
            PatternUnitForRestriction::Tuple(a, b) => {
                MatchOperandUnit::Tuple((&**a).into(), (&**b).into()).into()
            }
            PatternUnitForRestriction::TypeRestriction(_, t) => {
                MatchOperand::not_computed_from_type(t.clone())
            }
            PatternUnitForRestriction::Apply(p) => (&**p).into(),
        }
    }
}

fn type_intersection(a: Type, b: Type) -> Option<Type> {
    use ast_step2::types::Variance::*;
    use TypeMatchable::*;
    match (a.matchable(), b.matchable()) {
        (Tuple(a1, b1), Tuple(a2, b2)) => Some(
            TypeUnit::Tuple(
                type_intersection(a1, a2)?,
                type_intersection(b1, b2)?,
            )
            .into(),
        ),
        (Any, a) | (a, Any) => Some(a.into()),
        (Variance(Contravariant, a), Variance(Contravariant, b)) => {
            Some(Variance(Contravariant, a.union(b)).into())
        }
        (a, b) => {
            let a: Type = a.into();
            let b: Type = b.into();
            let ab = simplify_subtype_rel(a.clone(), b.clone(), None);
            if let Ok(ab) = ab {
                if ab.is_empty() {
                    return Some(a);
                }
            }
            let ba = simplify_subtype_rel(b.clone(), a, None);
            if let Ok(ba) = ba {
                if ba.is_empty() {
                    return Some(b);
                }
            }
            None
        }
    }
}

fn possible_strongest(
    t: TypeVariable,
    subtype_relation: &SubtypeRelations,
    pattern_restrictions: &PatternRestrictions,
    variable_requirements: &[VariableRequirement],
    fn_apply_dummies: &BTreeMap<Type, (Type, RelOrigin)>,
) -> Option<Type> {
    let mut down = Vec::new();
    if variable_requirements
        .iter()
        .any(|req| req.required_type.contains_variable(t))
    {
        return None;
    }
    for (a, (v, _)) in fn_apply_dummies {
        if a.contains_variable(t) {
            return None;
        }
        debug_assert!(!v.contains_variable(t));
    }
    for (sub, sup, _) in subtype_relation {
        if sub.contravariant_type_variables().contains(&t) {
            return None;
        } else if *sup == TypeUnit::Variable(t).into() {
            down.push(sub);
        } else if sup.covariant_type_variables().contains(&t) {
            return None;
        }
    }
    for pattern_restriction in pattern_restrictions {
        if pattern_restriction
            .pattern
            .iter()
            .any(|p| p.0.all_type_variables().contains(&t))
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

fn possible_strongest_t(t: Type, subtype_relation: &SubtypeRelations) -> Type {
    let mut down_up: Type = TypeMatchable::Empty.into();
    let mut down_down: Type = TypeMatchable::Empty.into();
    for (a, b, _) in subtype_relation {
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

fn mk_contravariant_candidates<T: TypeConstructor>(
    t: &TypeWithEnv<T>,
) -> FxHashSet<TypeVariable> {
    let mut rst: Vec<TypeVariable> =
        t.constructor.contravariant_type_variables();
    for req in &t.variable_requirements {
        rst.append(&mut req.required_type.covariant_type_variables());
    }
    rst.into_iter().collect()
}

fn mk_covariant_candidates<T: TypeConstructor>(
    t: &TypeWithEnv<T>,
) -> FxHashSet<TypeVariable> {
    let mut rst: Vec<TypeVariable> = t.constructor.covariant_type_variables();
    for req in &t.variable_requirements {
        rst.append(&mut req.required_type.contravariant_type_variables());
    }
    rst.into_iter().collect()
}

impl<T> TypeWithEnv<T>
where
    T: TypeConstructor,
{
    pub fn normalize_variables(
        self,
        map: &mut TypeVariableMap,
    ) -> Result<Self, CompileError> {
        Ok(Self {
            constructor: self.constructor.map_type(|t| map.normalize_type(t)),
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
                .map(|(a, b, origin)| {
                    (map.normalize_type(a), map.normalize_type(b), origin)
                })
                .collect(),
            pattern_restrictions: self
                .pattern_restrictions
                .into_iter()
                .map(|p| PatternRestriction {
                    type_: map.normalize_type(p.type_),
                    pattern: p
                        .pattern
                        .into_iter()
                        .map(|(p, span)| (map.normalize_pattern_unit(p), span))
                        .collect(),
                    ..p
                })
                .collect(),
            already_considered_relations: self.already_considered_relations,
            fn_apply_dummies: self
                .fn_apply_dummies
                .into_iter()
                .map(|(a, (b, origin))| {
                    (map.normalize_type(a), (map.normalize_type(b), origin))
                })
                .collect(),
        })
    }

    pub fn normalize(
        mut self,
        map: &mut TypeVariableMap,
    ) -> Result<Self, CompileError> {
        self.subtype_relations = self
            .subtype_relations
            .normalize(map, &mut self.already_considered_relations)?;
        self = self.normalize_variables(map)?;
        Ok(self)
    }

    pub fn normalize_with_unwrapping(
        mut self,
        map: &mut TypeVariableMap,
    ) -> Result<Self, CompileError> {
        self.subtype_relations =
            self.subtype_relations.normalize_with_unwrapping(
                map,
                &mut self.already_considered_relations,
            )?;
        self = self.normalize_variables(map)?;
        Ok(self)
    }
}

#[derive(Debug, Default)]
pub struct Env {
    pub data_decls: FxHashMap<TypeId, DataDecl>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub decl_id: DeclId,
    pub type_parameter_len: usize,
    pub fields: Vec<Field>,
}

struct ApplyTypeToPatternResult {
    subtype_relations: SubtypeRelations,
    not_sure: bool,
    updated: bool,
}

fn apply_type_to_pattern(
    restriction: &PatternRestriction,
    last_application: bool,
    env: &mut Env,
    map: &mut TypeVariableMap,
) -> Result<ApplyTypeToPatternResult, CompileError> {
    log::trace!(
        "ts = ({})",
        restriction.type_.iter().map(|t| format!("{t}")).join(", ")
    );
    log::trace!(
        "pattern = {}",
        restriction
            .pattern
            .iter()
            .map(|p| format!("{}", p.0))
            .join(" | ")
    );
    let mut updated = false;
    let mut remained =
        disclose_type(restriction.type_.clone(), &mut env.data_decls);
    let decl_type_map_in_pattern: FxHashMap<DeclId, Type> = restriction
        .pattern
        .iter()
        .flat_map(|(p, _)| p.decl_type_map())
        .map(|(d, t)| (d, t.clone()))
        .collect();
    let mut subtype_rels = SubtypeRelations::default();
    let mut not_sure = false;
    let mut has_max_remained = true;
    for (p, p_span) in &restriction.pattern {
        let TypeDestructResult {
            remained: r,
            matched_type: _,
            bind_matched,
            is_matched,
            remained_is_max,
        } = destruct_type_by_pattern(
            remained,
            p,
            p_span.clone(),
            last_application,
            env,
        );
        let has_max_remained_old = has_max_remained;
        has_max_remained &= remained_is_max;
        let bind_matched: Vec<_> = bind_matched
            .into_iter()
            .fold(
                FxHashMap::default(),
                |mut m: FxHashMap<DeclId, (MatchOperand, Span)>,
                 (decl_id, t, span)| {
                    match m.entry(decl_id) {
                        std::collections::hash_map::Entry::Occupied(mut a) => {
                            let m = a.get_mut();
                            m.0.append(t);
                            m.1 = merge_span(&m.1, &span);
                        }
                        std::collections::hash_map::Entry::Vacant(a) => {
                            a.insert((t, span));
                        }
                    }
                    m
                },
            )
            .into_iter()
            .map(|(decl_id, (t, span))| {
                let mut sub = SubtypeRelations::default();
                let r = (
                    decl_id,
                    close_type(
                        t,
                        &env.data_decls,
                        map,
                        &mut sub,
                        span.clone(),
                    )?,
                    span,
                );
                let sub = sub.normalize(map, &mut Default::default()).unwrap();
                debug_assert!(sub.is_empty());
                Ok(r)
            })
            .try_collect()?;
        remained = r;
        let subtype_r: SubtypeRelations = bind_matched
            .iter()
            .map(|(decl_id, t, span)| {
                (
                    t.clone(),
                    decl_type_map_in_pattern[decl_id].clone(),
                    RelOrigin {
                        left: t.clone(),
                        right: decl_type_map_in_pattern[decl_id].clone(),
                        span: span.clone(),
                    },
                )
            })
            .collect();
        updated |= !subtype_r.is_empty();
        match is_matched {
            Trinary::NotSure => {
                subtype_rels.extend(subtype_r);
                not_sure = true;
            }
            Trinary::No => (),
            Trinary::Yes => {
                if has_max_remained_old {
                    updated |= !bind_matched.is_empty();
                    for (decl_id, t, span) in bind_matched {
                        map.insert_type(
                            &mut subtype_rels,
                            t.clone(),
                            decl_type_map_in_pattern[&decl_id].clone(),
                            Some(RelOrigin {
                                left: t,
                                right: decl_type_map_in_pattern[&decl_id]
                                    .clone(),
                                span,
                            }),
                        );
                    }
                } else {
                    subtype_rels.extend(subtype_r);
                }
            }
        }
    }
    // if !restriction.allow_inexhaustive && !remained.is_empty() && !not_sure {

    //     log::debug!("missing type = {}", remained);
    //     Err(CompileError::InexhaustiveMatch {
    //         description: format!(
    //             "missing pattern = {}",
    //             remained
    //                 .argument_vecs_from_argument_tuple()
    //                 .iter()
    //                 .format_with("|", |args, f| if args.len() == 1 {
    //                     f(&format_args!("{}", args[0]))
    //                 } else {
    //                     f(&format_args!("({})", args.iter().format(", ")))
    //                 })
    //         ),
    //         span: restriction.span.clone(),
    //     })
    // } else {
    Ok(ApplyTypeToPatternResult {
        subtype_relations: subtype_rels,
        not_sure,
        updated,
    })
    // }
}

fn simplify_dummies<T: TypeConstructor>(
    mut t: TypeWithEnv<T>,
    map: &mut TypeVariableMap,
) -> (TypeWithEnv<T>, bool) {
    let mut updated = false;
    t.fn_apply_dummies = t
        .fn_apply_dummies
        .into_iter()
        .flat_map(|(a, (b, origin))| match a.matchable() {
            TypeMatchable::TypeLevelApply { f, a }
                if !matches!(
                    b.matchable_ref(),
                    TypeMatchableRef::Variable(_)
                ) =>
            {
                match a.matchable() {
                    TypeMatchable::Variable(a)
                        if b.all_type_variables_iter()
                            .unique()
                            .collect_vec()
                            == vec![a] =>
                    {
                        let b = b.replace_num(
                            a,
                            &TypeUnit::Variable(TypeVariable::RecursiveIndex(
                                0,
                            ))
                            .into(),
                        );
                        map.insert_type(
                            &mut t.subtype_relations,
                            f,
                            TypeUnit::TypeLevelFn(b).into(),
                            Some(origin),
                        );
                        updated = true;
                        None
                    }
                    a => Some((
                        TypeUnit::TypeLevelApply { f, a: a.into() }.into(),
                        (b, origin),
                    )),
                }
            }
            a => {
                map.insert_type(
                    &mut t.subtype_relations,
                    a.into(),
                    b,
                    Some(origin),
                );
                updated = true;
                None
            }
        })
        .collect();
    (t, updated)
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Trinary {
    Yes,
    NotSure,
    No,
}

#[derive(Debug)]
struct TypeDestructResult {
    remained: MatchOperand,
    matched_type: MatchOperand,
    bind_matched: Vec<(DeclId, MatchOperand, Span)>,
    is_matched: Trinary,
    remained_is_max: bool,
}

fn destruct_type_by_pattern(
    t: MatchOperand,
    pattern: &PatternUnitForRestriction,
    pattern_span: Span,
    last_application: bool,
    env: &mut Env,
) -> TypeDestructResult {
    let mut remained = MatchOperand::default();
    let mut destructed = false;
    let mut not_sure = false;
    let mut remained_is_max = true;
    let mut matched = MatchOperand::default();
    let mut bind_matched = Vec::new();
    for tu in t {
        let TypeDestructResult {
            remained: r,
            matched_type: m,
            bind_matched: mut bm,
            is_matched,
            remained_is_max: is_max,
        } = destruct_type_unit_by_pattern(
            tu,
            pattern,
            pattern_span.clone(),
            last_application,
            env,
        );
        if last_application {
            debug_assert_ne!(is_matched, Trinary::NotSure);
        }
        remained_is_max &= is_max;
        remained.append(r);
        match is_matched {
            Trinary::NotSure => {
                matched.append(m);
                not_sure = true;
            }
            Trinary::No => (),
            Trinary::Yes => {
                matched.append(m);
                destructed = true;
                bind_matched.append(&mut bm);
            }
        }
    }
    if not_sure {
        TypeDestructResult {
            remained,
            matched_type: matched,
            bind_matched,
            is_matched: Trinary::NotSure,
            remained_is_max,
        }
    } else if destructed {
        TypeDestructResult {
            remained,
            matched_type: matched,
            bind_matched,
            is_matched: Trinary::Yes,
            remained_is_max,
        }
    } else {
        TypeDestructResult {
            remained,
            matched_type: Default::default(),
            bind_matched: Vec::new(),
            is_matched: Trinary::No,
            remained_is_max,
        }
    }
}

fn destruct_type_unit_by_pattern(
    t: MatchOperandUnit,
    pattern: &PatternUnitForRestriction,
    pattern_span: Span,
    last_application: bool,
    env: &mut Env,
) -> TypeDestructResult {
    match (t, pattern) {
        (
            t @ MatchOperandUnit::Const(TypeId::Intrinsic(IntrinsicType::I64)),
            PatternUnitForRestriction::I64,
        )
        | (
            t @ MatchOperandUnit::Const(TypeId::Intrinsic(
                IntrinsicType::String,
            )),
            PatternUnitForRestriction::Str,
        ) => TypeDestructResult {
            remained: t.into(),
            matched_type: MatchOperand::default(),
            bind_matched: Vec::new(),
            is_matched: Trinary::Yes,
            remained_is_max: true,
        },
        (t, PatternUnitForRestriction::Apply(p)) => {
            let r = destruct_type_unit_by_pattern(
                t.clone(),
                p,
                pattern_span,
                last_application,
                env,
            );
            TypeDestructResult {
                remained: t.into(),
                ..r
            }
        }
        (t, PatternUnitForRestriction::Binder(_, decl_id)) => {
            let t = MatchOperand::from(t);
            TypeDestructResult {
                remained: MatchOperand::default(),
                matched_type: t.clone(),
                bind_matched: vec![(*decl_id, t, pattern_span)],
                is_matched: Trinary::Yes,
                remained_is_max: true,
            }
        }
        (t, PatternUnitForRestriction::TypeRestriction(p, annotation)) => {
            let (out, maybe_in) =
                MatchOperand::from(t).remove_disjoint_part(annotation, env);
            let (not_sure, in_) = maybe_in.split_slow(annotation);
            let not_sure_is_empty = not_sure.is_empty();
            let mut r = destruct_type_by_pattern(
                in_.union(not_sure),
                p,
                pattern_span,
                last_application,
                env,
            );
            r.remained.append(out);
            if r.is_matched == Trinary::Yes
                && !not_sure_is_empty
                && !last_application
            {
                r.is_matched = Trinary::NotSure;
            }
            r
        }
        (MatchOperandUnit::NotComputed(t), _) => destruct_type_by_pattern(
            disclose_type_unit(t, &mut env.data_decls),
            pattern,
            pattern_span,
            last_application,
            env,
        ),
        (
            MatchOperandUnit::Const(id1),
            PatternUnitForRestriction::Const { id: id2, .. },
        ) if id1 == *id2 => TypeDestructResult {
            remained: MatchOperand::default(),
            matched_type: MatchOperandUnit::Const(id1).into(),
            bind_matched: Vec::new(),
            is_matched: Trinary::Yes,
            remained_is_max: true,
        },
        (
            MatchOperandUnit::Tuple(a1, a2),
            PatternUnitForRestriction::Tuple(p1, p2),
        ) => {
            let mut r1 = destruct_type_by_pattern(
                a1,
                p1,
                pattern_span.clone(),
                last_application,
                env,
            );
            if r1.is_matched == Trinary::No {
                TypeDestructResult {
                    remained: MatchOperand::tuple(r1.remained, a2),
                    matched_type: Default::default(),
                    bind_matched: Vec::new(),
                    is_matched: Trinary::No,
                    remained_is_max: true,
                }
            } else {
                let r2 = destruct_type_by_pattern(
                    a2,
                    p2,
                    pattern_span,
                    last_application,
                    env,
                );
                if r2.is_matched == Trinary::No {
                    r1.remained.append(r1.matched_type);
                    TypeDestructResult {
                        remained: MatchOperand::tuple(r1.remained, r2.remained),
                        matched_type: Default::default(),
                        bind_matched: Vec::new(),
                        is_matched: Trinary::No,
                        remained_is_max: true,
                    }
                } else {
                    let not_sure = r1.is_matched == Trinary::NotSure
                        || r2.is_matched == Trinary::NotSure;
                    TypeDestructResult {
                        remained: MatchOperand::default()
                            .union(MatchOperand::tuple(
                                r1.remained.clone(),
                                r2.remained.clone(),
                            ))
                            .union(MatchOperand::tuple(
                                r1.remained.clone(),
                                r2.matched_type.clone(),
                            ))
                            .union(MatchOperand::tuple(
                                r1.matched_type.clone(),
                                r2.remained,
                            )),
                        matched_type: MatchOperand::tuple(
                            r1.matched_type,
                            r2.matched_type,
                        ),
                        bind_matched: merge_vec(
                            r1.bind_matched,
                            r2.bind_matched,
                        ),
                        is_matched: if not_sure {
                            Trinary::NotSure
                        } else {
                            Trinary::Yes
                        },
                        remained_is_max: r1.remained_is_max
                            && r2.remained_is_max,
                    }
                }
            }
        }
        (t, PatternUnitForRestriction::Tuple(a, b))
            if matches!(
                **a,
                PatternUnitForRestriction::I64 | PatternUnitForRestriction::Str
            ) && matches!(
                **b,
                PatternUnitForRestriction::Const {
                    id: TypeId::Intrinsic(IntrinsicType::Unit)
                }
            ) =>
        {
            TypeDestructResult {
                remained: t.into(),
                matched_type: MatchOperand::default(),
                bind_matched: Vec::new(),
                is_matched: if last_application {
                    Trinary::Yes
                } else {
                    Trinary::NotSure
                },
                remained_is_max: true,
            }
        }
        (MatchOperandUnit::Any, PatternUnitForRestriction::Const { .. }) => {
            TypeDestructResult {
                remained: MatchOperandUnit::Any.into(),
                matched_type: Default::default(),
                bind_matched: Vec::new(),
                is_matched: Trinary::Yes,
                remained_is_max: true,
            }
        }
        (MatchOperandUnit::Any, PatternUnitForRestriction::Tuple(a, b)) => {
            let r1 = destruct_type_by_pattern(
                MatchOperandUnit::Any.into(),
                a,
                pattern_span.clone(),
                last_application,
                env,
            );
            let r2 = destruct_type_by_pattern(
                MatchOperandUnit::Any.into(),
                b,
                pattern_span,
                last_application,
                env,
            );
            TypeDestructResult {
                remained: MatchOperandUnit::Any.into(),
                matched_type: Default::default(),
                bind_matched: merge_vec(r1.bind_matched, r2.bind_matched),
                is_matched: Trinary::Yes,
                remained_is_max: true,
            }
        }
        (
            v @ (MatchOperandUnit::Variable(_)
            | MatchOperandUnit::Const(TypeId::FixedVariable(_))),
            PatternUnitForRestriction::Tuple(a, b),
        ) if last_application => {
            let r1 = destruct_type_by_pattern(
                MatchOperandUnit::Any.into(),
                a,
                pattern_span.clone(),
                last_application,
                env,
            );
            let r2 = destruct_type_by_pattern(
                MatchOperandUnit::Any.into(),
                b,
                pattern_span,
                last_application,
                env,
            );
            TypeDestructResult {
                remained: v.into(),
                matched_type: Default::default(),
                bind_matched: merge_vec(r1.bind_matched, r2.bind_matched),
                is_matched: Trinary::Yes,
                remained_is_max: true,
            }
        }
        (
            v @ (MatchOperandUnit::Variable(_)
            | MatchOperandUnit::Const(TypeId::FixedVariable(_))),
            PatternUnitForRestriction::I64
            | PatternUnitForRestriction::Str
            | PatternUnitForRestriction::Const { .. }
            | PatternUnitForRestriction::Tuple(_, _),
        ) if last_application => TypeDestructResult {
            remained: v.into(),
            matched_type: Default::default(),
            bind_matched: Vec::new(),
            is_matched: Trinary::Yes,
            remained_is_max: true,
        },
        (
            v @ MatchOperandUnit::Variable(_),
            PatternUnitForRestriction::I64
            | PatternUnitForRestriction::Str
            | PatternUnitForRestriction::Const { .. }
            | PatternUnitForRestriction::Tuple(_, _),
        ) => TypeDestructResult {
            remained: Default::default(),
            matched_type: v.into(),
            bind_matched: Vec::new(),
            is_matched: Trinary::NotSure,
            remained_is_max: false,
        },
        (
            remained @ (MatchOperandUnit::Tuple(_, _)
            | MatchOperandUnit::Const(_)
            | MatchOperandUnit::Any),
            PatternUnitForRestriction::Tuple(_, _)
            | PatternUnitForRestriction::I64
            | PatternUnitForRestriction::Str
            | PatternUnitForRestriction::Const { .. },
        ) => TypeDestructResult {
            remained: remained.into(),
            matched_type: Default::default(),
            bind_matched: Vec::new(),
            is_matched: Trinary::No,
            remained_is_max: true,
        },
    }
}

fn mk_graph(subtype_relations: &SubtypeRelations) -> DiGraphMap<&Type, ()> {
    let mut g = DiGraphMap::new();
    for (a, b, _) in subtype_relations {
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

fn try_eq_sub<T: TypeConstructor>(
    map: &mut TypeVariableMap,
    t: &mut TypeWithEnv<T>,
) -> bool {
    if t.subtype_relations.is_empty() {
        return false;
    }
    let mut m = TypeVariableMap::default();
    let mut subtype = SubtypeRelations::default();
    for (a, b, origin) in &t.subtype_relations {
        m.insert_type_without_log(
            &mut subtype,
            a.clone(),
            b.clone(),
            Some(origin.clone()),
        );
    }
    match subtype
        .normalize_subtype_rel_with_unwrapping(map, &mut BTreeSet::default())
    {
        Ok(subtype) if subtype.is_empty() => {
            for (v, k) in m.0 {
                map.insert(&mut t.subtype_relations, v, k);
            }
            t.subtype_relations = SubtypeRelations::default();
            true
        }
        Ok(_) => false,
        _ => false,
    }
}

impl<T: TypeConstructor> TypeWithEnv<T> {
    fn type_variables_in_env_except_for_subtype_rel(
        &self,
    ) -> FxHashSet<TypeVariable> {
        self.constructor
            .all_type_variables_iter()
            .chain(
                self.variable_requirements.iter().flat_map(|req| {
                    req.required_type.all_type_variables_iter()
                }),
            )
            .chain(
                self.fn_apply_dummies
                    .values()
                    .flat_map(|(t, _)| t.all_type_variables_iter()),
            )
            .collect()
    }
}

impl Display for VariableRequirement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "  {:<3}  ?{:?} : {} , env = ",
            self.ident, self.name, self.required_type
        )?;
        for (name, _, _) in &self.local_env {
            write!(f, "{name}, ")?;
        }
        write!(f, "req count = {}", self.req_recursion_count)?;
        Ok(())
    }
}

impl<T: TypeConstructor> Display for ast_step2::TypeWithEnv<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{} forall {{", self.constructor)?;
        for (a, b, origin) in &self.subtype_relations {
            if a != &origin.left || b != &origin.right {
                writeln!(
                    f,
                    "    {} < {} ({:?}) (from {} < {}),",
                    a, b, origin.span, origin.left, origin.right
                )?;
            } else {
                writeln!(f, "    {} < {} ({:?}),", a, b, origin.span)?;
            }
        }
        for req in &self.variable_requirements {
            writeln!(f, "{req},")?;
        }
        for p in &self.pattern_restrictions {
            writeln!(f, "    {},", p)?;
        }
        if !self.already_considered_relations.is_empty() {
            writeln!(f, "already_considered_relations:")?;
            write!(
                f,
                "{}",
                self.already_considered_relations
                    .iter()
                    .format_with("\n", |(a, b), f| f(&format_args!(
                        "{a} < {b}"
                    )))
            )?;
        }
        if !self.fn_apply_dummies.is_empty() {
            writeln!(f, "fn_apply_dummies:")?;
            write!(
                f,
                "{}",
                self.fn_apply_dummies.iter().format_with(
                    "",
                    |(a, (b, origin)), f| f(&format_args!(
                        "{} = {} ({:?}) (from {} = {}),\n",
                        a, b, origin.span, origin.left, origin.right
                    ))
                )
            )?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl Display for SubtypeRelations {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (a, b, origin) in self {
            if a != &origin.left || b != &origin.right {
                writeln!(
                    f,
                    "    {} < {} ({:?}) (from {} < {}),",
                    a, b, origin.span, origin.left, origin.right
                )?;
            } else {
                writeln!(f, "    {} < {} ({:?}),", a, b, origin.span)?;
            }
        }
        Ok(())
    }
}

impl Display for TypeVariableMap {
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
    use crate::ast_step1::decl_id::DeclId;
    use crate::ast_step1::name_id::Path;
    use crate::ast_step2::types::{Type, TypeUnit, TypeVariable};
    use crate::ast_step2::{
        PatternRestriction, PatternUnitForRestriction, RelOrigin, TypeId,
        TypeWithEnv,
    };
    use crate::ast_step3::type_check::simplify::{
        apply_type_to_pattern, simplify_subtype_rel, simplify_type, Env,
        TypeVariableMap,
    };
    use crate::ast_step3::type_check::RemovedParameters;
    use crate::{ast_step1, ast_step2, combine_with_prelude, Imports};
    use doki::intrinsics::IntrinsicType;
    use itertools::Itertools;
    use stripmargin::StripMargin;

    #[test]
    fn simplify1() {
        let src = r#"
        |main : () -> () =
        |    | () => ()
        |test : I64 /\ I64 ->
        |((I64 /\ I64 | I64 /\ t1 | t2 /\ I64 | t3 /\ t4) -> I64 | String)
        |-> I64 | String forall {t1, t2, t3, t4}
        |= ()
        |dot : a -> (a -> b) -> b forall {a, b} = ()
        |"#
        .strip_margin();
        let ast = combine_with_prelude(parser::parse(&src));
        let mut imports = Imports::default();
        let (ast, mut token_map) =
            ast_step1::Ast::from(&ast, &mut imports).unwrap();
        let ast =
            ast_step2::Ast::from(ast, &mut token_map, &mut imports).unwrap();
        let RemovedParameters {
            fixed_type: req_t, ..
        } = ast
            .variable_decl
            .iter()
            .find(|d| d.name == Path::from_str(Path::pkg_root(), "test"))
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .unfixed
            .remove_parameters();
        let RemovedParameters {
            fixed_type: dot, ..
        } = ast
            .variable_decl
            .iter()
            .find(|d| d.name == Path::from_str(Path::pkg_root(), "dot"))
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .unfixed
            .remove_parameters();
        let t = TypeWithEnv {
            constructor: Type::intrinsic_from_str("I64").arrow(
                Type::intrinsic_from_str("I64")
                    .union(Type::intrinsic_from_str("String")),
            ),
            subtype_relations: vec![(
                dot.clone(),
                req_t.clone(),
                RelOrigin {
                    left: dot,
                    right: req_t,
                    span: 0..0,
                },
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        };
        let mut map: TypeVariableMap = Default::default();
        let st = simplify_type(&mut map, t, &mut Env::default()).unwrap();
        assert_eq!(format!("{st}"), "-I64 -> [{:String | :I64}] forall {\n}");
    }

    #[test]
    fn simplify3() {
        let src = r#"
        |main : () -> () =
        |    | () => ()
        |test1 : (False /\ False /\ False) = ()
        |test2 : (True /\ a /\ b) |
        |    (c /\ True /\ d) |
        |    (e /\ f /\ True) forall {a,b,c,d,e,f} = ()
        |"#
        .strip_margin();
        let ast = combine_with_prelude(parser::parse(&src));
        let mut imports = Imports::default();
        let (ast, mut token_map) =
            ast_step1::Ast::from(&ast, &mut imports).unwrap();
        let ast =
            ast_step2::Ast::from(ast, &mut token_map, &mut imports).unwrap();
        let t1 = ast
            .variable_decl
            .iter()
            .find(|d| d.name == Path::from_str(Path::pkg_root(), "test1"))
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .unfixed;
        let RemovedParameters { fixed_type: t2, .. } = ast
            .variable_decl
            .iter()
            .find(|d| d.name == Path::from_str(Path::pkg_root(), "test2"))
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .unfixed
            .remove_parameters();
        let t = simplify_subtype_rel(t1, t2, None);
        assert!(t.is_err());
    }

    #[test]
    fn apply_type_to_pattern_0() {
        let v1 = TypeVariable::new();
        let t1 =
            Type::intrinsic_from_str("I64").union_unit(TypeUnit::Variable(v1));
        let v2 = TypeVariable::new();
        let mut map = Default::default();
        let str_pattern = PatternUnitForRestriction::Tuple(
            Box::new(PatternUnitForRestriction::Str),
            Box::new(PatternUnitForRestriction::Const {
                id: TypeId::Intrinsic(IntrinsicType::Unit),
            }),
        );
        let r = apply_type_to_pattern(
            &PatternRestriction {
                type_: Type::argument_tuple_from_arguments(vec![t1]),
                pattern: vec![
                    PatternUnitForRestriction::argument_tuple_from_arguments(
                        vec![(str_pattern, 0..0)],
                    ),
                    PatternUnitForRestriction::argument_tuple_from_arguments(
                        vec![(
                            PatternUnitForRestriction::Binder(
                                TypeUnit::Variable(v2).into(),
                                DeclId::new(),
                            ),
                            0..0,
                        )],
                    ),
                ]
                .into_iter()
                .map(|(a, s)| (a, s.unwrap()))
                .collect_vec(),
                span: 0..0,
                allow_inexhaustive: false,
            },
            true,
            &mut Env::default(),
            &mut map,
        )
        .unwrap();
        assert!(r.subtype_relations.is_empty());
        assert_eq!(map.find(v2).to_string(), format!("{{{v1} | I64}}"));
    }

    #[test]
    fn apply_type_to_pattern_1() {
        let v1 = TypeVariable::new();
        let t1 = Type::intrinsic_from_str("I64");
        let v2 = TypeVariable::new();
        let v3 = TypeVariable::new();
        let mut map = Default::default();
        let mut env = Env::default();
        let i64_pattern = PatternUnitForRestriction::Tuple(
            Box::new(PatternUnitForRestriction::I64),
            Box::new(PatternUnitForRestriction::Const {
                id: TypeId::Intrinsic(IntrinsicType::Unit),
            }),
        );
        let r =
            apply_type_to_pattern(
                &PatternRestriction {
                    type_: Type::argument_tuple_from_arguments(vec![
                        t1.clone(),
                        t1,
                    ]),
                    pattern: vec![
                    PatternUnitForRestriction::argument_tuple_from_arguments(
                        vec![(i64_pattern, 0..0),(
                            PatternUnitForRestriction::Binder(
                                TypeUnit::Variable(v1).into(),
                                DeclId::new(),
                            ),
                            0..0,
                        )],
                    ),
                    PatternUnitForRestriction::argument_tuple_from_arguments(
                        vec![(
                            PatternUnitForRestriction::Binder(
                                TypeUnit::Variable(v2).into(),
                                DeclId::new(),
                            ),
                            0..0,
                        ),(
                            PatternUnitForRestriction::Binder(
                                TypeUnit::Variable(v3).into(),
                                DeclId::new(),
                            ),
                            0..0,
                        )],
                    ),
                ]
                    .into_iter()
                    .map(|(a, s)| (a, s.unwrap()))
                    .collect_vec(),
                    span: 0..0,
                    allow_inexhaustive: false,
                },
                true,
                &mut env,
                &mut map,
            )
            .unwrap();
        assert!(r.subtype_relations.is_empty());
        assert!(!r.not_sure);
        assert_eq!(map.find(v1).to_string(), format!("I64"));
    }
}
