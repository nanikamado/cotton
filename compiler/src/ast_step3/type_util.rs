use crate::ast_step2::types::{
    merge_vec, unwrap_or_clone, Type, TypeConstructor, TypeMatchable,
    TypeMatchableRef, TypeUnit, TypeVariable,
};
use crate::ast_step2::{RelOrigin, TypeId, TypeWithEnv};
use crate::ast_step3::type_check::unwrap_recursive_alias;
use crate::errors::NotSubtypeReason;
use crate::intrinsics::{IntrinsicType, INTRINSIC_TYPES};
use std::collections::BTreeMap;
use std::rc::Rc;

impl TypeUnit {
    pub fn all_type_variables(&self) -> Vec<TypeVariable> {
        match self {
            TypeUnit::Variable(i) => std::iter::once(*i).collect(),
            TypeUnit::RecursiveAlias { body } => {
                let s = body.all_type_variables_vec();
                s.into_iter().filter(|d| !d.is_recursive_index()).collect()
            }
            TypeUnit::Const { .. } | TypeUnit::Any => Vec::new(),
            TypeUnit::Tuple(a, b) => a
                .all_type_variables_vec()
                .into_iter()
                .chain(b.all_type_variables_vec().into_iter())
                .collect(),
            TypeUnit::TypeLevelFn(f) => f
                .all_type_variables_vec()
                .into_iter()
                .filter(|d| !d.is_recursive_index())
                .collect(),
            TypeUnit::TypeLevelApply { f, a } => merge_vec(
                f.all_type_variables_vec(),
                a.all_type_variables_vec(),
            ),
            TypeUnit::Restrictions { t, .. } | TypeUnit::Variance(_, t) => {
                t.all_type_variables_vec()
            }
        }
    }

    pub fn replace_num_with_update_flag(
        self,
        from: TypeVariable,
        to: &Type,
        recursive_alias_depth: usize,
    ) -> (Type, bool) {
        match self {
            Self::Variable(n) => {
                if n == from
                    .increment_recursive_index(recursive_alias_depth as i32)
                {
                    (
                        to.clone().increment_recursive_index(
                            0,
                            recursive_alias_depth as i32,
                        ),
                        true,
                    )
                } else {
                    (Self::Variable(n).into(), false)
                }
            }
            Self::RecursiveAlias { body } => {
                let (body, updated) = body.replace_num_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth + 1,
                );
                let t = (Self::RecursiveAlias { body }).into();
                (t, updated)
            }
            a @ (Self::Const { .. } | Self::Any) => (a.into(), false),
            Self::Tuple(a, b) => {
                let (a, updated1) = a.replace_num_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                let (b, updated2) = b.replace_num_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                (Self::Tuple(a, b).into(), updated1 || updated2)
            }
            Self::TypeLevelFn(f) => {
                let (f, u) = f.replace_num_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth + 1,
                );
                (Self::TypeLevelFn(f).into(), u)
            }
            Self::TypeLevelApply { f, a } => {
                let (f, updated1) = f.replace_num_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                let (a, updated2) = a.replace_num_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                (f.type_level_function_apply(a), updated1 || updated2)
            }
            Self::Restrictions {
                t,
                variable_requirements,
                subtype_relations,
            } => {
                let mut u = false;
                let (t, u_) = t.replace_num_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                u |= u_;
                let variable_requirements = variable_requirements
                    .into_iter()
                    .map(|(name, mut r)| {
                        let (t, u_) = r.replace_num_with_update_flag(
                            from,
                            to,
                            recursive_alias_depth,
                        );
                        u |= u_;
                        r = t;
                        (name, r)
                    })
                    .collect();
                let subtype_relations = subtype_relations
                    .into_iter()
                    .map(|(a, b)| {
                        let (a, u_) = a.replace_num_with_update_flag(
                            from,
                            to,
                            recursive_alias_depth,
                        );
                        u |= u_;
                        let (b, u_) = b.replace_num_with_update_flag(
                            from,
                            to,
                            recursive_alias_depth,
                        );
                        u |= u_;
                        (a, b)
                    })
                    .collect();
                (
                    Self::Restrictions {
                        t,
                        variable_requirements,
                        subtype_relations,
                    }
                    .into(),
                    u,
                )
            }
            Self::Variance(v, t) => {
                let (t, u) = t.replace_num_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                (Self::Variance(v, t).into(), u)
            }
        }
    }

    pub fn replace_num(self, from: TypeVariable, to: &Type) -> Type {
        self.replace_num_with_update_flag(from, to, 0).0
    }

    pub fn replace_type(self, from: &TypeUnit, to: &TypeUnit) -> Self {
        match self {
            t if t == *from => to.clone(),
            Self::RecursiveAlias { body } => Self::RecursiveAlias {
                body: body.replace_type(from, to),
            },
            Self::Tuple(a, b) => {
                Self::Tuple(a.replace_type(from, to), b.replace_type(from, to))
            }
            t => t,
        }
    }

    pub fn replace_type_union(self, from: &Type, to: &TypeUnit) -> Self {
        match self {
            Self::RecursiveAlias { body } => Self::RecursiveAlias {
                body: body.replace_type_union(from, to),
            },
            Self::Tuple(a, b) => Self::Tuple(
                a.replace_type_union(from, to),
                b.replace_type_union(from, to),
            ),
            t => t,
        }
    }

    pub fn matchable_ref(&self) -> TypeMatchableRef {
        use TypeMatchableRef::*;
        match self {
            TypeUnit::Variable(v) => Variable(*v),
            TypeUnit::RecursiveAlias { body } => RecursiveAlias { body },
            TypeUnit::Const { id } => Const { id: *id },
            TypeUnit::Tuple(a, b) => Tuple(a, b),
            TypeUnit::TypeLevelFn(f) => TypeLevelFn(f),
            TypeUnit::TypeLevelApply { f, a } => TypeLevelApply { f, a },
            TypeUnit::Restrictions {
                t,
                variable_requirements,
                subtype_relations,
            } => Restrictions {
                t,
                variable_requirements,
                subtype_relations,
            },
            TypeUnit::Any => Any,
            TypeUnit::Variance(v, t) => Variance(*v, t),
        }
    }

    pub fn replace_type_union_with_update_flag(
        self,
        from: &Type,
        to: &TypeUnit,
        recursive_alias_depth: usize,
    ) -> (Self, bool) {
        if self.matchable_ref() == from.matchable_ref() {
            return (
                to.clone()
                    .increment_recursive_index(0, recursive_alias_depth as i32),
                true,
            );
        }
        match self {
            Self::RecursiveAlias { body } => {
                let (body, updated) = body.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth + 1,
                );
                (Self::RecursiveAlias { body }, updated)
            }
            Self::Tuple(args, rtn) => {
                let (a, u1) = args.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                let (b, u2) = rtn.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                (Self::Tuple(a, b), u1 || u2)
            }
            t @ (Self::Variable(_) | Self::Const { .. } | Self::Any) => {
                (t, false)
            }
            Self::TypeLevelFn(f) => {
                let (f, u) = f.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth + 1,
                );
                (Self::TypeLevelFn(f), u)
            }
            Self::TypeLevelApply { f, a } => {
                let (f, u1) = f.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                let (a, u2) = a.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                (Self::TypeLevelApply { f, a }, u1 || u2)
            }
            Self::Restrictions {
                t,
                variable_requirements,
                subtype_relations,
            } => {
                let mut u = false;
                let (t, u_) = t.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                u |= u_;
                let variable_requirements = variable_requirements
                    .into_iter()
                    .map(|(name, mut r)| {
                        let (t, u_) = r.replace_type_union_with_update_flag(
                            from,
                            to,
                            recursive_alias_depth,
                        );
                        u |= u_;
                        r = t;
                        (name, r)
                    })
                    .collect();
                (
                    Self::Restrictions {
                        t,
                        variable_requirements,
                        subtype_relations,
                    },
                    u,
                )
            }
            Self::Variance(v, t) => {
                let (t, u) = t.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                (Self::Variance(v, t), u)
            }
        }
    }

    pub fn contains_variable(&self, variable_num: TypeVariable) -> bool {
        match self {
            Self::Variable(n) => *n == variable_num,
            Self::RecursiveAlias { body } => body
                .contains_variable(variable_num.increment_recursive_index(1)),
            Self::Const { .. } | Self::Any => false,
            Self::Tuple(a, b) => {
                a.contains_variable(variable_num)
                    || b.contains_variable(variable_num)
            }
            Self::TypeLevelFn(f) => {
                f.contains_variable(variable_num.increment_recursive_index(1))
            }
            Self::TypeLevelApply { f, a } => {
                f.contains_variable(variable_num)
                    || a.contains_variable(variable_num)
            }
            Self::Restrictions { t, .. } | Self::Variance(_, t) => {
                t.contains_variable(variable_num)
            }
        }
    }

    fn split(self, other: &Self) -> (Type, Type) {
        match (self, other) {
            (TypeUnit::Tuple(a1, a2), TypeUnit::Tuple(b1, b2)) => {
                let (a1_out, a1_in) = a1.split(b1);
                let (a2_out, a2_in) = a2.split(b2);
                (
                    Type::default()
                        .union_unit(TypeUnit::Tuple(
                            a1_out,
                            a2_out.clone().union(a2_in.clone()),
                        ))
                        .union_unit(TypeUnit::Tuple(a1_in.clone(), a2_out)),
                    TypeUnit::Tuple(a1_in, a2_in).into(),
                )
            }
            (a, TypeUnit::Any) => (Type::default(), a.into()),
            (TypeUnit::Any, a) => (TypeUnit::Any.into(), a.clone().into()),
            (a, b) if a == *b => (Type::default(), a.into()),
            (t, _) => (t.into(), Type::default()),
        }
    }

    pub fn split_slow(
        self,
        other: &Self,
        visited: &mut BTreeMap<(TypeUnit, TypeUnit), Option<(Type, Type)>>,
    ) -> (Type, Type) {
        if let Some(a) = visited.get(&(self.clone(), other.clone())) {
            return a.clone().unwrap();
        }
        visited.insert((self.clone(), other.clone()), None);
        use crate::ast_step2::types::Variance::*;
        let r = match (self.clone(), other.clone()) {
            (TypeUnit::Tuple(a1, a2), TypeUnit::Tuple(b1, b2)) => {
                let (a1_out, a1_in) = a1.split_slow(&b1, visited);
                let (a2_out, a2_in) = a2.split_slow(&b2, visited);
                (
                    Type::default()
                        .union_unit(TypeUnit::Tuple(
                            a1_out,
                            a2_out.clone().union(a2_in.clone()),
                        ))
                        .union_unit(TypeUnit::Tuple(a1_in.clone(), a2_out)),
                    TypeUnit::Tuple(a1_in, a2_in).into(),
                )
            }
            (a, TypeUnit::Any) => (Type::default(), a.into()),
            (
                TypeUnit::Variance(Contravariant, a),
                TypeUnit::Variance(Contravariant, b),
            ) => {
                if b.is_subtype_of(a.clone()) {
                    (
                        Type::default(),
                        TypeUnit::Variance(Contravariant, a).into(),
                    )
                } else {
                    (
                        TypeUnit::Variance(Contravariant, a).into(),
                        Type::default(),
                    )
                }
            }
            (a, b) if a == b => (Type::default(), a.into()),
            (t, _)
                if t.is_non_polymorphic_recursive_fn_apply()
                    && other.is_wrapped_by_const() =>
            {
                t.unwrap_recursive_fn_apply()
                    .0
                    .split_unit_slow(other, visited)
            }
            (t, _) => (t.into(), Type::default()),
        };
        visited.insert((self, other.clone()), Some(r.clone()));
        r
    }

    pub fn remove_disjoint_part(
        self,
        other: &Self,
    ) -> (Type, Type, Option<NotSubtypeReason>) {
        match (self, other) {
            (
                t @ (TypeUnit::Variable(_)
                | TypeUnit::RecursiveAlias { .. }
                | TypeUnit::Any
                | TypeUnit::Variance(_, _)),
                _,
            )
            | (
                t,
                TypeUnit::Variable(_)
                | TypeUnit::RecursiveAlias { .. }
                | TypeUnit::Any
                | TypeUnit::Variance(_, _),
            ) => (Type::default(), t.into(), None),
            (
                TypeUnit::TypeLevelApply { f: t_f, a: t_a },
                TypeUnit::TypeLevelApply { f: other_f, .. },
            ) => match (t_f.matchable_ref(), other_f.matchable_ref()) {
                (
                    TypeMatchableRef::Const { id: t_id },
                    TypeMatchableRef::Const { id: other_id },
                ) if t_id != other_id => {
                    let t: Type =
                        TypeUnit::TypeLevelApply { f: t_f, a: t_a }.into();
                    (
                        t.clone(),
                        Type::default(),
                        Some(NotSubtypeReason::Disjoint {
                            left: other.clone().into(),
                            right: t,
                            reasons: Vec::new(),
                        }),
                    )
                }
                _ => (
                    Type::default(),
                    TypeUnit::TypeLevelApply { f: t_f, a: t_a }.into(),
                    None,
                ),
            },
            (t, TypeUnit::TypeLevelApply { f, .. })
                if matches!(
                    f.matchable_ref(),
                    TypeMatchableRef::Const { .. }
                ) && t.is_wrapped_by_const() =>
            {
                let t: Type = t.into();
                (
                    t.clone(),
                    Type::default(),
                    Some(NotSubtypeReason::Disjoint {
                        left: other.clone().into(),
                        right: t,
                        reasons: Vec::new(),
                    }),
                )
            }
            (t, _) if t.is_non_polymorphic_recursive_fn_apply() => t
                .unwrap_recursive_fn_apply()
                .0
                .remove_disjoint_part_unit(other),
            (TypeUnit::TypeLevelApply { f, a }, _)
                if matches!(
                    f.matchable_ref(),
                    TypeMatchableRef::Const { .. }
                ) && other.is_wrapped_by_const() =>
            {
                let t: Type = TypeUnit::TypeLevelApply { f, a }.into();
                (
                    t.clone(),
                    Type::default(),
                    Some(NotSubtypeReason::Disjoint {
                        left: other.clone().into(),
                        right: t,
                        reasons: Vec::new(),
                    }),
                )
            }
            (t @ TypeUnit::TypeLevelApply { .. }, _)
            | (t, TypeUnit::TypeLevelApply { .. }) => {
                (Type::default(), t.into(), None)
            }
            (TypeUnit::Const { id: id1 }, TypeUnit::Const { id: id2, .. })
                if id1 == *id2 =>
            {
                (Type::default(), TypeUnit::Const { id: id1 }.into(), None)
            }
            (TypeUnit::Tuple(a1, a2), TypeUnit::Tuple(b1, b2)) => {
                let (a1_out, a1_in, r1) = a1.remove_disjoint_part(b1);
                if a1_in.is_empty() {
                    let out = Type::from(TypeUnit::Tuple(a1_out, a2));
                    return (
                        out.clone(),
                        Type::default(),
                        if out.is_empty() {
                            None
                        } else {
                            Some(NotSubtypeReason::Disjoint {
                                left: other.clone().into(),
                                right: out,
                                reasons: r1.into_iter().collect(),
                            })
                        },
                    );
                }
                let (a2_out, a2_in, r2) = a2.remove_disjoint_part(b2);
                let out = Type::default()
                    .union_unit(TypeUnit::Tuple(
                        a1_out,
                        a2_out.clone().union(a2_in.clone()),
                    ))
                    .union_unit(TypeUnit::Tuple(a1_in.clone(), a2_out));
                (
                    out.clone(),
                    TypeUnit::Tuple(a1_in, a2_in).into(),
                    if out.is_empty() {
                        None
                    } else {
                        Some(NotSubtypeReason::Disjoint {
                            left: other.clone().into(),
                            right: out,
                            reasons: vec![r1, r2]
                                .into_iter()
                                .flatten()
                                .collect(),
                        })
                    },
                )
            }
            (t, _) => (
                t.clone().into(),
                Type::default(),
                Some(NotSubtypeReason::Disjoint {
                    left: other.clone().into(),
                    right: t.into(),
                    reasons: Vec::new(),
                }),
            ),
        }
    }

    fn disjunctive(self) -> Result<Vec<Rc<Self>>, Self> {
        match self {
            TypeUnit::Tuple(a, b) => match a.disjunctive() {
                Ok(a) => Ok(a
                    .into_iter()
                    .map(|a| {
                        Rc::new(TypeUnit::Tuple(
                            unwrap_or_clone(a).into(),
                            b.clone(),
                        ))
                    })
                    .collect()),
                Err(a) => match b.disjunctive() {
                    Ok(b) => Ok(b
                        .into_iter()
                        .map(|b| {
                            Rc::new(TypeUnit::Tuple(
                                a.clone().into(),
                                unwrap_or_clone(b).into(),
                            ))
                        })
                        .collect()),
                    Err(b) => Err(TypeUnit::Tuple(a.into(), b.into())),
                },
            },
            a => Err(a),
        }
    }

    pub fn contains_broken_index(&self, recursive_alias_depth: usize) -> bool {
        match self {
            TypeUnit::Variable(TypeVariable::Normal(_))
            | TypeUnit::Const { .. }
            | TypeUnit::Any => false,
            TypeUnit::Variable(TypeVariable::RecursiveIndex(d)) => {
                *d >= recursive_alias_depth
            }
            TypeUnit::RecursiveAlias { body } => {
                body.contains_broken_index(recursive_alias_depth + 1)
            }
            TypeUnit::TypeLevelFn(f) => {
                f.contains_broken_index(recursive_alias_depth + 1)
            }
            TypeUnit::TypeLevelApply { f, a } => {
                f.contains_broken_index(recursive_alias_depth)
                    || a.contains_broken_index(recursive_alias_depth)
            }
            TypeUnit::Restrictions { t, .. } | TypeUnit::Variance(_, t) => {
                t.contains_broken_index(recursive_alias_depth)
            }
            TypeUnit::Tuple(a, b) => {
                a.contains_broken_index(recursive_alias_depth)
                    || b.contains_broken_index(recursive_alias_depth)
            }
        }
    }

    pub fn contains_restriction(&self) -> bool {
        match self {
            TypeUnit::Tuple(a, b) | TypeUnit::TypeLevelApply { f: b, a } => {
                a.contains_restriction() || b.contains_restriction()
            }
            TypeUnit::RecursiveAlias { body: a }
            | TypeUnit::TypeLevelFn(a)
            | TypeUnit::Variance(_, a) => a.contains_restriction(),
            TypeUnit::Variable(_) | TypeUnit::Const { .. } | TypeUnit::Any => {
                false
            }
            TypeUnit::Restrictions { .. } => true,
        }
    }

    pub fn is_wrapped_by_const(&self) -> bool {
        use TypeUnit::*;
        match self {
            Tuple(_, _) | Const { .. } => true,
            Variable(_) | Restrictions { .. } | Any => false,
            RecursiveAlias { body: a }
            | TypeLevelFn(a)
            | TypeLevelApply { f: a, .. }
            | Variance(_, a) => a.is_wrapped_by_const(),
        }
    }

    pub fn is_recursive_fn_apply(&self) -> bool {
        matches!(
            self,
            TypeUnit::TypeLevelApply { f, .. } if matches!(
                f.matchable_ref(),
                TypeMatchableRef::RecursiveAlias { .. }
            )
        )
    }

    pub fn is_non_polymorphic_recursive_fn_apply(&self) -> bool {
        fn contains_non_polymorphic_point_unit(
            t: &TypeUnit,
            depth: usize,
        ) -> bool {
            match t {
                TypeUnit::Tuple(a, b) => {
                    contains_non_polymorphic_point(a, depth)
                        || contains_non_polymorphic_point(b, depth)
                }
                TypeUnit::Variable(_)
                | TypeUnit::Const { .. }
                | TypeUnit::Any => false,
                TypeUnit::RecursiveAlias { body: a }
                | TypeUnit::TypeLevelFn(a)
                | TypeUnit::Variance(_, a) => {
                    contains_non_polymorphic_point(a, depth + 1)
                }
                TypeUnit::TypeLevelApply { f, a } => {
                    !matches!(
                        a.matchable_ref(),
                        TypeMatchableRef::Variable(
                            TypeVariable::RecursiveIndex(d)
                        )if d == depth
                    ) && f.contains_variable(TypeVariable::RecursiveIndex(
                        depth + 1,
                    ))
                }
                TypeUnit::Restrictions { t, .. } => {
                    contains_non_polymorphic_point(t, depth)
                }
            }
        }
        fn contains_non_polymorphic_point(t: &Type, depth: usize) -> bool {
            t.iter()
                .any(|t| contains_non_polymorphic_point_unit(t, depth))
        }
        if let TypeUnit::TypeLevelApply { f, .. } = self {
            if let TypeMatchableRef::RecursiveAlias { body } = f.matchable_ref()
            {
                if let TypeMatchableRef::TypeLevelFn(body) =
                    body.matchable_ref()
                {
                    !contains_non_polymorphic_point(body, 0)
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            false
        }
    }

    pub fn unwrap_recursive_fn_apply(self) -> (Type, bool) {
        match self {
            TypeUnit::TypeLevelApply { f, a }
                if matches!(
                    f.matchable_ref(),
                    TypeMatchableRef::RecursiveAlias { .. }
                ) =>
            {
                (f.type_level_function_apply_strong(a), true)
            }
            t => (t.into(), false),
        }
    }

    pub fn contains_recursion(&self) -> bool {
        match self {
            TypeUnit::TypeLevelApply { f: a, a: b } | TypeUnit::Tuple(a, b) => {
                a.contains_recursion() || b.contains_recursion()
            }
            TypeUnit::Restrictions { t: a, .. }
            | TypeUnit::TypeLevelFn(a)
            | TypeUnit::Variance(_, a) => a.contains_recursion(),
            TypeUnit::RecursiveAlias { .. } => true,
            TypeUnit::Const { .. } | TypeUnit::Variable(_) | TypeUnit::Any => {
                false
            }
        }
    }

    pub fn is_function(&self) -> bool {
        if let TypeUnit::Tuple(a, _) = self {
            matches!(
                a.matchable_ref(),
                TypeMatchableRef::Const {
                    id: TypeId::Intrinsic(crate::intrinsics::IntrinsicType::Fn),
                }
            )
        } else {
            false
        }
    }

    pub fn arrow(a: Type, b: Type) -> Self {
        TypeUnit::Tuple(
            TypeUnit::Const {
                id: TypeId::Intrinsic(IntrinsicType::Fn),
            }
            .into(),
            TypeUnit::Tuple(
                TypeUnit::Variance(
                    crate::ast_step2::types::Variance::Contravariant,
                    a,
                )
                .into(),
                TypeUnit::Tuple(
                    b,
                    TypeUnit::Const {
                        id: TypeId::Intrinsic(IntrinsicType::Unit),
                    }
                    .into(),
                )
                .into(),
            )
            .into(),
        )
    }

    pub fn type_level_function_apply(self, arg: Type) -> Type {
        match self {
            TypeUnit::TypeLevelFn(f) => {
                f.replace_index_zero_and_decrement_indices(arg)
            }
            TypeUnit::Tuple(head, tail) => {
                TypeUnit::Tuple(head, tail.type_level_function_apply(arg))
                    .into()
            }
            u @ TypeUnit::Const {
                id: TypeId::Intrinsic(IntrinsicType::Unit),
            } => TypeUnit::Tuple(arg, u.into()).into(),
            t => TypeUnit::TypeLevelApply {
                f: t.into(),
                a: arg,
            }
            .into(),
        }
    }

    pub fn type_level_function_apply_strong(self, arg: Type) -> Type {
        match self {
            TypeUnit::TypeLevelFn(f) => {
                f.replace_index_zero_and_decrement_indices(arg)
            }
            TypeUnit::RecursiveAlias { body } => {
                unwrap_recursive_alias(body).type_level_function_apply(arg)
            }
            t => TypeUnit::TypeLevelApply {
                f: t.into(),
                a: arg,
            }
            .into(),
        }
    }
}

impl Type {
    pub fn label_from_str(t: &'static str) -> Self {
        Type::from(TypeUnit::Const {
            id: TypeId::Intrinsic(INTRINSIC_TYPES[t]),
        })
    }

    pub fn arrow(self, other: Self) -> Self {
        TypeUnit::arrow(self, other).into()
    }

    pub fn union(mut self, other: Self) -> Self {
        if self.len() > 1000 {
            panic!()
        }
        self.union_in_place(other);
        self
    }

    pub fn union_unit(mut self, other: TypeUnit) -> Self {
        self.insert(other.into());
        self
    }

    pub fn disjunctive(self) -> Result<Vec<Rc<TypeUnit>>, TypeUnit> {
        if self.len() > 1 {
            Ok(self.into_iter().collect())
        } else {
            unwrap_or_clone(self.into_iter().next().unwrap()).disjunctive()
        }
    }

    pub fn intersection_and_difference(
        self,
        other: Self,
    ) -> (Self, Self, Self) {
        let (maybe_only_in_self, intersection) = self.split(&other);
        let (maybe_only_in_other, b_) = other.split(&intersection);
        debug_assert_eq!(intersection, b_);
        (maybe_only_in_self, intersection, maybe_only_in_other)
    }

    pub fn split(self, other: &Self) -> (Self, Self) {
        let mut in_ = Type::default();
        let mut out = self;
        for t in other.iter() {
            let i;
            (out, i) = out.split_unit(t);
            in_.union_in_place(i);
        }
        (out, in_)
    }

    pub fn split_slow(
        self,
        other: &Self,
        visited: &mut BTreeMap<(TypeUnit, TypeUnit), Option<(Type, Type)>>,
    ) -> (Self, Self) {
        let mut in_ = Type::default();
        let mut out = self;
        for t in other.iter() {
            let i;
            (out, i) = out.split_unit_slow(t, visited);
            in_.union_in_place(i);
        }
        (out, in_)
    }

    pub fn split_unit(self, other: &TypeUnit) -> (Self, Self) {
        let mut in_ = Type::default();
        let mut out = Type::default();
        for t in self {
            let (o, i) = unwrap_or_clone(t).split(other);
            in_.union_in_place(i);
            out.union_in_place(o);
        }
        (out, in_)
    }

    pub fn split_unit_slow(
        self,
        other: &TypeUnit,
        visited: &mut BTreeMap<(TypeUnit, TypeUnit), Option<(Type, Type)>>,
    ) -> (Self, Self) {
        if !self.contains_recursion() && other.is_recursive_fn_apply() {
            let other = other.clone().unwrap_recursive_fn_apply().0;
            return self.split_slow(&other, visited);
        }
        let mut in_ = Type::default();
        let mut out = Type::default();
        for t in self {
            let (o, i) = unwrap_or_clone(t).split_slow(other, visited);
            in_.union_in_place(i);
            out.union_in_place(o);
        }
        (out, in_)
    }

    pub fn remove_disjoint_part(
        self,
        other: &Self,
    ) -> (Self, Self, Option<NotSubtypeReason>) {
        let mut in_ = Type::default();
        let mut out = self;
        let mut reasons = Vec::new();
        for t in other.iter() {
            let i;
            let r;
            (out, i, r) = out.remove_disjoint_part_unit(t);
            in_.union_in_place(i);
            if let Some(r) = r {
                reasons.push(r);
            }
        }
        (
            out.clone(),
            in_,
            if other.len() == 1 {
                reasons.into_iter().next()
            } else {
                Some(NotSubtypeReason::Disjoint {
                    left: out,
                    right: other.clone(),
                    reasons,
                })
            },
        )
    }

    pub fn remove_disjoint_part_unit(
        self,
        other: &TypeUnit,
    ) -> (Self, Self, Option<NotSubtypeReason>) {
        if !self.contains_recursion() && other.is_recursive_fn_apply() {
            return self.remove_disjoint_part(
                &Type::from(other.clone()).unwrap_recursive_fn_apply().0,
            );
        }
        let mut in_ = Type::default();
        let mut out = Type::default();
        let mut reasons = Vec::new();
        let self_len = self.len();
        for t in self {
            let (o, i, r) = unwrap_or_clone(t).remove_disjoint_part(other);
            in_.union_in_place(i);
            out.union_in_place(o);
            if let Some(r) = r {
                reasons.push(r);
            }
        }
        let reason = if self_len == 1 {
            reasons.into_iter().next()
        } else {
            Some(NotSubtypeReason::Disjoint {
                left: other.clone().into(),
                right: out.clone(),
                reasons,
            })
        };
        (out, in_, reason)
    }

    pub fn diff(self, other: &Self) -> Self {
        let (t, _) = self.split(other);
        t
    }

    pub fn type_level_function_apply(self, arg: Self) -> Self {
        self.into_iter()
            .flat_map(|t| {
                unwrap_or_clone(t).type_level_function_apply(arg.clone())
            })
            .collect()
    }

    pub fn type_level_function_apply_strong(self, arg: Self) -> Self {
        self.into_iter()
            .flat_map(|t| {
                unwrap_or_clone(t).type_level_function_apply_strong(arg.clone())
            })
            .collect()
    }

    pub fn replace_index_zero_and_decrement_indices(self, t: Self) -> Self {
        self.replace_num(
            TypeVariable::RecursiveIndex(0),
            &t.increment_recursive_index(0, 1),
        )
        .increment_recursive_index(0, -1)
    }

    pub fn contains_broken_index(&self, recursive_alias_depth: usize) -> bool {
        self.iter()
            .any(|t| t.contains_broken_index(recursive_alias_depth))
    }

    pub fn contains_restriction(&self) -> bool {
        self.iter().any(|t| t.contains_restriction())
    }

    pub fn is_function(&self) -> bool {
        match self.matchable_ref() {
            TypeMatchableRef::TypeLevelFn(t)
            | TypeMatchableRef::Restrictions { t, .. }
            | TypeMatchableRef::RecursiveAlias { body: t } => t.is_function(),
            TypeMatchableRef::Tuple(a, _) => {
                matches!(
                    a.matchable_ref(),
                    TypeMatchableRef::Const {
                        id: TypeId::Intrinsic(
                            crate::intrinsics::IntrinsicType::Fn
                        ),
                    }
                )
            }
            TypeMatchableRef::TypeLevelApply { .. }
            | TypeMatchableRef::Const { .. }
            | TypeMatchableRef::Union(_)
            | TypeMatchableRef::Variable(_)
            | TypeMatchableRef::Empty
            | TypeMatchableRef::Any
            | TypeMatchableRef::Variance(_, _) => false,
        }
    }

    pub fn is_wrapped_by_const(&self) -> bool {
        self.iter().all(|t| t.is_wrapped_by_const())
    }

    pub fn is_non_polymorphic_recursive_fn_apply(&self) -> bool {
        self.len() == 1
            && self
                .iter()
                .next()
                .unwrap()
                .is_non_polymorphic_recursive_fn_apply()
    }

    pub fn is_recursive_fn_apply(&self) -> bool {
        self.len() == 1 && self.iter().next().unwrap().is_recursive_fn_apply()
    }

    pub fn unwrap_recursive_fn_apply(self) -> (Self, bool) {
        match self.matchable() {
            TypeMatchable::TypeLevelApply { f, a }
                if matches!(
                    f.matchable_ref(),
                    TypeMatchableRef::RecursiveAlias { .. }
                ) =>
            {
                (f.type_level_function_apply_strong(a), true)
            }
            t => (t.into(), false),
        }
    }

    pub fn contains_recursion(&self) -> bool {
        self.iter().any(|t| t.contains_recursion())
    }
}

impl TypeWithEnv {
    pub fn insert_to_subtype_rels_with_restrictions(
        &mut self,
        value: (Type, Type, RelOrigin),
    ) {
        let a = match value.0.matchable() {
            TypeMatchable::Restrictions { .. } => {
                panic!();
            }
            a => a.into(),
        };
        let b = match value.1.matchable() {
            TypeMatchable::Restrictions { .. } => {
                panic!();
            }
            b => b.into(),
        };
        self.subtype_relations.insert((a, b, value.2));
    }
}

#[cfg(test)]
mod tests {
    use crate::ast_step1::name_id::Path;
    use crate::{ast_step1, ast_step2, combine_with_prelude, Imports};
    use stripmargin::StripMargin;

    #[test]
    fn conjunctive_0() {
        let src = r#"
        |main : () -> () =
        |    | () => ()
        |test1 : (False /\ False) | (False /\ True) | (True /\ False) | (True /\ True) = ()
        |"#.strip_margin();
        let ast = combine_with_prelude(parser::parse(&src));
        let mut imports = Imports::default();
        let (ast, mut token_map) =
            ast_step1::Ast::from(&ast, &mut imports).unwrap();
        let ast =
            ast_step2::Ast::from(ast, &mut token_map, &mut imports).unwrap();
        let t = ast
            .variable_decl
            .iter()
            .find(|d| d.name == Path::from_str(Path::pkg_root(), "test1"))
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .unfixed;
        assert_eq!(
            format!("{t}"),
            r#"/\[[{:True | :False}], [{:True | :False}]]"#
        );
    }
}
