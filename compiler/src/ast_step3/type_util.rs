use crate::{
    ast_step1,
    ast_step2::{
        type_to_type,
        types::{
            merge_vec, unwrap_or_clone, Type, TypeMatchable, TypeMatchableRef,
            TypeUnit, TypeVariable,
        },
        SubtypeRelations, TypeConstructor, TypeId, TypeWithEnv,
    },
    intrinsics::INTRINSIC_TYPES,
};
use std::rc::Rc;

impl TypeUnit {
    pub fn all_type_variables(&self) -> Vec<TypeVariable> {
        match self {
            TypeUnit::Fn(arg, ret) => arg
                .all_type_variables_vec()
                .into_iter()
                .chain(ret.all_type_variables_vec().into_iter())
                .collect(),
            TypeUnit::Variable(i) => std::iter::once(*i).collect(),
            TypeUnit::RecursiveAlias { body } => {
                let s = body.all_type_variables_vec();
                s.into_iter().filter(|d| !d.is_recursive_index()).collect()
            }
            TypeUnit::Const { .. } => Vec::new(),
            TypeUnit::Tuple(a, b) => a
                .all_type_variables_vec()
                .into_iter()
                .chain(b.all_type_variables_vec().into_iter())
                .collect(),
            TypeUnit::TypeLevelFn(f) => f.all_type_variables_vec(),
            TypeUnit::TypeLevelApply { f, a } => merge_vec(
                f.all_type_variables_vec(),
                a.all_type_variables_vec(),
            ),
            TypeUnit::Restrictions { t, .. } => t.all_type_variables_vec(),
        }
    }

    pub fn replace_num_with_update_flag(
        self,
        from: TypeVariable,
        to: &Type,
        recursive_alias_depth: usize,
    ) -> (Type, bool) {
        match self {
            Self::Fn(args, rtn) => {
                let (args, updated1) = args.replace_num_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                let (rtn, updated2) = rtn.replace_num_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                (Self::Fn(args, rtn).into(), updated1 || updated2)
            }
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
            Self::Const { id } => (Self::Const { id }.into(), false),
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
        }
    }

    pub fn replace_num(self, from: TypeVariable, to: &Type) -> Type {
        self.replace_num_with_update_flag(from, to, 0).0
    }

    pub fn replace_type(self, from: &TypeUnit, to: &TypeUnit) -> Self {
        match self {
            t if t == *from => to.clone(),
            Self::Fn(args, rtn) => Self::Fn(
                args.replace_type(from, to),
                rtn.replace_type(from, to),
            ),
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
            Self::Fn(args, rtn) => Self::Fn(
                args.replace_type_union(from, to),
                rtn.replace_type_union(from, to),
            ),
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
            TypeUnit::Fn(a, b) => Fn(a, b),
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
        }
    }

    pub fn replace_type_union_with_update_flag(
        self,
        from: &Type,
        to: &TypeUnit,
        recursive_alias_depth: usize,
    ) -> (Self, bool) {
        if self.matchable_ref() == from.matchable_ref() {
            return (to.clone(), true);
        }
        match self {
            Self::Fn(args, rtn) => {
                let (args, u1) = args.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                let (rtn, u2) = rtn.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
                );
                (Self::Fn(args, rtn), u1 || u2)
            }
            Self::RecursiveAlias { body } => {
                let (body, updated) = body.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
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
            t @ (Self::Variable(_) | Self::Const { .. }) => (t, false),
            Self::TypeLevelFn(f) => {
                let (f, u) = f.replace_type_union_with_update_flag(
                    from,
                    to,
                    recursive_alias_depth,
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
        }
    }

    pub fn contains_variable(&self, variable_num: TypeVariable) -> bool {
        match self {
            Self::Fn(a, r) => {
                a.contains_variable(variable_num)
                    || r.contains_variable(variable_num)
            }
            Self::Variable(n) => *n == variable_num,
            Self::RecursiveAlias { body } => body
                .contains_variable(variable_num.increment_recursive_index(1)),
            Self::Const { .. } => false,
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
            Self::Restrictions { t, .. } => t.contains_variable(variable_num),
        }
    }

    fn split(self, other: &Self) -> (Type, Type) {
        match (self, other) {
            (TypeUnit::Fn(a1, a2), TypeUnit::Fn(b1, b2)) => {
                if b1.clone().is_subtype_of(a1.clone()) {
                    let (a2_out, a2_in) = a2.split(b2);
                    (
                        TypeUnit::Fn(a1.clone(), a2_out).into(),
                        TypeUnit::Fn(a1, a2_in).into(),
                    )
                } else {
                    (TypeUnit::Fn(a1, a2).into(), Type::default())
                }
            }
            (TypeUnit::Const { id: id1 }, TypeUnit::Const { id: id2, .. })
                if id1 == *id2 =>
            {
                (Type::default(), TypeUnit::Const { id: id1 }.into())
            }
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
            (t, _) => (t.into(), Type::default()),
        }
    }

    fn split_broad(self, other: &Self) -> (Type, Type) {
        match (self, other) {
            (
                t @ (TypeUnit::Variable(_) | TypeUnit::RecursiveAlias { .. }),
                _,
            )
            | (t, TypeUnit::Variable(_) | TypeUnit::RecursiveAlias { .. }) => {
                (Type::default(), t.into())
            }
            (TypeUnit::Fn(a1, a2), TypeUnit::Fn(b1, b2)) => {
                if b1.clone().is_subtype_of(a1.clone()) {
                    let (a2_out, a2_in) = a2.split_broad(b2);
                    (
                        TypeUnit::Fn(a1.clone(), a2_out).into(),
                        TypeUnit::Fn(a1, a2_in).into(),
                    )
                } else {
                    (Type::default(), TypeUnit::Fn(a1, a2).into())
                }
            }
            (TypeUnit::Const { id: id1 }, TypeUnit::Const { id: id2, .. })
                if id1 == *id2 =>
            {
                (Type::default(), TypeUnit::Const { id: id1 }.into())
            }
            (TypeUnit::Tuple(a1, a2), TypeUnit::Tuple(b1, b2)) => {
                let (a1_out, a1_in) = a1.split_broad(b1);
                let (a2_out, a2_in) = a2.split_broad(b2);
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
            (t, _) => (t.into(), Type::default()),
        }
    }

    fn disjunctive(self) -> Result<Vec<Rc<Self>>, Self> {
        match self {
            TypeUnit::Fn(a, b) => match b.disjunctive() {
                Ok(b) => Ok(b
                    .into_iter()
                    .map(|b| {
                        Rc::new(TypeUnit::Fn(
                            a.clone(),
                            unwrap_or_clone(b).into(),
                        ))
                    })
                    .collect()),
                Err(b) => Err(TypeUnit::Fn(a, b.into())),
            },
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
            TypeUnit::Fn(a, b) => {
                a.contains_broken_index(recursive_alias_depth)
                    || b.contains_broken_index(recursive_alias_depth)
            }
            TypeUnit::Variable(TypeVariable::Normal(_)) => false,
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
            TypeUnit::Restrictions { t, .. } => {
                t.contains_broken_index(recursive_alias_depth)
            }
            TypeUnit::Const { .. } => false,
            TypeUnit::Tuple(a, b) => {
                a.contains_broken_index(recursive_alias_depth)
                    || b.contains_broken_index(recursive_alias_depth)
            }
        }
    }

    pub fn contains_restriction(&self) -> bool {
        match self {
            TypeUnit::Fn(a, b)
            | TypeUnit::Tuple(a, b)
            | TypeUnit::TypeLevelApply { f: b, a } => {
                a.contains_restriction() || b.contains_restriction()
            }
            TypeUnit::RecursiveAlias { body: a } | TypeUnit::TypeLevelFn(a) => {
                a.contains_restriction()
            }
            TypeUnit::Variable(_) | TypeUnit::Const { .. } => false,
            TypeUnit::Restrictions { .. } => true,
        }
    }
}

impl Type {
    // pub fn is_singleton(&self) -> bool {
    //     use TypeMatchableRef::*;
    //     match self.matchable_ref() {
    //         Fn(a, b) => a.is_singleton() && b.is_singleton(),
    //         Tuple(a, b) => a.is_singleton() && b.is_singleton(),
    //         Const { .. } => true,
    //         _ => false,
    //     }
    // }

    pub fn from_str(t: &'static str) -> Self {
        let t = ast_step1::Type {
            name: (t, None),
            args: Default::default(),
        };
        type_to_type(
            t,
            &Default::default(),
            &Default::default(),
            &mut Default::default(),
            crate::ast_step2::SearchMode::Normal,
            &mut Default::default(),
        )
    }

    pub fn label_from_str(t: &'static str) -> Self {
        Type::from(TypeUnit::Const {
            id: TypeId::Intrinsic(INTRINSIC_TYPES[t]),
        })
    }

    pub fn arrow(self, other: Self) -> Self {
        TypeUnit::Fn(self, other).into()
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

    // pub fn partition(self) -> Vec<Self> {
    //     let mut t = Vec::new();
    //     let s = self.disjunctive();
    //     for tu in s.iter() {
    //         if tu.is_singleton() {
    //             t.push(tu.clone().into());
    //         } else {
    //             return vec![s];
    //         }
    //     }
    //     t.into_iter().collect()
    // }

    pub fn disjunctive(self) -> Result<Vec<Rc<TypeUnit>>, TypeUnit> {
        if self.len() > 1 {
            Ok(self.into_iter().collect())
        } else {
            unwrap_or_clone(self.into_iter().next().unwrap()).disjunctive()
        }
    }

    // pub fn conjunctive(self) -> Self {
    //     let mut ts: Vec<_> = self
    //         .into_iter()
    //         .map(|t| unwrap_or_clone(t).conjunctive())
    //         .collect();
    //     let mut new_ts = Vec::new();
    //     'pop_loop: while let Some(last_t) = ts.pop() {
    //         for t in ts.iter_mut() {
    //             if let Some(merged) = t.merge_union_with(&last_t) {
    //                 *t = merged;
    //                 continue 'pop_loop;
    //             }
    //         }
    //         new_ts.push(last_t);
    //     }
    //     new_ts.into_iter().collect()
    // }

    pub fn intersection_and_difference(
        self,
        other: Self,
    ) -> (Self, Self, Self) {
        let (a, b) = self.split(&other);
        let (c, b_) = other.split(&b);
        debug_assert_eq!(b, b_);
        (a, b, c)
    }

    pub fn intersection_and_difference_broad(
        self,
        other: Self,
    ) -> (Self, Self, Self, Self) {
        let (a, b) = self.split_broad(&other);
        let (c, d) = other.split_broad(&b);
        (a, b, d, c)
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

    pub fn split_broad(self, other: &Self) -> (Self, Self) {
        let mut in_ = Type::default();
        let mut out = self;
        for t in other.iter() {
            let i;
            (out, i) = out.split_broad_unit(t);
            in_.union_in_place(i);
        }
        (out, in_)
    }

    pub fn split_broad_unit(self, other: &TypeUnit) -> (Self, Self) {
        let mut in_ = Type::default();
        let mut out = Type::default();
        for t in self {
            let (o, i) = unwrap_or_clone(t).split_broad(other);
            in_.union_in_place(i);
            out.union_in_place(o);
        }
        (out, in_)
    }

    pub fn diff(self, other: &Self) -> Self {
        let (t, _) = self.split(other);
        t
    }

    pub fn type_level_function_apply(self, arg: Self) -> Self {
        match self.matchable() {
            TypeMatchable::TypeLevelFn(f) => f
                .replace_num(TypeVariable::RecursiveIndex(0), &arg)
                .increment_recursive_index(0, -1),
            TypeMatchable::RecursiveAlias { body } => {
                if let TypeMatchable::TypeLevelFn(f) = body.clone().matchable()
                {
                    TypeUnit::RecursiveAlias {
                        body: apply_arg_to_recursive_fn(f, &arg, 0),
                    }
                    .into()
                } else {
                    TypeUnit::TypeLevelApply {
                        f: TypeMatchable::RecursiveAlias { body }.into(),
                        a: arg,
                    }
                    .into()
                }
            }
            t => TypeUnit::TypeLevelApply {
                f: t.into(),
                a: arg,
            }
            .into(),
        }
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
            TypeMatchableRef::Fn(_, _) => true,
            TypeMatchableRef::TypeLevelFn(t)
            | TypeMatchableRef::Restrictions { t, .. }
            | TypeMatchableRef::RecursiveAlias { body: t } => t.is_function(),
            TypeMatchableRef::TypeLevelApply { .. }
            | TypeMatchableRef::Const { .. }
            | TypeMatchableRef::Tuple(_, _)
            | TypeMatchableRef::Union(_)
            | TypeMatchableRef::Variable(_)
            | TypeMatchableRef::Empty => false,
        }
    }
}

fn apply_arg_to_recursive_fn(
    f: Type,
    arg: &Type,
    recursive_alias_depth: usize,
) -> Type {
    use TypeUnit::*;
    f.into_iter()
        .flat_map(|t| match unwrap_or_clone(t) {
            Fn(f, a) => Fn(
                apply_arg_to_recursive_fn(f, arg, recursive_alias_depth),
                apply_arg_to_recursive_fn(a, arg, recursive_alias_depth),
            )
            .into(),
            Variable(v) => {
                if v == TypeVariable::RecursiveIndex(recursive_alias_depth + 1)
                {
                    panic!()
                } else if v
                    == TypeVariable::RecursiveIndex(recursive_alias_depth)
                {
                    arg.clone()
                } else {
                    Variable(v.increment_recursive_index_with_bound(1, -1))
                        .into()
                }
            }
            RecursiveAlias { body } => RecursiveAlias {
                body: apply_arg_to_recursive_fn(
                    body,
                    arg,
                    recursive_alias_depth + 1,
                ),
            }
            .into(),
            TypeLevelFn(f) => TypeLevelFn(apply_arg_to_recursive_fn(
                f,
                arg,
                recursive_alias_depth + 1,
            ))
            .into(),
            TypeLevelApply { f, a } => {
                match (f.matchable_ref(), a.matchable_ref()) {
                    (
                        TypeMatchableRef::Variable(
                            TypeVariable::RecursiveIndex(f),
                        ),
                        TypeMatchableRef::Variable(
                            TypeVariable::RecursiveIndex(a),
                        ),
                    ) if f == (recursive_alias_depth + 1)
                        && a == recursive_alias_depth =>
                    {
                        Variable(TypeVariable::RecursiveIndex(
                            recursive_alias_depth,
                        ))
                        .into()
                    }
                    _ => TypeLevelApply {
                        f: apply_arg_to_recursive_fn(
                            f,
                            arg,
                            recursive_alias_depth,
                        ),
                        a: apply_arg_to_recursive_fn(
                            a,
                            arg,
                            recursive_alias_depth,
                        ),
                    }
                    .into(),
                }
            }
            Const { id } => Const { id }.into(),
            Tuple(a, b) => Tuple(
                apply_arg_to_recursive_fn(a, arg, recursive_alias_depth),
                apply_arg_to_recursive_fn(b, arg, recursive_alias_depth),
            )
            .into(),
            Restrictions { .. } => unimplemented!(),
        })
        .collect()
}

// impl<'a> PatternUnitForRestriction<'_> {
//     pub fn all_type_variables(&self) -> FxHashSet<TypeVariable> {
//         match self {
//             PatternUnitForRestriction::Str
//             | PatternUnitForRestriction::I64 => Default::default(),
//             PatternUnitForRestriction::Constructor {
//                 args, ..
//             } => args
//                 .into_iter()
//                 .flat_map(|a| a.all_type_variables())
//                 .collect(),
//             PatternUnitForRestriction::Binder(v) => {
//                 [*v].into_iter().collect()
//             }
//         }
//     }
// }

impl TypeWithEnv {
    pub fn insert_to_subtype_rels_with_restrictions(
        &mut self,
        value: (Type, Type),
    ) {
        let mut additional_subtype_rel = SubtypeRelations::default();
        let a = match value.0.matchable() {
            TypeMatchable::Restrictions {
                t,
                variable_requirements: _,
                subtype_relations,
            } => {
                additional_subtype_rel.extend(subtype_relations);
                // self.variable_requirements
                //     .append(&mut variable_requirements);
                t
            }
            a => a.into(),
        };
        let b = match value.1.matchable() {
            TypeMatchable::Restrictions {
                t,
                variable_requirements: _,
                subtype_relations,
            } => {
                additional_subtype_rel.extend(subtype_relations);
                // self.variable_requirements
                //     .append(&mut variable_requirements);
                t
            }
            b => b.into(),
        };
        self.subtype_relations.insert((a, b));
        self.subtype_relations.extend(additional_subtype_rel);
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast_step1,
        ast_step2::{self, name_id::Name},
    };

    #[test]
    fn conjunctive_0() {
        let src = r#"data A /\ B forall { A, B }
        infixl 3 /\
        main : () -> () =
            | () => ()
        test1 : (False /\ False) | (False /\ True) | (True /\ False) | (True /\ True) = ()
        "#;
        let ast = parser::parse(src);
        let (ast, _) = ast_step1::Ast::from(&ast);
        let (ast, _) = ast_step2::Ast::from(ast);
        let t = ast
            .variable_decl
            .iter()
            .find(|d| d.name == Name::from_str("test1"))
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .unfixed;
        assert_eq!(
            format!("{}", t),
            r#"/\[[{:True | :False}], [{:True | :False}]]"#
        );
    }

    #[test]
    fn conjunctive_1() {
        let src = r#"data A /\ B forall { A, B }
        infixr 3 /\
        main : () -> () =
            | () => ()
        type List = () | A /\ List[A] forall { A }
        test1 : List[() | I64] | List[I64] = ()
        "#;
        let ast = parser::parse(src);
        let (ast, _) = ast_step1::Ast::from(&ast);
        let (ast, _) = ast_step2::Ast::from(ast);
        let t = ast
            .variable_decl
            .iter()
            .find(|d| d.name == Name::from_str("test1"))
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .unfixed;
        assert_eq!(format!("{}", t), r#"rec[{/\[[{:I64 | :()}], d0] | ()}]"#);
    }
}
