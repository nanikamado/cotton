use crate::{
    ast_step1,
    ast_step2::{
        type_to_type,
        types::{Type, TypeMatchableRef, TypeUnit, TypeVariable},
        IncompleteType, TypeConstructor,
    },
};
use fxhash::FxHashSet;
use itertools::Itertools;
use TypeMatchableRef::{Fn, Normal};

impl<'a> TypeUnit<'a> {
    pub fn all_type_variables(&self) -> Vec<TypeVariable> {
        match self {
            TypeUnit::Normal { args, .. } => args
                .iter()
                .flat_map(|t| t.all_type_variables_vec())
                .collect(),
            TypeUnit::Fn(arg, ret) => arg
                .all_type_variables_vec()
                .into_iter()
                .chain(ret.all_type_variables_vec().into_iter())
                .collect(),
            TypeUnit::Variable(i) => std::iter::once(*i).collect(),
            TypeUnit::RecursiveAlias { body } => {
                let s = body.all_type_variables_vec();
                s.into_iter()
                    .filter(|d| !d.is_recursive_index())
                    .collect()
            }
        }
    }

    pub fn replace_num(
        self,
        from: TypeVariable,
        to: &Type<'a>,
    ) -> Type<'a> {
        match self {
            Self::Fn(args, rtn) => Self::Fn(
                args.replace_num(from, to),
                rtn.replace_num(from, to),
            )
            .into(),
            Self::Normal { name, args, id } => {
                let args = args
                    .into_iter()
                    .map(|t| t.replace_num(from, to))
                    .collect_vec();
                if args.iter().any(|c| c.len() == 0) {
                    Default::default()
                } else {
                    Self::Normal { name, args, id }.into()
                }
            }
            Self::Variable(n) => {
                if n == from {
                    to.clone()
                } else {
                    Self::Variable(n).into()
                }
            }
            Self::RecursiveAlias { body } => {
                debug_assert_ne!(
                    TypeVariable::recursive_index_zero(),
                    from
                );
                (Self::RecursiveAlias {
                    body: body.replace_num(from, to),
                })
                .into()
            }
        }
    }

    pub fn replace_type(
        self,
        from: &TypeUnit<'a>,
        to: &TypeUnit<'a>,
    ) -> Self {
        match self {
            t if t == *from => to.clone(),
            Self::Fn(args, rtn) => Self::Fn(
                args.replace_type(from, to),
                rtn.replace_type(from, to),
            ),
            Self::Normal { name, args, id } => Self::Normal {
                name,
                args: args
                    .into_iter()
                    .map(|t| t.replace_type(from, to))
                    .collect(),
                id,
            },
            Self::Variable(n) => Self::Variable(n),
            Self::RecursiveAlias { body } => Self::RecursiveAlias {
                body: body.replace_type(from, to),
            },
        }
    }

    pub fn replace_type_union(
        self,
        from: &Type,
        to: &TypeUnit<'a>,
    ) -> Self {
        match self {
            Self::Fn(args, rtn) => Self::Fn(
                args.replace_type_union(from, to),
                rtn.replace_type_union(from, to),
            ),
            Self::Normal { name, args, id } => Self::Normal {
                name,
                args: args
                    .into_iter()
                    .map(|t| t.replace_type_union(from, to))
                    .collect(),
                id,
            },
            Self::Variable(n) => Self::Variable(n),
            Self::RecursiveAlias { body } => Self::RecursiveAlias {
                body: body.replace_type_union(from, to),
            },
        }
    }

    pub fn contains_num(&self, variable_num: TypeVariable) -> bool {
        match self {
            Self::Normal { args, .. } => {
                args.iter().any(|c| c.contains_num(variable_num))
            }
            Self::Fn(a, r) => {
                a.contains_num(variable_num)
                    || r.contains_num(variable_num)
            }
            Self::Variable(n) => *n == variable_num,
            Self::RecursiveAlias { body } => {
                body.contains_num(variable_num)
            }
        }
    }

    pub fn is_singleton(&self) -> bool {
        match self {
            TypeUnit::Normal { args, .. } => {
                args.iter().all(|c| c.is_singleton())
            }
            TypeUnit::Fn(a, b) => {
                a.is_singleton() && b.is_singleton()
            }
            _ => false,
        }
    }

    fn merge_union_with(&self, other: &Self) -> Option<Self> {
        use TypeUnit::*;
        match (self, other) {
            (
                Normal {
                    name,
                    args: args1,
                    id: id1,
                },
                Normal {
                    args: args2,
                    id: id2,
                    ..
                },
            ) if id1 == id2 => {
                let mut diff_count = 0;
                let mut diff_position = None;
                for (i, (a1, a2)) in
                    args1.into_iter().zip(args2).enumerate()
                {
                    if a1 != a2 {
                        diff_count += 1;
                        diff_position = Some(i);
                    }
                }
                if diff_count == 0 {
                    Some(self.clone())
                } else if diff_count == 1 {
                    let diff_position = diff_position.unwrap();
                    let mut args = args1.clone();
                    args[diff_position] = args1[diff_position]
                        .clone()
                        .union(args2[diff_position].clone());
                    Some(Normal {
                        name,
                        args,
                        id: *id1,
                    })
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

impl<'a> Type<'a> {
    pub fn is_singleton(&self) -> bool {
        match self.matchable_ref() {
            Normal { args, .. } => {
                args.iter().all(|c| c.is_singleton())
            }
            Fn(a, b) => a.is_singleton() && b.is_singleton(),
            _ => false,
        }
    }

    pub fn contains_num(&self, variable_num: TypeVariable) -> bool {
        self.iter().any(|t| t.contains_num(variable_num))
    }

    pub fn from_str(t: &'static str) -> Self {
        let t = ast_step1::Type {
            name: t,
            args: Default::default(),
        };
        type_to_type(
            t,
            &Default::default(),
            &Default::default(),
            &mut Default::default(),
            crate::ast_step2::SearchMode::Normal,
        )
    }

    pub fn arrow(self, other: Self) -> Self {
        TypeUnit::Fn(self, other).into()
    }

    pub fn union(self, other: Self) -> Self {
        self.into_iter().chain(other.into_iter()).collect()
    }

    pub fn partition(self) -> Vec<Self> {
        let mut t = Vec::new();
        let s = self.disjunctive();
        for tu in s.iter() {
            if tu.is_singleton() {
                t.push(tu.clone().into());
            } else {
                return vec![s];
            }
        }
        t.into_iter().collect()
    }

    pub fn disjunctive(self) -> Self {
        self.into_iter()
            .flat_map(|tu| match tu {
                TypeUnit::Normal { name, args, id } => {
                    if args.is_empty() {
                        vec![TypeUnit::Normal { name, args, id }]
                    } else {
                        args.into_iter()
                            .map(|t| {
                                // t.partition()
                                t.disjunctive()
                                    .into_iter()
                                    .map(Type::from)
                                    .collect_vec()
                                // vec![t]
                            })
                            .multi_cartesian_product()
                            .map(|args| TypeUnit::Normal {
                                name,
                                args,
                                id,
                            })
                            .collect()
                    }
                }
                tu => vec![tu],
            })
            .collect()
    }

    pub fn conjunctive(self) -> Self {
        let mut ts: Vec<_> = self.into_iter().collect();
        let mut new_ts = Vec::new();
        'pop_loop: while let Some(last_t) = ts.pop() {
            for t in ts.iter_mut() {
                if let Some(merged) = t.merge_union_with(&last_t) {
                    *t = merged;
                    continue 'pop_loop;
                }
            }
            new_ts.push(last_t);
        }
        new_ts.into_iter().collect()
    }
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

impl<'a> IncompleteType<'a> {
    pub fn all_type_variables(&self) -> FxHashSet<TypeVariable> {
        let IncompleteType {
            constructor,
            variable_requirements,
            subtype_relations: subtype_relation,
            pattern_restrictions: _,
        } = self;
        variable_requirements
            .iter()
            .flat_map(|(_, t, _, _)| t.all_type_variables())
            .chain(subtype_relation.iter().flat_map(|(a, b)| {
                let mut a = a.all_type_variables();
                a.extend(b.all_type_variables());
                a
            }))
            .chain(constructor.all_type_variables())
            // .chain(pattern_restrictions.into_iter().flat_map(
            //     |(v, p)| {
            //         p.into_iter()
            //             .flat_map(|p| p.all_type_variables())
            //             .chain(v.all_type_variables())
            //     },
            // ))
            .collect::<FxHashSet<_>>()
    }

    pub fn change_variable_num(
        mut self,
    ) -> (Self, Vec<(TypeVariable, TypeVariable)>) {
        let anos = self.all_type_variables();
        let mut variable_map = Vec::new();
        for a in anos {
            let new_variable = TypeVariable::new();
            self = self.replace_num(
                a,
                &TypeUnit::Variable(new_variable).into(),
            );
            variable_map.push((a, new_variable));
        }
        (self, variable_map)
    }
}

impl<'a, T> IncompleteType<'a, T>
where
    T: TypeConstructor<'a>,
{
    pub fn replace_num(
        self,
        from: TypeVariable,
        to: &Type<'a>,
    ) -> Self {
        self.map_type(|t| t.replace_num(from, to))
    }

    pub fn map_type<F>(self, mut f: F) -> Self
    where
        F: FnMut(Type<'a>) -> Type<'a>,
    {
        let IncompleteType {
            constructor,
            variable_requirements,
            subtype_relations: subtype_relationship,
            pattern_restrictions,
        } = self;
        IncompleteType {
            constructor: constructor.map_type(&mut f),
            variable_requirements: variable_requirements
                .into_iter()
                .map(|(name, t, id, type_variable)| {
                    (name, f(t), id, type_variable)
                })
                .collect(),
            subtype_relations: subtype_relationship
                .into_iter()
                .map(|(a, b)| (f(a), f(b)))
                .collect(),
            pattern_restrictions,
        }
    }

    pub fn conjunctive(self) -> Self {
        self.map_type(|t| t.conjunctive())
    }
}

#[cfg(test)]
mod tests {
    use crate::{ast_step1, ast_step2};

    #[test]
    fn conjunctive_0() {
        let src = r#"data a /\ b
        infixl 3 /\
        main : () -> () =
            | () => ()
        test1 : (False /\ False) | (False /\ True) | (True /\ False) | (True /\ True) = ()
        "#;
        let ast = parse::parse(src);
        let ast: ast_step1::Ast = (&ast).into();
        let ast: ast_step2::Ast = ast.into();
        let t = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "test1")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        assert_eq!(
            format!("{}", t.conjunctive()),
            r#"/\({False | True}, {False | True})"#
        );
    }
}
