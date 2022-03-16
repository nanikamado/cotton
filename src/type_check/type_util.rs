use crate::{
    ast1::{self, OpPrecedenceMap},
    ast2::{
        self,
        types::{Type, TypeMatchableRef, TypeUnit},
        IncompleteType, Requirements,
    },
};
use fxhash::FxHashMap;
use itertools::Itertools;
use std::collections::HashSet;
use TypeMatchableRef::{Fn, Normal};

use super::intrinsics::OP_PRECEDENCE;

impl TypeUnit {
    pub fn all_type_variables(&self) -> Vec<usize> {
        match self {
            TypeUnit::Normal { args, .. } => args
                .iter()
                .flat_map(|t| t.all_type_variables())
                .collect(),
            TypeUnit::Fn(arg, ret) => arg
                .all_type_variables()
                .into_iter()
                .chain(ret.all_type_variables().into_iter())
                .collect(),
            TypeUnit::Variable(i) => std::iter::once(*i).collect(),
            TypeUnit::RecursiveAlias { alias, body } => {
                let mut s = body.all_type_variables();
                s.remove(alias);
                s.into_iter().collect()
            }
        }
    }

    pub fn replace_num(self, from: usize, to: &Type) -> Type {
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
            Self::RecursiveAlias { alias, body } => {
                (Self::RecursiveAlias {
                    alias,
                    body: body.replace_num(from, to),
                })
                .into()
            }
        }
    }

    pub fn replace_type(
        self,
        from: &TypeUnit,
        to: &TypeUnit,
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
            Self::RecursiveAlias { alias, body } => {
                Self::RecursiveAlias {
                    alias,
                    body: body.replace_type(from, to),
                }
            }
        }
    }

    pub fn replace_type_union(
        self,
        from: &Type,
        to: &TypeUnit,
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
            Self::RecursiveAlias { alias, body } => {
                Self::RecursiveAlias {
                    alias,
                    body: body.replace_type_union(from, to),
                }
            }
        }
    }

    pub fn contains_num(&self, variable_num: usize) -> bool {
        match self {
            Self::Normal { args, .. } => {
                args.iter().any(|c| c.contains_num(variable_num))
            }
            Self::Fn(a, r) => {
                a.contains_num(variable_num)
                    || r.contains_num(variable_num)
            }
            Self::Variable(n) => *n == variable_num,
            Self::RecursiveAlias { alias: _, body } => {
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
}

impl Type {
    pub fn all_type_variables(&self) -> HashSet<usize> {
        self.iter().flat_map(|t| t.all_type_variables()).collect()
    }

    pub fn replace_num(self, from: usize, to: &Self) -> Self {
        self.into_iter()
            .flat_map(|t| t.replace_num(from, to).into_iter())
            .collect()
    }

    pub fn replace_type(
        self,
        from: &TypeUnit,
        to: &TypeUnit,
    ) -> Self {
        self.into_iter().map(|t| t.replace_type(from, to)).collect()
    }

    pub fn replace_type_union(
        self,
        from: &Type,
        to: &TypeUnit,
    ) -> Self {
        if self == *from {
            to.clone().into()
        } else {
            self.into_iter()
                .map(|t| t.replace_type_union(from, to))
                .collect()
        }
    }

    pub fn is_singleton(&self) -> bool {
        match self.matchable_ref() {
            Normal { args, .. } => {
                args.iter().all(|c| c.is_singleton())
            }
            Fn(a, b) => a.is_singleton() && b.is_singleton(),
            _ => false,
        }
    }

    pub fn contains_num(&self, variable_num: usize) -> bool {
        self.iter().any(|t| t.contains_num(variable_num))
    }
}

impl IncompleteType {
    fn all_type_variables(&self) -> HashSet<usize> {
        let IncompleteType {
            constructor,
            requirements:
                Requirements {
                    variable_requirements,
                    subtype_relation,
                },
        } = self;
        variable_requirements
            .iter()
            .flat_map(|(_, t, _)| t.all_type_variables())
            .chain(subtype_relation.iter().flat_map(|(a, b)| {
                let mut a = a.all_type_variables();
                a.extend(b.all_type_variables());
                a
            }))
            .chain(constructor.all_type_variables())
            .collect()
    }

    pub fn change_variable_num(mut self) -> Self {
        let anos = self.all_type_variables();
        for a in anos {
            self =
                self.replace_num(a, &TypeUnit::new_variable().into())
        }
        self
    }

    pub fn replace_num(self, from: usize, to: &Type) -> Self {
        let IncompleteType {
            constructor,
            requirements:
                Requirements {
                    variable_requirements,
                    subtype_relation: subtype_relationship,
                },
        } = self;
        IncompleteType {
            constructor: constructor.replace_num(from, to),
            requirements: Requirements {
                variable_requirements: variable_requirements
                    .into_iter()
                    .map(|(name, t, id)| {
                        (name, t.replace_num(from, to), id)
                    })
                    .collect(),
                subtype_relation: subtype_relationship
                    .into_iter()
                    .map(|(a, b)| {
                        (
                            a.replace_num(from, to),
                            b.replace_num(from, to),
                        )
                    })
                    .collect(),
            },
        }
    }
}

impl Requirements {
    pub fn merge(self, other: Self) -> Self {
        Self {
            variable_requirements: [
                self.variable_requirements,
                other.variable_requirements,
            ]
            .concat(),
            subtype_relation: {
                let mut s = self.subtype_relation;
                s.extend(other.subtype_relation);
                s
            },
        }
    }
}

pub fn construct_type(s: &str) -> Type {
    construct_type_with_variables(s, &[], &Default::default())
}

pub fn construct_type_with_variables(
    s: &str,
    type_variable_names: &[&str],
    data_decl_map: &FxHashMap<&str, ast2::decl_id::DeclId>,
) -> Type {
    let (_, type_seq) = crate::parse::infix_type_sequence(s).unwrap();
    let type_seq: ast1::TypeOperatorSequence = ast1::op_sequence(
        type_seq,
        &OpPrecedenceMap::new(OP_PRECEDENCE.clone()),
    );
    let t = ast1::infix_op_sequence(type_seq);
    crate::ast2::type_to_type(
        t,
        data_decl_map,
        &type_variable_names
            .iter()
            .map(|&name| {
                (name.to_string(), TypeUnit::new_variable_num())
            })
            .collect(),
    )
}
