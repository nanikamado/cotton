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
            Self::RecursiveAlias { alias, body } => {
                Self::RecursiveAlias {
                    alias,
                    body: body.replace_type_union(from, to),
                }
            }
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
        type_to_type(t, &Default::default(), &Default::default())
    }

    pub fn arrow(self, other: Self) -> Self {
        TypeUnit::Fn(self, other).into()
    }

    pub fn union(self, other: Self) -> Self {
        self.into_iter().chain(other.into_iter()).collect()
    }

    pub fn partition(self) -> Vec<Self> {
        let mut t = Vec::new();
        for tu in self.iter() {
            if tu.is_singleton() {
                t.push(tu.clone().into());
            } else {
                return vec![self];
            }
        }
        t.into_iter().collect()
    }
}

impl<'a> IncompleteType<'a> {
    pub fn all_type_variables(&self) -> FxHashSet<TypeVariable> {
        let IncompleteType {
            constructor,
            variable_requirements,
            subtype_relation,
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

    pub fn replace_num(
        self,
        from: TypeVariable,
        to: &Type<'a>,
    ) -> Self {
        let IncompleteType {
            constructor,
            variable_requirements,
            subtype_relation: subtype_relationship,
        } = self;
        IncompleteType {
            constructor: constructor.replace_num(from, to),
            variable_requirements: variable_requirements
                .into_iter()
                .map(|(name, t, id)| {
                    (name, t.replace_num(from, to), id)
                })
                .collect(),
            subtype_relation: subtype_relationship
                .into_iter()
                .map(|(a, b)| {
                    (a.replace_num(from, to), b.replace_num(from, to))
                })
                .collect(),
        }
    }
}
