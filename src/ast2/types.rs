pub use self::type_type::Type;
use crate::ast2::TypeId;
use fxhash::FxHashSet;
use itertools::Itertools;
use std::{collections::BTreeSet, fmt::Display};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchable<'a> {
    Normal {
        name: &'a str,
        args: Vec<Type<'a>>,
        id: TypeId<'a>,
    },
    Fn(Type<'a>, Type<'a>),
    Union(Type<'a>),
    Variable(usize),
    Empty,
    RecursiveAlias {
        alias: usize,
        body: Type<'a>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchableRef<'a> {
    Normal {
        name: &'a str,
        args: &'a Vec<Type<'a>>,
        id: TypeId<'a>,
    },
    Fn(&'a Type<'a>, &'a Type<'a>),
    Union(&'a BTreeSet<TypeUnit<'a>>),
    Variable(usize),
    Empty,
    RecursiveAlias {
        alias: usize,
        body: &'a Type<'a>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeUnit<'a> {
    Normal {
        name: &'a str,
        args: Vec<Type<'a>>,
        id: TypeId<'a>,
    },
    Fn(Type<'a>, Type<'a>),
    Variable(usize),
    RecursiveAlias {
        alias: usize,
        body: Type<'a>,
    },
}

mod type_type {
    use std::{collections::BTreeSet, iter::FromIterator};

    use super::{TypeMatchable, TypeMatchableRef, TypeUnit};

    #[derive(
        Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default,
    )]
    pub struct Type<'a>(BTreeSet<TypeUnit<'a>>);

    impl<'a> IntoIterator for Type<'a> {
        type Item = TypeUnit<'a>;

        type IntoIter =
            std::collections::btree_set::IntoIter<Self::Item>;

        fn into_iter(self) -> Self::IntoIter {
            self.0.into_iter()
        }
    }

    impl<'a> Type<'a> {
        pub fn iter<'b>(
            &'b self,
        ) -> std::collections::btree_set::Iter<'b, TypeUnit<'a>>
        {
            self.0.iter()
        }

        pub fn contains(&self, value: &Type) -> bool {
            self.0.is_superset(&value.0)
        }

        // pub fn merge(self, other: Self) -> Self {
        //     let mut u = self.0;
        //     u.extend(other.0);
        //     Type(u)
        // }

        pub fn len(&self) -> usize {
            self.0.len()
        }

        pub fn matchable(self) -> TypeMatchable<'a> {
            use TypeMatchable::*;
            match self.0.len() {
                0 => Empty,
                1 => match self.0.into_iter().next().unwrap() {
                    TypeUnit::Normal { name, args, id } => {
                        Normal { name, args, id }
                    }
                    TypeUnit::Fn(arg, ret) => Fn(arg, ret),
                    TypeUnit::Variable(i) => Variable(i),
                    TypeUnit::RecursiveAlias { alias, body } => {
                        RecursiveAlias { alias, body }
                    }
                },
                _ => TypeMatchable::Union(self),
            }
        }

        pub fn matchable_ref(&self) -> TypeMatchableRef {
            use TypeMatchableRef::*;
            match self.0.len() {
                0 => Empty,
                1 => match self.0.iter().next().unwrap() {
                    TypeUnit::Normal { name, args, id } => Normal {
                        name,
                        args,
                        id: *id,
                    },
                    TypeUnit::Fn(arg, ret) => Fn(arg, ret),
                    TypeUnit::Variable(i) => Variable(*i),
                    TypeUnit::RecursiveAlias { alias, body } => {
                        RecursiveAlias {
                            alias: *alias,
                            body,
                        }
                    }
                },
                _ => Union(&self.0),
            }
        }
    }

    impl<'a> FromIterator<TypeUnit<'a>> for Type<'a> {
        fn from_iter<T: IntoIterator<Item = TypeUnit<'a>>>(
            iter: T,
        ) -> Self {
            Type(iter.into_iter().collect())
        }
    }

    impl<'a> From<TypeUnit<'a>> for Type<'a> {
        fn from(t: TypeUnit<'a>) -> Self {
            Type(std::iter::once(t).collect())
        }
    }
}

impl<'a> From<TypeMatchable<'a>> for Type<'a> {
    fn from(m: TypeMatchable<'a>) -> Self {
        match m {
            TypeMatchable::Normal { name, args, id } => {
                TypeUnit::Normal { name, args, id }.into()
            }
            TypeMatchable::Fn(a, b) => TypeUnit::Fn(a, b).into(),
            TypeMatchable::Union(u) => u,
            TypeMatchable::Variable(i) => {
                TypeUnit::Variable(i).into()
            }
            TypeMatchable::Empty => Default::default(),
            TypeMatchable::RecursiveAlias { alias, body } => {
                TypeUnit::RecursiveAlias { alias, body }.into()
            }
        }
    }
}

impl<'a> TypeConstructor<'a> for Type<'a> {
    fn all_type_variables(&self) -> fxhash::FxHashSet<usize> {
        self.iter().flat_map(|t| t.all_type_variables()).collect()
    }

    fn replace_num(self, from: usize, to: &Self) -> Self {
        self.into_iter()
            .flat_map(|t| t.replace_num(from, to).into_iter())
            .collect()
    }

    fn covariant_type_variables(&self) -> Vec<usize> {
        match self.matchable_ref() {
            TypeMatchableRef::Fn(a, r) => marge_vec(
                r.covariant_type_variables(),
                a.contravariant_type_variables(),
            ),
            TypeMatchableRef::Normal { args, .. } => args
                .iter()
                .flat_map(TypeConstructor::covariant_type_variables)
                .collect(),
            TypeMatchableRef::Union(cs) => cs
                .iter()
                .map(|c| {
                    Type::from(c.clone()).covariant_type_variables()
                })
                .concat(),
            TypeMatchableRef::Variable(n) => {
                [n].iter().copied().collect()
            }
            TypeMatchableRef::Empty => Default::default(),
            TypeMatchableRef::RecursiveAlias { alias, body } => {
                let mut vs: FxHashSet<_> = body
                    .covariant_type_variables()
                    .into_iter()
                    .collect();
                vs.remove(&alias);
                vs.into_iter().collect()
            }
        }
    }

    fn contravariant_type_variables(&self) -> Vec<usize> {
        match self.matchable_ref() {
            TypeMatchableRef::Fn(a, r) => marge_vec(
                a.covariant_type_variables(),
                r.contravariant_type_variables(),
            ),
            TypeMatchableRef::Normal { args, .. } => args
                .iter()
                .map(TypeConstructor::contravariant_type_variables)
                .concat(),
            TypeMatchableRef::Union(cs) => cs
                .iter()
                .map(|c| {
                    Type::from(c.clone())
                        .contravariant_type_variables()
                })
                .concat(),
            TypeMatchableRef::Variable(_)
            | TypeMatchableRef::Empty => Default::default(),
            TypeMatchableRef::RecursiveAlias { alias, body } => {
                let mut vs: FxHashSet<_> = body
                    .contravariant_type_variables()
                    .into_iter()
                    .collect();
                vs.remove(&alias);
                vs.into_iter().collect()
            }
        }
    }

    fn find_recursive_alias(&self) -> Option<(usize, Type<'a>)> {
        self.iter().find_map(TypeUnit::find_recursive_alias)
    }

    fn replace_type(
        self,
        from: &TypeUnit<'a>,
        to: &TypeUnit<'a>,
    ) -> Self {
        self.into_iter().map(|t| t.replace_type(from, to)).collect()
    }

    fn replace_type_union(
        self,
        from: &Type,
        to: &TypeUnit<'a>,
    ) -> Self {
        if self == *from {
            to.clone().into()
        } else {
            self.into_iter()
                .map(|t| t.replace_type_union(from, to))
                .collect()
        }
    }
}

fn marge_vec<T>(mut a: Vec<T>, mut b: Vec<T>) -> Vec<T> {
    a.append(&mut b);
    a
}

pub trait TypeConstructor<'a>:
    Sized
    + std::fmt::Debug
    + std::fmt::Display
    + Eq
    + Clone
    + std::hash::Hash
{
    fn all_type_variables(&self) -> FxHashSet<usize>;
    fn replace_num(self, from: usize, to: &Type<'a>) -> Self;
    fn covariant_type_variables(&self) -> Vec<usize>;
    fn contravariant_type_variables(&self) -> Vec<usize>;
    fn find_recursive_alias(&self) -> Option<(usize, Type<'a>)>;
    fn replace_type(
        self,
        from: &TypeUnit<'a>,
        to: &TypeUnit<'a>,
    ) -> Self;
    fn replace_type_union(
        self,
        from: &Type,
        to: &TypeUnit<'a>,
    ) -> Self;
}

impl<'a> TypeUnit<'a> {
    fn find_recursive_alias(&self) -> Option<(usize, Type<'a>)> {
        match self {
            TypeUnit::Normal { args, .. } => {
                args.iter().find_map(Type::find_recursive_alias)
            }
            TypeUnit::Fn(a, r) => {
                [a, r].iter().find_map(|a| a.find_recursive_alias())
            }
            TypeUnit::Variable(_) => None,
            TypeUnit::RecursiveAlias { alias, body } => {
                Some((*alias, body.clone()))
            }
        }
    }
}

impl Display for Type<'_> {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        use TypeMatchableRef::*;
        match self.matchable_ref() {
            Normal { name, args, .. } => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(
                        f,
                        "{}({})",
                        name,
                        args.iter()
                            .map(|c| format!("{}", c))
                            .join(", ")
                    )
                }
            }
            Fn(arg, rtn) => {
                if let Fn(_, _) = arg.matchable_ref() {
                    write!(f, "({}) -> {}", arg, rtn)
                } else {
                    write!(f, "{} -> {}", arg, rtn)
                }
            }
            Union(a) => write!(
                f,
                "{{{}}}",
                a.iter()
                    .map(|t| {
                        if let TypeUnit::Fn(_, _) = t {
                            format!("({})", t)
                        } else {
                            format!("{}", t)
                        }
                    })
                    .join(" | ")
            ),
            Variable(n) => write!(f, "t{}", n),
            Empty => write!(f, "∅"),
            RecursiveAlias { alias, body } => {
                write!(f, "rec[t{} = {}]", alias, *body)
            }
        }
    }
}

impl Display for TypeUnit<'_> {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        use TypeUnit::*;
        match self {
            Normal { name, args, .. } => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(
                        f,
                        "{}({})",
                        name,
                        args.iter()
                            .map(|c| format!("{}", c))
                            .join(", ")
                    )
                }
            }
            Fn(arg, rtn) => {
                if let TypeMatchableRef::Fn(_, _) =
                    arg.matchable_ref()
                {
                    write!(f, "({}) -> {}", arg, rtn)
                } else {
                    write!(f, "{} -> {}", arg, rtn)
                }
            }
            Variable(n) => write!(f, "t{}", n),
            RecursiveAlias { alias, body } => {
                write!(f, "rec[t{} = {}]", alias, *body)
            }
        }
    }
}