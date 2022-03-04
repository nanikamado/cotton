pub use self::type_type::Type;
use itertools::Itertools;
use std::{collections::BTreeSet, fmt::Display};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchable {
    Normal { name: String, args: Vec<Type> },
    Fn(Type, Type),
    Union(Type),
    Variable(usize),
    Empty,
    RecursiveAlias { alias: usize, body: Type },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchableRef<'a> {
    Normal { name: &'a str, args: &'a Vec<Type> },
    Fn(&'a Type, &'a Type),
    Union(&'a BTreeSet<TypeUnit>),
    Variable(usize),
    Empty,
    RecursiveAlias { alias: usize, body: &'a Type },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeUnit {
    Normal { name: String, args: Vec<Type> },
    Fn(Type, Type),
    Variable(usize),
    RecursiveAlias { alias: usize, body: Type },
}

pub mod type_type {
    use std::{collections::BTreeSet, iter::FromIterator};

    use super::{TypeMatchable, TypeMatchableRef, TypeUnit};

    #[derive(
        Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default,
    )]
    pub struct Type(BTreeSet<TypeUnit>);

    impl IntoIterator for Type {
        type Item = TypeUnit;

        type IntoIter =
            std::collections::btree_set::IntoIter<Self::Item>;

        fn into_iter(self) -> Self::IntoIter {
            self.0.into_iter()
        }
    }

    impl Type {
        pub fn iter(
            &self,
        ) -> std::collections::btree_set::Iter<'_, TypeUnit> {
            self.0.iter()
        }

        pub fn contains(&self, value: &Type) -> bool {
            self.0.is_superset(&value.0)
        }

        pub fn merge(self, other: Self) -> Self {
            let mut u = self.0;
            u.extend(other.0);
            Type(u)
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }

        pub fn matchable(self) -> TypeMatchable {
            use TypeMatchable::*;
            match self.0.len() {
                0 => Empty,
                1 => match self.0.into_iter().next().unwrap() {
                    TypeUnit::Normal { name, args } => {
                        Normal { name, args }
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
                    TypeUnit::Normal { name, args } => {
                        Normal { name, args }
                    }
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

    impl FromIterator<TypeUnit> for Type {
        fn from_iter<T: IntoIterator<Item = TypeUnit>>(
            iter: T,
        ) -> Self {
            Type(iter.into_iter().collect())
        }
    }

    impl From<TypeUnit> for Type {
        fn from(t: TypeUnit) -> Self {
            Type(std::iter::once(t).collect())
        }
    }
}

impl From<TypeMatchable> for Type {
    fn from(m: TypeMatchable) -> Self {
        match m {
            TypeMatchable::Normal { name, args } => {
                TypeUnit::Normal { name, args }.into()
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

impl Display for Type {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        use TypeMatchableRef::*;
        match self.matchable_ref() {
            Normal { name, args } => {
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

impl Display for TypeUnit {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        use TypeUnit::*;
        match self {
            Normal { name, args } => {
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
