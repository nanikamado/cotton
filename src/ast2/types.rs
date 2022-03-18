pub use self::type_type::Type;
use crate::ast2::TypeId;
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

pub mod type_type {
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
        pub fn iter(
            &self,
        ) -> std::collections::btree_set::Iter<'_, TypeUnit<'a>>
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
