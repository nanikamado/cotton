use std::{collections::BTreeSet, iter::FromIterator};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchable {
    Normal(String, Vec<Type>),
    Fn(Type, Type),
    Union(Type),
    Variable(usize),
    Empty,
    RecursiveAlias { alias: usize, body: Type },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchableRef<'a> {
    Normal(&'a str, &'a Vec<Type>),
    Fn(&'a Type, &'a Type),
    Union(&'a BTreeSet<TypeUnit>),
    Variable(usize),
    Empty,
    RecursiveAlias { alias: usize, body: &'a Type },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeUnit {
    Normal(String, Vec<Type>),
    Fn(Type, Type),
    Variable(usize),
    RecursiveAlias { alias: usize, body: Type },
}

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
                TypeUnit::Normal(name, ts) => Normal(name, ts),
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
                TypeUnit::Normal(name, ts) => Normal(name, &ts),
                TypeUnit::Fn(arg, ret) => Fn(&arg, &ret),
                TypeUnit::Variable(i) => Variable(*i),
                TypeUnit::RecursiveAlias { alias, body } => {
                    RecursiveAlias {
                        alias: *alias,
                        body: &body,
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

impl From<TypeMatchable> for Type {
    fn from(m: TypeMatchable) -> Self {
        match m {
            TypeMatchable::Normal(name, cs) => {
                TypeUnit::Normal(name, cs).into()
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
