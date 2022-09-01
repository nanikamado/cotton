pub use self::type_type::Type;
pub use self::type_unit::TypeUnit;
pub use self::type_unit::TypeVariable;
use crate::ast_step2::TypeId;
use crate::ast_step3::TypeVariableMap;
use fxhash::FxHashSet;
use itertools::Itertools;
use std::{collections::BTreeSet, fmt::Display};

use super::IncompleteType;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchable<'a> {
    Normal {
        name: &'a str,
        args: Vec<Type<'a>>,
        id: TypeId,
    },
    Fn(Type<'a>, Type<'a>),
    Union(Type<'a>),
    Variable(TypeVariable),
    Empty,
    RecursiveAlias {
        body: Type<'a>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchableRef<'a, 'b> {
    Normal {
        name: &'a str,
        args: &'b Vec<Type<'a>>,
        id: TypeId,
    },
    Fn(&'b Type<'a>, &'b Type<'a>),
    Union(&'b BTreeSet<TypeUnit<'a>>),
    Variable(TypeVariable),
    Empty,
    RecursiveAlias {
        body: &'b Type<'a>,
    },
}

mod type_unit {
    use super::Type;
    use crate::ast_step2::TypeId;
    use std::{cell::Cell, fmt::Display};

    #[derive(
        Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
    )]
    pub struct TypeVariableInner(usize);

    #[derive(
        Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
    )]
    pub enum TypeVariable {
        Normal(TypeVariableInner),
        RecursiveIndex(usize),
    }

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum TypeUnit<'a> {
        Normal {
            name: &'a str,
            args: Vec<Type<'a>>,
            id: TypeId,
        },
        Fn(Type<'a>, Type<'a>),
        Variable(TypeVariable),
        RecursiveAlias {
            body: Type<'a>,
        },
    }

    impl Default for TypeVariable {
        fn default() -> Self {
            VARIABLE_COUNT.with(|c| {
                let t = c.get();
                c.set(t + 1);
                TypeVariable::Normal(TypeVariableInner(t))
            })
        }
    }

    impl TypeVariable {
        pub fn new() -> Self {
            Self::default()
        }

        pub fn recursive_index_zero() -> Self {
            Self::RecursiveIndex(0)
        }

        pub fn increment_recursive_index(self) -> Self {
            match self {
                TypeVariable::Normal(n) => TypeVariable::Normal(n),
                TypeVariable::RecursiveIndex(n) => {
                    TypeVariable::RecursiveIndex(n + 1)
                }
            }
        }

        pub fn increment_recursive_index_with_bound(
            self,
            greater_than_or_equal_to: usize,
        ) -> Self {
            match self {
                TypeVariable::RecursiveIndex(n)
                    if n >= greater_than_or_equal_to =>
                {
                    TypeVariable::RecursiveIndex(n + 1)
                }
                n => n,
            }
        }

        pub fn decrement_recursive_index_with_bound(
            self,
            greater_than_or_equal_to: usize,
        ) -> Self {
            match self {
                TypeVariable::RecursiveIndex(n)
                    if n >= greater_than_or_equal_to && n >= 1 =>
                {
                    TypeVariable::RecursiveIndex(n - 1)
                }
                n => n,
            }
        }

        pub fn is_recursive_index(self) -> bool {
            match self {
                TypeVariable::Normal(_) => false,
                TypeVariable::RecursiveIndex(_) => true,
            }
        }
    }

    impl TypeUnit<'_> {
        pub fn new_variable() -> Self {
            Self::Variable(TypeVariable::new())
        }
    }

    thread_local! {
        static VARIABLE_COUNT: Cell<usize> = Cell::new(0);
    }

    impl Display for TypeVariable {
        fn fmt(
            &self,
            f: &mut std::fmt::Formatter<'_>,
        ) -> std::fmt::Result {
            match self {
                TypeVariable::Normal(TypeVariableInner(n)) => {
                    write!(f, "t{}", n)
                }
                TypeVariable::RecursiveIndex(n) => {
                    write!(f, "d{}", n)
                }
            }
        }
    }
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

        pub fn contains_unit(&self, value: &TypeUnit) -> bool {
            self.0.contains(value)
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
                    TypeUnit::RecursiveAlias { body } => {
                        RecursiveAlias { body }
                    }
                },
                _ => TypeMatchable::Union(self),
            }
        }

        pub fn matchable_ref<'b>(
            &'b self,
        ) -> TypeMatchableRef<'a, 'b> {
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
                    TypeUnit::RecursiveAlias { body } => {
                        RecursiveAlias { body }
                    }
                },
                _ => Union(&self.0),
            }
        }

        pub fn union_in_place(&mut self, mut other: Self) {
            self.0.append(&mut other.0);
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
            TypeMatchable::RecursiveAlias { body } => {
                TypeUnit::RecursiveAlias { body }.into()
            }
        }
    }
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SingleTypeConstructor<'a> {
    pub type_: Type<'a>,
    pub contravariant_candidates_from_annotation:
        Option<Vec<TypeVariable>>,
}

impl<'a> TypeConstructor<'a> for SingleTypeConstructor<'a> {
    fn all_type_variables(&self) -> fxhash::FxHashSet<TypeVariable> {
        self.type_.all_type_variables()
    }

    fn all_type_variables_vec(&self) -> Vec<TypeVariable> {
        self.type_.all_type_variables_vec()
    }

    fn replace_num(
        mut self,
        from: TypeVariable,
        to: &type_type::Type<'a>,
    ) -> Self {
        self.type_ = self.type_.replace_num(from, to);
        self
    }

    fn replace_num_with_update_flag(
        mut self,
        from: TypeVariable,
        to: &Type<'a>,
    ) -> (Self, bool) {
        let updated;
        (self.type_, updated) =
            self.type_.replace_num_with_update_flag(from, to);
        (self, updated)
    }

    fn covariant_type_variables(&self) -> Vec<TypeVariable> {
        if self.contravariant_candidates_from_annotation.is_some() {
            self.all_type_variables().into_iter().collect()
        } else {
            self.type_.covariant_type_variables()
        }
    }

    fn contravariant_type_variables(&self) -> Vec<TypeVariable> {
        if let Some(cs) =
            self.contravariant_candidates_from_annotation.as_ref()
        {
            cs.clone()
        } else {
            self.type_.contravariant_type_variables()
        }
    }

    fn find_recursive_alias(&self) -> Option<Type<'a>> {
        self.type_.find_recursive_alias()
    }

    fn replace_type(
        mut self,
        from: &TypeUnit<'a>,
        to: &TypeUnit<'a>,
    ) -> Self {
        self.type_ = self.type_.replace_type(from, to);
        self
    }

    fn replace_type_union(
        mut self,
        from: &Type,
        to: &TypeUnit<'a>,
    ) -> Self {
        self.type_ = self.type_.replace_type_union(from, to);
        self
    }

    fn replace_type_union_with_update_flag(
        mut self,
        from: &Type,
        to: &TypeUnit<'a>,
    ) -> (Self, bool) {
        let updated;
        (self.type_, updated) =
            self.type_.replace_type_union_with_update_flag(from, to);
        (self, updated)
    }

    fn map_type<F: FnMut(Type<'a>) -> Type<'a>>(
        mut self,
        f: F,
    ) -> Self {
        self.type_ = self.type_.map_type(f);
        self
    }

    fn normalize_contravariant_candidates_from_annotation(
        mut self,
        map: &mut TypeVariableMap,
    ) -> Self {
        self.contravariant_candidates_from_annotation =
            self.contravariant_candidates_from_annotation.map(|a| {
                a.into_iter()
                    .flat_map(|t| {
                        if let TypeMatchable::Variable(v) =
                            map.find(t).matchable()
                        {
                            Some(v)
                        } else {
                            None
                        }
                    })
                    .collect()
            });
        self
    }
}

impl<'a> TypeConstructor<'a> for Type<'a> {
    fn all_type_variables(&self) -> fxhash::FxHashSet<TypeVariable> {
        self.all_type_variables_vec().into_iter().collect()
    }

    fn all_type_variables_vec(&self) -> Vec<TypeVariable> {
        self.iter().flat_map(|t| t.all_type_variables()).collect()
    }

    fn replace_num(self, from: TypeVariable, to: &Self) -> Self {
        self.replace_num_with_update_flag(from, to).0
    }

    fn replace_num_with_update_flag(
        self,
        from: TypeVariable,
        to: &Self,
    ) -> (Self, bool) {
        let mut updated = false;
        let t = self
            .into_iter()
            .flat_map(|t| {
                let (t2, u) =
                    t.replace_num_with_update_flag(from, to);
                updated |= u;
                t2.into_iter()
            })
            .collect();
        (t, updated)
    }

    fn covariant_type_variables(&self) -> Vec<TypeVariable> {
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
                vec![n]
            }
            TypeMatchableRef::Empty => Default::default(),
            TypeMatchableRef::RecursiveAlias { body } => {
                let mut vs: FxHashSet<_> = body
                    .covariant_type_variables()
                    .into_iter()
                    .collect();
                vs.remove(&TypeVariable::RecursiveIndex(0));
                vs.into_iter().collect()
            }
        }
    }

    fn contravariant_type_variables(&self) -> Vec<TypeVariable> {
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
            TypeMatchableRef::RecursiveAlias { body } => {
                let mut vs: FxHashSet<_> = body
                    .contravariant_type_variables()
                    .into_iter()
                    .collect();
                vs.remove(&TypeVariable::RecursiveIndex(0));
                vs.into_iter().collect()
            }
        }
    }

    fn find_recursive_alias(&self) -> Option<Type<'a>> {
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

    fn replace_type_union_with_update_flag(
        self,
        from: &Type,
        to: &TypeUnit<'a>,
    ) -> (Self, bool) {
        if self == *from {
            (to.clone().into(), true)
        } else {
            let mut updated = false;
            (
                self.into_iter()
                    .map(|t| {
                        let (t, u) = t
                            .replace_type_union_with_update_flag(
                                from, to,
                            );
                        updated |= u;
                        t
                    })
                    .collect(),
                updated,
            )
        }
    }

    fn map_type<F: FnMut(Type<'a>) -> Type<'a>>(
        self,
        mut f: F,
    ) -> Self {
        f(self)
    }

    fn normalize_contravariant_candidates_from_annotation(
        self,
        _map: &mut TypeVariableMap<'a>,
    ) -> Self {
        self
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
    fn all_type_variables(&self) -> FxHashSet<TypeVariable>;
    fn all_type_variables_vec(&self) -> Vec<TypeVariable>;
    fn replace_num(self, from: TypeVariable, to: &Type<'a>) -> Self;
    fn replace_num_with_update_flag(
        self,
        from: TypeVariable,
        to: &Type<'a>,
    ) -> (Self, bool);
    fn covariant_type_variables(&self) -> Vec<TypeVariable>;
    fn contravariant_type_variables(&self) -> Vec<TypeVariable>;
    fn find_recursive_alias(&self) -> Option<Type<'a>>;
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
    fn replace_type_union_with_update_flag(
        self,
        from: &Type,
        to: &TypeUnit<'a>,
    ) -> (Self, bool);
    fn map_type<F: FnMut(Type<'a>) -> Type<'a>>(self, f: F) -> Self;
    fn normalize_contravariant_candidates_from_annotation(
        self,
        map: &mut TypeVariableMap<'a>,
    ) -> Self;
}

impl<'a> TypeUnit<'a> {
    fn find_recursive_alias(&self) -> Option<Type<'a>> {
        match self {
            TypeUnit::Normal { args, .. } => {
                args.iter().find_map(Type::find_recursive_alias)
            }
            TypeUnit::Fn(a, r) => {
                [a, r].iter().find_map(|a| a.find_recursive_alias())
            }
            TypeUnit::Variable(_) => None,
            TypeUnit::RecursiveAlias { body } => Some(body.clone()),
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
            Variable(n) => write!(f, "{}", n),
            Empty => write!(f, "∅"),
            RecursiveAlias { body } => {
                write!(f, "rec[{}]", *body)
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
            Variable(n) => write!(f, "{}", n),
            RecursiveAlias { body } => {
                write!(f, "rec[{}]", *body)
            }
        }
    }
}

impl Display for SingleTypeConstructor<'_> {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "{} (annotation: {})",
            self.type_,
            self.contravariant_candidates_from_annotation
                .as_ref()
                .map(|v| format!(
                    "[{}]",
                    v.iter().map(|v| format!("{v}")).join(", ")
                ))
                .unwrap_or_else(|| "None".to_string())
        )
    }
}

impl<'a> From<IncompleteType<'a, SingleTypeConstructor<'a>>>
    for IncompleteType<'a, Type<'a>>
{
    fn from(
        t: IncompleteType<'a, SingleTypeConstructor<'a>>,
    ) -> Self {
        IncompleteType {
            constructor: t.constructor.type_,
            variable_requirements: t.variable_requirements,
            subtype_relations: t.subtype_relations,
            pattern_restrictions: t.pattern_restrictions,
            already_considered_relations: t
                .already_considered_relations,
        }
    }
}
