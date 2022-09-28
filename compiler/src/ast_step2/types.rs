pub use self::type_type::Type;
pub use self::type_unit::TypeUnit;
pub use self::type_unit::TypeVariable;
use super::SubtypeRelations;
use super::TypeWithEnv;
use crate::ast_step2::TypeId;
use crate::ast_step3::simplify_subtype_rel;
use crate::ast_step3::TypeVariableMap;
use crate::intrinsics::IntrinsicType;
use fxhash::FxHashSet;
use itertools::Itertools;
use std::fmt::Display;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchable<'a> {
    Fn(Type<'a>, Type<'a>),
    Union(Type<'a>),
    Variable(TypeVariable),
    Empty,
    RecursiveAlias { body: Type<'a> },
    Const { name: &'a str, id: TypeId },
    Tuple(Type<'a>, Type<'a>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchableRef<'a, 'b> {
    Fn(&'b Type<'a>, &'b Type<'a>),
    Union(&'b Type<'a>),
    Variable(TypeVariable),
    Empty,
    RecursiveAlias { body: &'b Type<'a> },
    Const { name: &'a str, id: TypeId },
    Tuple(&'b Type<'a>, &'b Type<'a>),
}

mod type_unit {
    use super::Type;
    use crate::ast_step2::TypeId;
    use std::{cell::Cell, fmt::Display};

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct TypeVariableInner(usize);

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum TypeVariable {
        Normal(TypeVariableInner),
        RecursiveIndex(usize),
    }

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum TypeUnit<'a> {
        Fn(Type<'a>, Type<'a>),
        Variable(TypeVariable),
        RecursiveAlias { body: Type<'a> },
        Const { name: &'a str, id: TypeId },
        Tuple(Type<'a>, Type<'a>),
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

        pub fn increment_recursive_index(self, n: i32) -> Self {
            match self {
                TypeVariable::Normal(n) => TypeVariable::Normal(n),
                TypeVariable::RecursiveIndex(m) => {
                    if n >= 0 {
                        TypeVariable::RecursiveIndex(m + n as usize)
                    } else {
                        TypeVariable::RecursiveIndex(m - (-n) as usize)
                    }
                }
            }
        }

        pub fn increment_recursive_index_with_bound(
            self,
            greater_than_or_equal_to: usize,
            n: i32,
        ) -> Self {
            match self {
                TypeVariable::RecursiveIndex(m)
                    if m >= greater_than_or_equal_to =>
                {
                    if n >= 0 {
                        TypeVariable::RecursiveIndex(m + n as usize)
                    } else {
                        TypeVariable::RecursiveIndex(m - (-n) as usize)
                    }
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
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
    use super::{TypeMatchable, TypeMatchableRef, TypeUnit};
    use crate::{
        ast_step2::{types::unwrap_or_clone, SubtypeRelations},
        ast_step3::simplify_subtype_rel,
    };
    use std::{iter, rc::Rc, vec};

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
    pub struct Type<'a>(Vec<Rc<TypeUnit<'a>>>);

    impl<'a> IntoIterator for Type<'a> {
        type Item = Rc<TypeUnit<'a>>;

        type IntoIter = vec::IntoIter<Self::Item>;

        fn into_iter(self) -> Self::IntoIter {
            self.0.into_iter()
        }
    }

    impl<'a> Type<'a> {
        pub fn iter<'b>(&'b self) -> std::slice::Iter<'b, Rc<TypeUnit<'a>>> {
            self.0.iter()
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }

        pub fn is_empty(&self) -> bool {
            self.0.is_empty()
        }

        pub fn matchable(mut self) -> TypeMatchable<'a> {
            use TypeMatchable::*;
            match self.0.len() {
                0 => Empty,
                1 => match unwrap_or_clone(self.0.pop().unwrap()) {
                    TypeUnit::Fn(arg, ret) => Fn(arg, ret),
                    TypeUnit::Variable(i) => Variable(i),
                    TypeUnit::RecursiveAlias { body } => {
                        RecursiveAlias { body }
                    }
                    TypeUnit::Const { name, id } => Const { name, id },
                    TypeUnit::Tuple(a, b) => Tuple(a, b),
                },
                _ => TypeMatchable::Union(self),
            }
        }

        pub fn matchable_ref<'b>(&'b self) -> TypeMatchableRef<'a, 'b> {
            use TypeMatchableRef::*;
            match self.0.len() {
                0 => Empty,
                1 => match &**self.0.first().unwrap() {
                    TypeUnit::Fn(arg, ret) => Fn(arg, ret),
                    TypeUnit::Variable(i) => Variable(*i),
                    TypeUnit::RecursiveAlias { body } => {
                        RecursiveAlias { body }
                    }
                    TypeUnit::Const { name, id } => Const { name, id: *id },
                    TypeUnit::Tuple(a, b) => Tuple(a, b),
                },
                _ => Union(self),
            }
        }

        pub fn union_in_place(&mut self, other: Self) {
            for t in other {
                self.insert(t);
            }
        }

        fn insert_to_vec(&mut self, other: Rc<TypeUnit<'a>>) {
            let i = self.0.partition_point(|x| *x < other);
            self.0.insert(i, other);
        }

        fn push_tuple(&mut self, t: TypeUnit<'a>) {
            match t {
                TypeUnit::Tuple(t_head, t_tail) => {
                    let mut m = Vec::with_capacity(self.0.len());
                    let mut merged = false;
                    while let Some(u) = self.0.pop() {
                        match unwrap_or_clone(u) {
                            TypeUnit::Tuple(u_head, u_tail)
                                if t_tail == u_tail =>
                            {
                                self.0.push(Rc::new(TypeUnit::Tuple(
                                    t_head.clone().union(u_head),
                                    u_tail,
                                )));
                                merged = true;
                                break;
                            }
                            t => {
                                m.push(Rc::new(t));
                            }
                        }
                    }
                    self.0.append(&mut m);
                    if !merged {
                        self.0.push(Rc::new(TypeUnit::Tuple(t_head, t_tail)));
                    }
                    self.0.sort_unstable();
                }
                t => {
                    self.insert_to_vec(Rc::new(t));
                }
            }
        }

        pub fn insert_with_already_considered_relations(
            &mut self,
            other: Rc<TypeUnit<'a>>,
            already_considered_relations: Option<SubtypeRelations<'a>>,
        ) {
            if other.contains_empty_in_covariant_candidate() {
                return;
            }
            if let Some(u) = self.0.pop() {
                let (u, t1, t2) = unwrap_or_clone(u).merge_union_with(
                    unwrap_or_clone(other),
                    already_considered_relations,
                );
                if let Some(t2) = t2 {
                    self.insert(Rc::new(t2)); //
                }
                if let Some(u) = u {
                    self.push_tuple(u);
                }
                if let Some(t1) = t1 {
                    self.push_tuple(t1);
                }
            } else {
                self.insert_to_vec(other);
            }
        }

        pub fn insert(&mut self, other: Rc<TypeUnit<'a>>) {
            self.insert_with_already_considered_relations(other, None);
        }

        pub fn increment_recursive_index(
            self,
            greater_than_or_equal_to: usize,
            n: i32,
        ) -> Self {
            Type(
                self.0
                    .into_iter()
                    .map(|t| {
                        Rc::new(unwrap_or_clone(t).increment_recursive_index(
                            greater_than_or_equal_to,
                            n,
                        ))
                    })
                    .collect(),
            )
        }
    }

    impl<'a> From<TypeUnit<'a>> for Type<'a> {
        fn from(t: TypeUnit<'a>) -> Self {
            Type(iter::once(Rc::new(t)).collect())
        }
    }

    impl<'a> From<Rc<TypeUnit<'a>>> for Type<'a> {
        fn from(t: Rc<TypeUnit<'a>>) -> Self {
            Type(iter::once(t).collect())
        }
    }

    impl<'a> TypeUnit<'a> {
        pub fn merge_union_with(
            self,
            other: Self,
            mut already_considered_relations: Option<SubtypeRelations<'a>>,
        ) -> (Option<Self>, Option<Self>, Option<Self>) {
            use TypeUnit::*;
            match (self, other) {
                (Tuple(a1, a2), Tuple(b1, b2)) => {
                    let (da, i, db) = a1.intersection_and_difference(b1);
                    (
                        if da.is_empty() {
                            None
                        } else {
                            Some(Tuple(da, a2.clone()))
                        },
                        if i.is_empty() {
                            None
                        } else {
                            Some(Tuple(i, a2.union(b2.clone())))
                        },
                        if db.is_empty() {
                            None
                        } else {
                            Some(Tuple(db, b2))
                        },
                    )
                }
                (
                    a @ (Variable(_) | Const { .. }),
                    b @ (Variable(_) | Const { .. }),
                ) => {
                    if a == b {
                        (None, Some(a), None)
                    } else {
                        (Some(a), None, Some(b))
                    }
                }
                (Fn(a1, a2), Fn(b1, b2)) => {
                    if a1 == b1 {
                        (None, Some(Fn(a1, a2.union(b2))), None)
                    } else {
                        (Some(Fn(a1, a2)), None, Some(Fn(b1, b2)))
                    }
                }
                (a @ RecursiveAlias { .. }, b) => {
                    let r = simplify_subtype_rel(
                        b.clone().into(),
                        a.clone().into(),
                        already_considered_relations.as_mut(),
                    );
                    if r.map(|r| r.is_empty()).unwrap_or(false) {
                        (None, Some(a), None)
                    } else {
                        (Some(a), None, Some(b))
                    }
                }
                (a, b @ RecursiveAlias { .. }) => {
                    let r = simplify_subtype_rel(
                        a.clone().into(),
                        b.clone().into(),
                        already_considered_relations.as_mut(),
                    );
                    if r.map(|r| r.is_empty()).unwrap_or(false) {
                        (None, Some(b), None)
                    } else {
                        (Some(a), None, Some(b))
                    }
                }
                (
                    a @ Fn(_, _),
                    b @ (Variable(_) | Const { .. } | Tuple(_, _)),
                )
                | (
                    a @ Tuple(_, _),
                    b @ (Variable(_) | Const { .. } | Fn(_, _)),
                )
                | (
                    a @ (Variable(_) | Const { .. }),
                    b @ (Fn(_, _) | Tuple(_, _)),
                ) => (Some(a), None, Some(b)),
            }
        }

        pub fn contains_empty_in_covariant_candidate(&self) -> bool {
            match self {
                TypeUnit::Fn(_, a) => a.is_empty(),
                TypeUnit::Tuple(a, b) => a.is_empty() || b.is_empty(),
                TypeUnit::RecursiveAlias { body } => body.is_empty(),
                TypeUnit::Const { .. } | TypeUnit::Variable(_) => false,
            }
        }

        fn increment_recursive_index(
            self,
            greater_than_or_equal_to: usize,
            n: i32,
        ) -> Self {
            match self {
                TypeUnit::Fn(a, b) => TypeUnit::Fn(
                    a.increment_recursive_index(greater_than_or_equal_to, n),
                    b.increment_recursive_index(greater_than_or_equal_to, n),
                ),
                TypeUnit::Variable(v) => {
                    TypeUnit::Variable(v.increment_recursive_index_with_bound(
                        greater_than_or_equal_to,
                        n,
                    ))
                }
                TypeUnit::RecursiveAlias { body } => TypeUnit::RecursiveAlias {
                    body: body.increment_recursive_index(
                        greater_than_or_equal_to + 1,
                        n,
                    ),
                },
                TypeUnit::Const { name, id } => TypeUnit::Const { name, id },
                TypeUnit::Tuple(a, b) => TypeUnit::Tuple(
                    a.increment_recursive_index(greater_than_or_equal_to, n),
                    b.increment_recursive_index(greater_than_or_equal_to, n),
                ),
            }
        }
    }
}

impl<'a> Type<'a> {
    #[allow(clippy::wrong_self_convention)]
    pub fn is_subtype_of(self, other: Self) -> bool {
        let r = simplify_subtype_rel(self, other, None);
        r.map(|v| v.is_empty()).unwrap_or(false)
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn is_subtype_of_with_rels(
        self,
        other: Self,
        already_considered_relations: Option<&mut SubtypeRelations<'a>>,
    ) -> bool {
        let r = simplify_subtype_rel(self, other, already_considered_relations);
        r.map(|v| v.is_empty()).unwrap_or(false)
    }
}

impl<'a> FromIterator<TypeUnit<'a>> for Type<'a> {
    fn from_iter<T: IntoIterator<Item = TypeUnit<'a>>>(iter: T) -> Self {
        let mut t = Type::default();
        for u in iter.into_iter() {
            t.insert_with_already_considered_relations(
                Rc::new(u),
                Some(Default::default()),
            );
        }
        t
    }
}

impl<'a> FromIterator<Rc<TypeUnit<'a>>> for Type<'a> {
    fn from_iter<T: IntoIterator<Item = Rc<TypeUnit<'a>>>>(iter: T) -> Self {
        let mut t = Type::default();
        for u in iter.into_iter() {
            t.insert_with_already_considered_relations(
                u,
                Some(Default::default()),
            );
        }
        t
    }
}

impl<'a> From<TypeMatchable<'a>> for Type<'a> {
    fn from(m: TypeMatchable<'a>) -> Self {
        match m {
            TypeMatchable::Fn(a, b) => TypeUnit::Fn(a, b).into(),
            TypeMatchable::Union(u) => u,
            TypeMatchable::Variable(i) => TypeUnit::Variable(i).into(),
            TypeMatchable::Empty => Default::default(),
            TypeMatchable::RecursiveAlias { body } => {
                TypeUnit::RecursiveAlias { body }.into()
            }
            TypeMatchable::Const { name, id } => {
                TypeUnit::Const { name, id }.into()
            }
            TypeMatchable::Tuple(a, b) => TypeUnit::Tuple(a, b).into(),
        }
    }
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SingleTypeConstructor<'a> {
    pub type_: Type<'a>,
    pub contravariant_candidates_from_annotation: Option<Vec<TypeVariable>>,
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
        recursive_alias_depth: usize,
    ) -> (Self, bool) {
        let updated;
        (self.type_, updated) = self.type_.replace_num_with_update_flag(
            from,
            to,
            recursive_alias_depth,
        );
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
        if let Some(cs) = self.contravariant_candidates_from_annotation.as_ref()
        {
            cs.clone()
        } else {
            self.type_.contravariant_type_variables()
        }
    }

    fn find_recursive_alias(&self) -> Option<&Type<'a>> {
        self.type_.find_recursive_alias()
    }

    fn replace_type(mut self, from: &TypeUnit<'a>, to: &TypeUnit<'a>) -> Self {
        self.type_ = self.type_.replace_type(from, to);
        self
    }

    fn replace_type_union(mut self, from: &Type, to: &TypeUnit<'a>) -> Self {
        self.type_ = self.type_.replace_type_union(from, to);
        self
    }

    fn replace_type_union_with_update_flag(
        mut self,
        from: &Type,
        to: &TypeUnit<'a>,
        recursive_alias_depth: usize,
    ) -> (Self, bool) {
        let updated;
        (self.type_, updated) = self.type_.replace_type_union_with_update_flag(
            from,
            to,
            recursive_alias_depth,
        );
        (self, updated)
    }

    fn map_type<F: FnMut(Type<'a>) -> Type<'a>>(mut self, f: F) -> Self {
        self.type_ = self.type_.map_type(f);
        self
    }

    fn normalize_contravariant_candidates_from_annotation(
        mut self,
        map: &mut TypeVariableMap,
    ) -> Option<Self> {
        if let Some(a) = self.contravariant_candidates_from_annotation {
            self.contravariant_candidates_from_annotation = Some(
                a.into_iter()
                    .map(|t| {
                        if let TypeMatchable::Variable(v) =
                            map.find(t).matchable()
                        {
                            Some(v)
                        } else {
                            None
                        }
                    })
                    .collect::<Option<_>>()?,
            )
        };
        Some(self)
    }

    fn contains_variable(&self, v: TypeVariable) -> bool {
        self.type_.contains_variable(v)
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
        self.replace_num_with_update_flag(from, to, 0).0
    }

    fn replace_num_with_update_flag(
        self,
        from: TypeVariable,
        to: &Self,
        recursive_alias_depth: usize,
    ) -> (Self, bool) {
        let mut updated = false;
        let mut t = Type::default();
        for u in self {
            let (u, up_) = unwrap_or_clone(u).replace_num_with_update_flag(
                from,
                to,
                recursive_alias_depth,
            );
            updated |= up_;
            for u in u {
                t.insert_with_already_considered_relations(u, None);
            }
        }
        (t, updated)
    }

    fn covariant_type_variables(&self) -> Vec<TypeVariable> {
        match self.matchable_ref() {
            TypeMatchableRef::Fn(a, r) => merge_vec(
                r.covariant_type_variables(),
                a.contravariant_type_variables(),
            ),
            TypeMatchableRef::Union(cs) => cs
                .iter()
                .map(|c| Type::from(c.clone()).covariant_type_variables())
                .concat(),
            TypeMatchableRef::Variable(n) => {
                vec![n]
            }
            TypeMatchableRef::Empty => Default::default(),
            TypeMatchableRef::RecursiveAlias { body } => {
                let mut vs: FxHashSet<_> =
                    body.covariant_type_variables().into_iter().collect();
                vs.remove(&TypeVariable::RecursiveIndex(0));
                vs.into_iter().collect()
            }
            TypeMatchableRef::Const { .. } => Vec::new(),
            TypeMatchableRef::Tuple(a, b) => merge_vec(
                a.covariant_type_variables(),
                b.covariant_type_variables(),
            ),
        }
    }

    fn contravariant_type_variables(&self) -> Vec<TypeVariable> {
        match self.matchable_ref() {
            TypeMatchableRef::Fn(a, r) => merge_vec(
                a.covariant_type_variables(),
                r.contravariant_type_variables(),
            ),
            TypeMatchableRef::Union(cs) => cs
                .iter()
                .map(|c| Type::from(c.clone()).contravariant_type_variables())
                .concat(),
            TypeMatchableRef::Variable(_) | TypeMatchableRef::Empty => {
                Default::default()
            }
            TypeMatchableRef::RecursiveAlias { body } => {
                let mut vs: FxHashSet<_> =
                    body.contravariant_type_variables().into_iter().collect();
                vs.remove(&TypeVariable::RecursiveIndex(0));
                vs.into_iter().collect()
            }
            TypeMatchableRef::Const { .. } => Vec::new(),
            TypeMatchableRef::Tuple(a, b) => merge_vec(
                a.contravariant_type_variables(),
                b.contravariant_type_variables(),
            ),
        }
    }

    fn find_recursive_alias(&self) -> Option<&Type<'a>> {
        self.iter().find_map(|t| t.find_recursive_alias())
    }

    fn replace_type(self, from: &TypeUnit<'a>, to: &TypeUnit<'a>) -> Self {
        self.into_iter()
            .map(|t| unwrap_or_clone(t).replace_type(from, to))
            .collect()
    }

    fn replace_type_union(self, from: &Type, to: &TypeUnit<'a>) -> Self {
        if self == *from {
            to.clone().into()
        } else {
            self.into_iter()
                .map(|t| unwrap_or_clone(t).replace_type_union(from, to))
                .collect()
        }
    }

    fn replace_type_union_with_update_flag(
        self,
        from: &Type,
        to: &TypeUnit<'a>,
        recursive_alias_depth: usize,
    ) -> (Self, bool) {
        if self == *from {
            (to.clone().into(), true)
        } else {
            let mut updated = false;
            (
                self.into_iter()
                    .map(|t| {
                        let (t, u) = unwrap_or_clone(t)
                            .replace_type_union_with_update_flag(
                                from,
                                to,
                                recursive_alias_depth,
                            );
                        updated |= u;
                        t
                    })
                    .collect(),
                updated,
            )
        }
    }

    fn map_type<F: FnMut(Type<'a>) -> Type<'a>>(self, mut f: F) -> Self {
        f(self)
    }

    fn normalize_contravariant_candidates_from_annotation(
        self,
        _map: &mut TypeVariableMap<'a>,
    ) -> Option<Self> {
        Some(self)
    }

    fn contains_variable(&self, v: TypeVariable) -> bool {
        self.iter().any(|t| t.contains_variable(v))
    }
}

pub fn merge_vec<T>(mut a: Vec<T>, mut b: Vec<T>) -> Vec<T> {
    a.append(&mut b);
    a
}

pub trait TypeConstructor<'a>:
    Sized + std::fmt::Debug + std::fmt::Display + Eq + Clone + std::hash::Hash
{
    fn all_type_variables(&self) -> FxHashSet<TypeVariable>;
    fn all_type_variables_vec(&self) -> Vec<TypeVariable>;
    fn contains_variable(&self, v: TypeVariable) -> bool;
    fn replace_num(self, from: TypeVariable, to: &Type<'a>) -> Self;
    fn replace_num_with_update_flag(
        self,
        from: TypeVariable,
        to: &Type<'a>,
        recursive_alias_depth: usize,
    ) -> (Self, bool);
    fn covariant_type_variables(&self) -> Vec<TypeVariable>;
    fn contravariant_type_variables(&self) -> Vec<TypeVariable>;
    fn find_recursive_alias(&self) -> Option<&Type<'a>>;
    fn replace_type(self, from: &TypeUnit<'a>, to: &TypeUnit<'a>) -> Self;
    fn replace_type_union(self, from: &Type, to: &TypeUnit<'a>) -> Self;
    fn replace_type_union_with_update_flag(
        self,
        from: &Type,
        to: &TypeUnit<'a>,
        recursive_alias_depth: usize,
    ) -> (Self, bool);
    fn map_type<F: FnMut(Type<'a>) -> Type<'a>>(self, f: F) -> Self;
    fn normalize_contravariant_candidates_from_annotation(
        self,
        map: &mut TypeVariableMap<'a>,
    ) -> Option<Self>;
}

impl<'a> TypeUnit<'a> {
    fn find_recursive_alias(&self) -> Option<&Type<'a>> {
        match self {
            TypeUnit::Fn(a, r) => {
                [a, r].iter().find_map(|a| a.find_recursive_alias())
            }
            TypeUnit::Variable(_) => None,
            TypeUnit::RecursiveAlias { body } => Some(body),
            TypeUnit::Const { .. } => None,
            TypeUnit::Tuple(a, b) => {
                [a, b].iter().find_map(|a| a.find_recursive_alias())
            }
        }
    }
}

pub fn unwrap_or_clone<T: Clone>(this: Rc<T>) -> T {
    Rc::try_unwrap(this).unwrap_or_else(|rc| (*rc).clone())
}

impl Display for Type<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeMatchableRef::*;
        match self.matchable_ref() {
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
                        if let TypeUnit::Fn(_, _) = **t {
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
            Const { name, .. } => write!(f, ":{}", name),
            Tuple(a, b) => fmt_tuple(a, b, f),
        }
    }
}

impl std::fmt::Debug for Type<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeMatchableRef::*;
        match self.matchable_ref() {
            Fn(arg, rtn) => {
                if let Fn(_, _) = arg.matchable_ref() {
                    write!(f, "({:?}) -> {:?}", arg, rtn)
                } else {
                    write!(f, "{:?} -> {:?}", arg, rtn)
                }
            }
            Union(a) => write!(
                f,
                "{{{}}}",
                a.iter()
                    .map(|t| {
                        if let TypeUnit::Fn(_, _) = **t {
                            format!("({:?})", t)
                        } else {
                            format!("{:?}", t)
                        }
                    })
                    .join(" | ")
            ),
            Variable(n) => write!(f, "{}", n),
            Empty => write!(f, "∅"),
            RecursiveAlias { body } => {
                write!(f, "rec[{:?}]", *body)
            }
            Const { name, .. } => write!(f, ":{}", name),
            Tuple(a, b) => write!(f, "({a:?}, {b:?})"),
        }
    }
}

impl std::fmt::Debug for TypeUnit<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeUnit::*;
        match self {
            Fn(arg, rtn) => {
                if let TypeMatchableRef::Fn(_, _) = arg.matchable_ref() {
                    write!(f, "({:?}) -> {:?}", arg, rtn)
                } else {
                    write!(f, "{:?} -> {:?}", arg, rtn)
                }
            }
            Variable(n) => write!(f, "{}", n),
            RecursiveAlias { body } => {
                write!(f, "rec[{:?}]", *body)
            }
            Const { name, .. } => write!(f, ":{name}"),
            Tuple(a, b) => write!(f, "({a:?}, {b:?})"),
        }
    }
}

impl Display for TypeUnit<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeUnit::*;
        match self {
            Fn(arg, rtn) => {
                if let TypeMatchableRef::Fn(_, _) = arg.matchable_ref() {
                    write!(f, "({}) -> {}", arg, rtn)
                } else {
                    write!(f, "{} -> {}", arg, rtn)
                }
            }
            Variable(n) => write!(f, "{}", n),
            RecursiveAlias { body } => {
                write!(f, "rec[{}]", *body)
            }
            Const { name, .. } => write!(f, ":{name}"),
            Tuple(a, b) => fmt_tuple(a, b, f),
        }
    }
}

fn fmt_tuple(
    a: &Type<'_>,
    b: &Type<'_>,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    if let TypeMatchableRef::Const { name, .. } = a.matchable_ref() {
        match b.matchable_ref() {
            TypeMatchableRef::Const { id, .. }
                if id == TypeId::Intrinsic(IntrinsicType::Unit) =>
            {
                write!(f, "{}", name)
            }
            TypeMatchableRef::Tuple(h, t) => {
                write!(f, "{}[{}", name, h)?;
                fmt_tuple_tail(t, f)
            }
            TypeMatchableRef::Union(u) => {
                write!(f, "{}[{}]", name, u)
            }
            _ => panic!("expected tuple but found {}", b),
        }
    } else {
        write!(f, "[{a}")?;
        fmt_tuple_tail(b, f)
    }
}

fn fmt_tuple_tail(
    tuple: &Type<'_>,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    use TypeMatchableRef::*;
    match tuple.matchable_ref() {
        Union(u) => write!(f, "] <> {{{}}}", u.iter().format(" | ")),
        Empty => write!(f, "] <> ∅"),
        Tuple(a, b) => {
            write!(f, ", {}", a)?;
            fmt_tuple_tail(b, f)
        }
        Const { id, .. } if id == TypeId::Intrinsic(IntrinsicType::Unit) => {
            write!(f, "]")
        }
        _ => panic!("expected tuple but found {}", tuple),
    }
}

impl Display for SingleTypeConstructor<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

impl<'a> From<TypeWithEnv<'a, SingleTypeConstructor<'a>>>
    for TypeWithEnv<'a, Type<'a>>
{
    fn from(t: TypeWithEnv<'a, SingleTypeConstructor<'a>>) -> Self {
        TypeWithEnv {
            constructor: t.constructor.type_,
            variable_requirements: t.variable_requirements,
            subtype_relations: t.subtype_relations,
            pattern_restrictions: t.pattern_restrictions,
            already_considered_relations: t.already_considered_relations,
        }
    }
}
