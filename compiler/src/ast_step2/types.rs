pub use self::type_type::Type;
pub use self::type_unit::{TypeUnit, TypeVariable, Variance};
use super::TypeWithEnv;
use crate::ast_step2::{types, TypeId};
use crate::ast_step3::simplify_subtype_rel;
use crate::intrinsics::{IntrinsicType, INTRINSIC_TYPES};
use fxhash::FxHashSet;
use itertools::Itertools;
use std::collections::BTreeSet;
use std::fmt::Display;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchable {
    Union(Type),
    Variable(TypeVariable),
    Empty,
    RecursiveAlias {
        body: Type,
    },
    TypeLevelFn(Type),
    TypeLevelApply {
        f: Type,
        a: Type,
    },
    Restrictions {
        t: Type,
        variable_requirements: Vec<(String, Type)>,
        subtype_relations: BTreeSet<(Type, Type)>,
    },
    Const {
        id: TypeId,
    },
    Tuple(Type, Type),
    Any,
    Variance(Variance, Type),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMatchableRef<'b> {
    Union(&'b Type),
    Variable(TypeVariable),
    Empty,
    RecursiveAlias {
        body: &'b Type,
    },
    TypeLevelFn(&'b Type),
    TypeLevelApply {
        f: &'b Type,
        a: &'b Type,
    },
    Restrictions {
        t: &'b Type,
        variable_requirements: &'b Vec<(String, Type)>,
        subtype_relations: &'b BTreeSet<(Type, Type)>,
    },
    Const {
        id: TypeId,
    },
    Tuple(&'b Type, &'b Type),
    Any,
    Variance(Variance, &'b Type),
}

mod type_unit {
    use super::Type;
    use crate::ast_step2::TypeId;
    use std::cell::Cell;
    use std::collections::BTreeSet;
    use std::fmt::{Debug, Display};

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct TypeVariableInner(usize);

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum TypeVariable {
        Normal(TypeVariableInner),
        RecursiveIndex(usize),
    }

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    pub enum Variance {
        Contravariant,
        Invariant,
    }

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum TypeUnit {
        Variable(TypeVariable),
        RecursiveAlias {
            body: Type,
        },
        TypeLevelFn(Type),
        TypeLevelApply {
            f: Type,
            a: Type,
        },
        Restrictions {
            t: Type,
            variable_requirements: Vec<(String, Type)>,
            subtype_relations: BTreeSet<(Type, Type)>,
        },
        Const {
            id: TypeId,
        },
        Tuple(Type, Type),
        Any,
        Variance(Variance, Type),
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

        pub fn is_recursive_index(self) -> bool {
            match self {
                TypeVariable::Normal(_) => false,
                TypeVariable::RecursiveIndex(_) => true,
            }
        }
    }

    impl TypeUnit {
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
                    write!(f, "t{n}")
                }
                TypeVariable::RecursiveIndex(n) => {
                    write!(f, "d{n}")
                }
            }
        }
    }

    impl Debug for TypeVariable {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{self}")
        }
    }
}

mod type_type {
    use super::{TypeMatchable, TypeMatchableRef, TypeUnit};
    use crate::ast_step2::types::unwrap_or_clone;
    use crate::ast_step3::simplify_subtype_rel;
    use smallvec::SmallVec;
    use std::collections::BTreeSet;
    use std::iter;
    use std::rc::Rc;

    const VEC_SIZE: usize = 2;

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
    pub struct Type(SmallVec<[Rc<TypeUnit>; VEC_SIZE]>);

    impl IntoIterator for Type {
        type Item = Rc<TypeUnit>;

        type IntoIter = smallvec::IntoIter<[Rc<TypeUnit>; VEC_SIZE]>;

        fn into_iter(self) -> Self::IntoIter {
            self.0.into_iter()
        }
    }

    impl Type {
        pub fn iter(&self) -> std::slice::Iter<Rc<TypeUnit>> {
            self.0.iter()
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }

        pub fn is_empty(&self) -> bool {
            self.0.is_empty()
        }

        pub fn matchable(mut self) -> TypeMatchable {
            use TypeMatchable::*;
            match self.0.len() {
                0 => Empty,
                1 => match unwrap_or_clone(self.0.pop().unwrap()) {
                    TypeUnit::Variable(i) => Variable(i),
                    TypeUnit::RecursiveAlias { body } => {
                        RecursiveAlias { body }
                    }
                    TypeUnit::TypeLevelFn(f) => TypeLevelFn(f),
                    TypeUnit::TypeLevelApply { f, a } => {
                        TypeLevelApply { f, a }
                    }
                    TypeUnit::Restrictions {
                        t,
                        variable_requirements,
                        subtype_relations,
                    } => Restrictions {
                        t,
                        variable_requirements,
                        subtype_relations,
                    },
                    TypeUnit::Const { id } => Const { id },
                    TypeUnit::Tuple(a, b) => Tuple(a, b),
                    TypeUnit::Any => Any,
                    TypeUnit::Variance(v, t) => Variance(v, t),
                },
                _ => TypeMatchable::Union(self),
            }
        }

        pub fn matchable_ref(&self) -> TypeMatchableRef {
            use TypeMatchableRef::*;
            match self.0.len() {
                0 => Empty,
                1 => match &**self.0.first().unwrap() {
                    TypeUnit::Variable(i) => Variable(*i),
                    TypeUnit::RecursiveAlias { body } => {
                        RecursiveAlias { body }
                    }
                    TypeUnit::Const { id } => Const { id: *id },
                    TypeUnit::Tuple(a, b) => Tuple(a, b),
                    TypeUnit::TypeLevelFn(f) => TypeLevelFn(f),
                    TypeUnit::TypeLevelApply { f, a } => {
                        TypeLevelApply { f, a }
                    }
                    TypeUnit::Restrictions {
                        t,
                        variable_requirements,
                        subtype_relations,
                    } => Restrictions {
                        t,
                        variable_requirements,
                        subtype_relations,
                    },
                    TypeUnit::Any => Any,
                    TypeUnit::Variance(v, t) => Variance(*v, t),
                },
                _ => Union(self),
            }
        }

        pub fn union_in_place(&mut self, other: Self) {
            for t in other {
                self.insert(t);
            }
        }

        fn insert_to_vec(&mut self, other: Rc<TypeUnit>) {
            let i = self.0.partition_point(|x| *x < other);
            self.0.insert(i, other);
        }

        fn push_tuple(&mut self, t: TypeUnit) {
            match t {
                TypeUnit::Tuple(t_head, t_tail) => {
                    let mut m = SmallVec::<[Rc<TypeUnit>; 6]>::with_capacity(
                        self.0.len(),
                    );
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
            other: Rc<TypeUnit>,
            already_considered_relations: Option<BTreeSet<(Type, Type)>>,
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
                    self.insert(Rc::new(t2));
                }
                if let Some(u) = u {
                    self.push_tuple(u);
                }
                if let Some(t1) = t1 {
                    self.push_tuple(t1);
                }
            } else {
                self.0.push(other);
            }
        }

        pub fn insert(&mut self, other: Rc<TypeUnit>) {
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

    impl From<TypeUnit> for Type {
        fn from(t: TypeUnit) -> Self {
            Type(iter::once(Rc::new(t)).collect())
        }
    }

    impl From<Rc<TypeUnit>> for Type {
        fn from(t: Rc<TypeUnit>) -> Self {
            Type(iter::once(t).collect())
        }
    }

    impl TypeUnit {
        pub fn merge_union_with(
            self,
            other: Self,
            mut already_considered_relations: Option<BTreeSet<(Type, Type)>>,
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
                (TypeLevelFn(_), _) | (_, TypeLevelFn(_)) => panic!(),
                (a, b) if a == b => (None, Some(a), None),
                (a, b) => (Some(a), None, Some(b)),
            }
        }

        pub fn contains_empty_in_covariant_candidate(&self) -> bool {
            match self {
                TypeUnit::Variance(super::Variance::Invariant, a)
                | TypeUnit::RecursiveAlias { body: a } => a.is_empty(),
                TypeUnit::Tuple(a, b) => a.is_empty() || b.is_empty(),
                TypeUnit::Restrictions { .. }
                | TypeUnit::Const { .. }
                | TypeUnit::Variable(_)
                | TypeUnit::TypeLevelFn(_)
                | TypeUnit::TypeLevelApply { .. }
                | TypeUnit::Any
                | TypeUnit::Variance(_, _) => false,
            }
        }

        pub fn increment_recursive_index(
            self,
            greater_than_or_equal_to: usize,
            n: i32,
        ) -> Self {
            match self {
                TypeUnit::Variance(v, t) => TypeUnit::Variance(
                    v,
                    t.increment_recursive_index(greater_than_or_equal_to, n),
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
                TypeUnit::TypeLevelFn(body) => {
                    TypeUnit::TypeLevelFn(body.increment_recursive_index(
                        greater_than_or_equal_to + 1,
                        n,
                    ))
                }
                TypeUnit::TypeLevelApply { f, a } => TypeUnit::TypeLevelApply {
                    f: f.increment_recursive_index(greater_than_or_equal_to, n),
                    a: a.increment_recursive_index(greater_than_or_equal_to, n),
                },
                TypeUnit::Restrictions {
                    t,
                    variable_requirements,
                    subtype_relations,
                } => TypeUnit::Restrictions {
                    t: t.increment_recursive_index(greater_than_or_equal_to, n),
                    variable_requirements: variable_requirements
                        .into_iter()
                        .map(|(name, t)| {
                            (
                                name,
                                t.increment_recursive_index(
                                    greater_than_or_equal_to,
                                    n,
                                ),
                            )
                        })
                        .collect(),
                    subtype_relations: subtype_relations
                        .into_iter()
                        .map(|(a, b)| {
                            (
                                a.increment_recursive_index(
                                    greater_than_or_equal_to,
                                    n,
                                ),
                                b.increment_recursive_index(
                                    greater_than_or_equal_to,
                                    n,
                                ),
                            )
                        })
                        .collect(),
                },
                a @ (TypeUnit::Const { .. } | TypeUnit::Any) => a,
                TypeUnit::Tuple(a, b) => TypeUnit::Tuple(
                    a.increment_recursive_index(greater_than_or_equal_to, n),
                    b.increment_recursive_index(greater_than_or_equal_to, n),
                ),
            }
        }
    }
}

impl Type {
    #[allow(clippy::wrong_self_convention)]
    pub fn is_subtype_of(self, other: Self) -> bool {
        let r = simplify_subtype_rel(self, other, None);
        r.map(|v| v.is_empty()).unwrap_or(false)
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn is_subtype_of_with_rels(
        self,
        other: Self,
        already_considered_relations: Option<&mut BTreeSet<(Type, Type)>>,
    ) -> bool {
        let r = simplify_subtype_rel(self, other, already_considered_relations);
        r.map(|v| v.is_empty()).unwrap_or(false)
    }

    pub fn intrinsic_from_str(t: &'static str) -> Self {
        TypeUnit::Tuple(
            TypeUnit::Const {
                id: TypeId::Intrinsic(INTRINSIC_TYPES[t]),
            }
            .into(),
            TypeUnit::Const {
                id: TypeId::Intrinsic(INTRINSIC_TYPES["()"]),
            }
            .into(),
        )
        .into()
    }
}

impl FromIterator<TypeUnit> for Type {
    fn from_iter<T: IntoIterator<Item = TypeUnit>>(iter: T) -> Self {
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

impl FromIterator<Rc<TypeUnit>> for Type {
    fn from_iter<T: IntoIterator<Item = Rc<TypeUnit>>>(iter: T) -> Self {
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

impl From<TypeMatchable> for Type {
    fn from(m: TypeMatchable) -> Self {
        match m {
            TypeMatchable::Union(u) => u,
            TypeMatchable::Variable(i) => TypeUnit::Variable(i).into(),
            TypeMatchable::Empty => Default::default(),
            TypeMatchable::RecursiveAlias { body } => {
                TypeUnit::RecursiveAlias { body }.into()
            }
            TypeMatchable::Const { id } => TypeUnit::Const { id }.into(),
            TypeMatchable::Tuple(a, b) => TypeUnit::Tuple(a, b).into(),
            TypeMatchable::TypeLevelFn(a) => TypeUnit::TypeLevelFn(a).into(),
            TypeMatchable::TypeLevelApply { f, a } => {
                TypeUnit::TypeLevelApply { f, a }.into()
            }
            TypeMatchable::Restrictions {
                t,
                variable_requirements,
                subtype_relations,
            } => TypeUnit::Restrictions {
                t,
                variable_requirements,
                subtype_relations,
            }
            .into(),
            TypeMatchable::Any => TypeUnit::Any.into(),
            TypeMatchable::Variance(v, t) => TypeUnit::Variance(v, t).into(),
        }
    }
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SingleTypeConstructor {
    pub type_: Type,
    pub has_annotation: bool,
}

impl TypeConstructor for SingleTypeConstructor {
    fn all_type_variables(&self) -> fxhash::FxHashSet<TypeVariable> {
        self.type_.all_type_variables()
    }

    fn all_type_variables_vec(&self) -> Vec<TypeVariable> {
        self.type_.all_type_variables_vec()
    }

    fn replace_num(mut self, from: TypeVariable, to: &type_type::Type) -> Self {
        self.type_ = self.type_.replace_num(from, to);
        self
    }

    fn replace_num_with_update_flag(
        mut self,
        from: TypeVariable,
        to: &Type,
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
        if self.has_annotation {
            self.all_type_variables().into_iter().collect()
        } else {
            self.type_.covariant_type_variables()
        }
    }

    fn contravariant_type_variables(&self) -> Vec<TypeVariable> {
        if self.has_annotation {
            Vec::new()
        } else {
            self.type_.contravariant_type_variables()
        }
    }

    fn find_recursive_alias(&self) -> Option<&Type> {
        self.type_.find_recursive_alias()
    }

    fn replace_type(mut self, from: &TypeUnit, to: &TypeUnit) -> Self {
        self.type_ = self.type_.replace_type(from, to);
        self
    }

    fn replace_type_union(mut self, from: &Type, to: &TypeUnit) -> Self {
        self.type_ = self.type_.replace_type_union(from, to);
        self
    }

    fn replace_type_union_with_update_flag(
        mut self,
        from: &Type,
        to: &TypeUnit,
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

    fn map_type<F: FnMut(Type) -> Type>(mut self, f: F) -> Self {
        self.type_ = self.type_.map_type(f);
        self
    }

    fn contains_variable(&self, v: TypeVariable) -> bool {
        self.type_.contains_variable(v)
    }
}

impl TypeConstructor for Type {
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
            TypeMatchableRef::Const { .. } | TypeMatchableRef::Any => {
                Vec::new()
            }
            TypeMatchableRef::Tuple(a, b) => merge_vec(
                a.covariant_type_variables(),
                b.covariant_type_variables(),
            ),
            TypeMatchableRef::TypeLevelFn(f) => f.covariant_type_variables(),
            TypeMatchableRef::TypeLevelApply { f, a } => {
                [f.covariant_type_variables(), a.covariant_type_variables()]
                    .concat()
            }
            TypeMatchableRef::Restrictions {
                t,
                variable_requirements,
                ..
            } => variable_requirements
                .iter()
                .flat_map(|(_, t)| t.contravariant_type_variables())
                .chain(t.covariant_type_variables())
                .collect(),
            TypeMatchableRef::Variance(Variance::Invariant, t) => merge_vec(
                t.covariant_type_variables(),
                t.contravariant_type_variables(),
            ),
            TypeMatchableRef::Variance(Variance::Contravariant, t) => {
                t.contravariant_type_variables()
            }
        }
    }

    fn contravariant_type_variables(&self) -> Vec<TypeVariable> {
        match self.matchable_ref() {
            TypeMatchableRef::Union(cs) => cs
                .iter()
                .map(|c| Type::from(c.clone()).contravariant_type_variables())
                .concat(),
            TypeMatchableRef::Variable(_)
            | TypeMatchableRef::Empty
            | TypeMatchableRef::Any => Default::default(),
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
            TypeMatchableRef::TypeLevelFn(f) => {
                f.contravariant_type_variables()
            }
            TypeMatchableRef::TypeLevelApply { f, a } => [
                f.contravariant_type_variables(),
                a.contravariant_type_variables(),
            ]
            .concat(),
            TypeMatchableRef::Restrictions {
                t,
                variable_requirements,
                ..
            } => variable_requirements
                .iter()
                .flat_map(|(_, t)| t.covariant_type_variables())
                .chain(t.contravariant_type_variables())
                .collect(),
            TypeMatchableRef::Variance(Variance::Contravariant, t) => {
                t.covariant_type_variables()
            }
            TypeMatchableRef::Variance(Variance::Invariant, t) => merge_vec(
                t.covariant_type_variables(),
                t.contravariant_type_variables(),
            ),
        }
    }

    fn find_recursive_alias(&self) -> Option<&Type> {
        self.iter().find_map(|t| t.find_recursive_alias())
    }

    fn replace_type(self, from: &TypeUnit, to: &TypeUnit) -> Self {
        self.into_iter()
            .map(|t| unwrap_or_clone(t).replace_type(from, to))
            .collect()
    }

    fn replace_type_union(self, from: &Type, to: &TypeUnit) -> Self {
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
        to: &TypeUnit,
        recursive_alias_depth: usize,
    ) -> (Self, bool) {
        if self == *from {
            (
                Type::from(to.clone())
                    .increment_recursive_index(0, recursive_alias_depth as i32),
                true,
            )
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

    fn map_type<F: FnMut(Type) -> Type>(self, mut f: F) -> Self {
        f(self)
    }

    fn contains_variable(&self, v: TypeVariable) -> bool {
        self.iter().any(|t| t.contains_variable(v))
    }
}

pub fn merge_vec<T>(mut a: Vec<T>, mut b: Vec<T>) -> Vec<T> {
    a.append(&mut b);
    a
}

pub trait TypeConstructor:
    Sized + std::fmt::Debug + std::fmt::Display + Eq + Clone + std::hash::Hash
{
    fn all_type_variables(&self) -> FxHashSet<TypeVariable>;
    fn all_type_variables_vec(&self) -> Vec<TypeVariable>;
    fn contains_variable(&self, v: TypeVariable) -> bool;
    fn replace_num(self, from: TypeVariable, to: &Type) -> Self;
    fn replace_num_with_update_flag(
        self,
        from: TypeVariable,
        to: &Type,
        recursive_alias_depth: usize,
    ) -> (Self, bool);
    fn covariant_type_variables(&self) -> Vec<TypeVariable>;
    fn contravariant_type_variables(&self) -> Vec<TypeVariable>;
    fn find_recursive_alias(&self) -> Option<&Type>;
    fn replace_type(self, from: &TypeUnit, to: &TypeUnit) -> Self;
    fn replace_type_union(self, from: &Type, to: &TypeUnit) -> Self;
    fn replace_type_union_with_update_flag(
        self,
        from: &Type,
        to: &TypeUnit,
        recursive_alias_depth: usize,
    ) -> (Self, bool);
    fn map_type<F: FnMut(Type) -> Type>(self, f: F) -> Self;
}

impl TypeUnit {
    fn find_recursive_alias(&self) -> Option<&Type> {
        match self {
            TypeUnit::Const { .. } | TypeUnit::Variable(_) | TypeUnit::Any => {
                None
            }
            TypeUnit::RecursiveAlias { body } => Some(body),
            TypeUnit::Tuple(a, b) => {
                [a, b].iter().find_map(|a| a.find_recursive_alias())
            }
            TypeUnit::TypeLevelFn(f) => f.find_recursive_alias(),
            TypeUnit::TypeLevelApply { f: _, a } => a.find_recursive_alias(),
            TypeUnit::Restrictions { t, .. } | TypeUnit::Variance(_, t) => {
                t.find_recursive_alias()
            }
        }
    }
}

pub fn unwrap_or_clone<T: Clone>(this: Rc<T>) -> T {
    Rc::try_unwrap(this).unwrap_or_else(|rc| (*rc).clone())
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use types::Variance::*;
        use TypeMatchableRef::*;
        match self.matchable_ref() {
            Union(a) => write!(
                f,
                "{{{}}}",
                a.iter()
                    .map(|t| {
                        if t.is_function() {
                            format!("({t})")
                        } else {
                            format!("{t}")
                        }
                    })
                    .join(" | ")
            ),
            Variable(n) => write!(f, "{n}"),
            Empty => write!(f, "∅"),
            RecursiveAlias { body } => {
                write!(f, "rec[{}]", *body)
            }
            Const { id } => write!(f, ":{id}"),
            Tuple(a, b) => fmt_tuple(a, b, f),
            TypeLevelFn(_f) => write!(f, "fn[{_f}]"),
            TypeLevelApply { f: _f, a } => write!(f, "{_f}[{a}]"),
            Restrictions {
                t,
                variable_requirements,
                subtype_relations,
            } => {
                write!(
                    f,
                    "{t} where {{{}, {}}}",
                    subtype_relations.iter().format_with(",\n", |(a, b), f| f(
                        &format_args!("{a} < {b}")
                    )),
                    variable_requirements
                        .iter()
                        .format_with(",\n", |(name, t), f| f(&format_args!(
                            "?{name} : {t}"
                        )))
                )
            }
            Any => write!(f, "Any"),
            Variance(Contravariant, t) => {
                if t.is_function() {
                    write!(f, "-({t})")
                } else {
                    write!(f, "-{t}")
                }
            }
            Variance(Invariant, t) => {
                if t.is_function() {
                    write!(f, "=({t})")
                } else {
                    write!(f, "={t}")
                }
            }
        }
    }
}

impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl std::fmt::Debug for TypeUnit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use types::Variance::*;
        use TypeUnit::*;
        match self {
            Variable(n) => write!(f, "{n}"),
            RecursiveAlias { body } => {
                write!(f, "rec[{:?}]", *body)
            }
            Const { id } => write!(f, ":{}", *id),
            Tuple(a, b) => write!(f, "({a:?}, {b:?})"),
            TypeLevelFn(_f) => write!(f, "fn[{_f:?}]"),
            TypeLevelApply { f: _f, a } => write!(f, "{_f:?}[{a:?}]"),
            Restrictions {
                t,
                variable_requirements,
                subtype_relations,
            } => write!(
                f,
                "{t:?} where {{{subtype_relations:?}, {:?}}}",
                variable_requirements.iter().format(",\n")
            ),
            Any => write!(f, "Any"),
            Variance(Contravariant, t) => write!(f, "-{t}"),
            Variance(Invariant, t) => write!(f, "={t}"),
        }
    }
}

impl Display for TypeUnit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use types::Variance::*;
        use TypeUnit::*;
        match self {
            Variable(n) => write!(f, "{n}"),
            RecursiveAlias { body } => {
                write!(f, "rec[{}]", *body)
            }
            Const { id } => write!(f, ":{}", *id),
            Tuple(a, b) => fmt_tuple(a, b, f),
            TypeLevelFn(_f) => write!(f, "fn[{_f}]"),
            TypeLevelApply { f: _f, a } => write!(f, "{_f}[{a}]"),
            Restrictions {
                t,
                variable_requirements,
                subtype_relations,
            } => write!(
                f,
                "{t} where {{{}, {}}}",
                subtype_relations.iter().format_with(",\n", |(a, b), f| f(
                    &format_args!("{a} < {b}")
                )),
                variable_requirements
                    .iter()
                    .format_with(",\n", |(name, t), f| f(&format_args!(
                        "?{name} : {t}"
                    )))
            ),
            Any => write!(f, "Any"),
            Variance(Contravariant, t) => {
                if t.is_function() {
                    write!(f, "-({t})")
                } else {
                    write!(f, "-{t}")
                }
            }
            Variance(Invariant, t) => {
                if t.is_function() {
                    write!(f, "=({t})")
                } else {
                    write!(f, "={t}")
                }
            }
        }
    }
}

fn fmt_tuple(
    a: &Type,
    b: &Type,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    if let TypeMatchableRef::Const { id: id_a } = a.matchable_ref() {
        if matches!(id_a, TypeId::Intrinsic(IntrinsicType::Fn)) {
            let TypeMatchableRef::Tuple(arg, rtn) = b.matchable_ref() else {
                panic!()
            };
            let TypeMatchableRef::Tuple(rtn, _) = rtn.matchable_ref() else {
                panic!()
            };
            if arg.is_function() {
                write!(f, "({arg}) -> {rtn}")
            } else {
                write!(f, "{arg} -> {rtn}")
            }
        } else {
            match b.matchable_ref() {
                TypeMatchableRef::Const { id: id_b, .. }
                    if id_b == TypeId::Intrinsic(IntrinsicType::Unit) =>
                {
                    write!(f, "{id_a}")
                }
                TypeMatchableRef::Tuple(h, t) => {
                    write!(f, "{id_a}[{h}")?;
                    fmt_tuple_tail(t, f)
                }
                TypeMatchableRef::Union(u) => {
                    write!(f, "{id_a}[{u}]")
                }
                _ => panic!("expected tuple but found {b}"),
            }
        }
    } else {
        write!(f, "[{a}")?;
        fmt_tuple_tail(b, f)
    }
}

fn fmt_tuple_tail(
    tuple: &Type,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    use TypeMatchableRef::*;
    match tuple.matchable_ref() {
        Union(u) => write!(f, "] ++ {{{}}}", u.iter().format(" | ")),
        Empty => write!(f, "] ++ ∅"),
        Tuple(a, b) => {
            write!(f, ", {a}")?;
            fmt_tuple_tail(b, f)
        }
        Const { id, .. } if id == TypeId::Intrinsic(IntrinsicType::Unit) => {
            write!(f, "]")
        }
        _ => panic!("expected tuple but found {tuple}"),
    }
}

impl Display for SingleTypeConstructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (annotation: {})", self.type_, self.has_annotation)
    }
}

impl From<TypeWithEnv<SingleTypeConstructor>> for TypeWithEnv<Type> {
    fn from(t: TypeWithEnv<SingleTypeConstructor>) -> Self {
        TypeWithEnv {
            constructor: t.constructor.type_,
            variable_requirements: t.variable_requirements,
            subtype_relations: t.subtype_relations,
            pattern_restrictions: t.pattern_restrictions,
            already_considered_relations: t.already_considered_relations,
            fn_apply_dummies: t.fn_apply_dummies,
        }
    }
}
