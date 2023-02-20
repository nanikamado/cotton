use super::simplify::{DataDecl, Env};
use super::{simplify_subtype_rel, unwrap_recursive_alias, TypeVariableMap};
use crate::ast_step2::types::{
    unwrap_or_clone, Type, TypeConstructor, TypeMatchableRef, TypeUnit,
    TypeVariable,
};
use crate::ast_step2::{RelOrigin, SubtypeRelations, TypeId};
use crate::errors::CompileError;
use crate::intrinsics::{IntrinsicType, INTRINSIC_TYPES};
use fxhash::FxHashMap;
use itertools::Itertools;
use parser::Span;
use std::fmt::Display;

#[derive(Debug, Clone)]
pub enum MatchOperandUnit {
    Const(TypeId),
    Tuple(MatchOperand, MatchOperand),
    Any,
    Variable(TypeVariable),
    NotComputed(TypeUnit),
}

#[derive(Debug, Clone, Default)]
pub struct MatchOperand(Vec<MatchOperandUnit>);

impl From<MatchOperandUnit> for MatchOperand {
    fn from(value: MatchOperandUnit) -> Self {
        Self(vec![value])
    }
}

impl IntoIterator for MatchOperand {
    type Item = MatchOperandUnit;
    type IntoIter = std::vec::IntoIter<MatchOperandUnit>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<MatchOperandUnit> for MatchOperand {
    fn from_iter<T: IntoIterator<Item = MatchOperandUnit>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl MatchOperandUnit {
    pub fn map_type(self, f: &mut impl FnMut(Type) -> Type) -> MatchOperand {
        use MatchOperandUnit::*;
        match self {
            Const(c) => Const(c).into(),
            Tuple(a, b) => Tuple(a.map_type(f), b.map_type(f)).into(),
            Any => Any.into(),
            Variable(v) => f(TypeUnit::Variable(v).into())
                .into_iter()
                .map(|a| NotComputed(unwrap_or_clone(a)))
                .collect(),
            NotComputed(c) => f(c.into())
                .into_iter()
                .map(|a| NotComputed(unwrap_or_clone(a)))
                .collect(),
        }
    }

    fn contains_recursion(&self) -> bool {
        use MatchOperandUnit::*;
        match self {
            Const(_) | Any | Variable(_) => false,
            Tuple(a, b) => a.contains_recursion() || b.contains_recursion(),
            NotComputed(t) => t.contains_recursion(),
        }
    }

    pub fn remove_disjoint_part(
        self,
        other: &TypeUnit,
        env: &mut Env,
    ) -> (MatchOperand, MatchOperand) {
        match (self, other) {
            (MatchOperandUnit::Variable(v), _) => {
                if TypeUnit::Variable(v) == *other {
                    (
                        MatchOperand::default(),
                        MatchOperandUnit::Variable(v).into(),
                    )
                } else {
                    (
                        MatchOperandUnit::Variable(v).into(),
                        MatchOperand::default(),
                    )
                }
            }
            (MatchOperandUnit::NotComputed(t), _) => {
                let (out, maybe_in, _) = t.remove_disjoint_part(other);
                (
                    MatchOperand::not_computed_from_type(out),
                    MatchOperand::not_computed_from_type(maybe_in),
                )
            }
            (MatchOperandUnit::Const(id1), TypeUnit::Const { id: id2 })
                if id1 == *id2 =>
            {
                (MatchOperand::default(), MatchOperandUnit::Const(id1).into())
            }
            (MatchOperandUnit::Tuple(a1, a2), TypeUnit::Tuple(b1, b2)) => {
                let (a1_out, a1_in) = a1.remove_disjoint_part(b1, env);
                if a1_in.0.is_empty() {
                    let out = MatchOperand::tuple(a1_out, a2);
                    return (out, MatchOperand::default());
                }
                let (a2_out, a2_in) = a2.remove_disjoint_part(b2, env);
                let out = MatchOperand::default()
                    .union(MatchOperand::tuple(
                        a1_out,
                        a2_out.clone().union(a2_in.clone()),
                    ))
                    .union(MatchOperand::tuple(a1_in.clone(), a2_out));
                (out, MatchOperand::tuple(a1_in, a2_in))
            }
            (t, _) => (t.into(), Default::default()),
        }
    }

    fn split_slow(self, other: &TypeUnit) -> (MatchOperand, MatchOperand) {
        match (self, other) {
            (MatchOperandUnit::Tuple(a1, a2), TypeUnit::Tuple(b1, b2)) => {
                let (a1_out, a1_in) = a1.split_slow(b1);
                let (a2_out, a2_in) = a2.split_slow(b2);
                (
                    MatchOperand::default()
                        .union(MatchOperand::tuple(
                            a1_out,
                            a2_out.clone().union(a2_in.clone()),
                        ))
                        .union(MatchOperand::tuple(a1_in.clone(), a2_out)),
                    MatchOperand::tuple(a1_in, a2_in),
                )
            }
            (MatchOperandUnit::NotComputed(m), _) => {
                let (maybe_out, in_) =
                    m.split_slow(other, &mut Default::default());
                (
                    MatchOperand::not_computed_from_type(maybe_out),
                    MatchOperand::not_computed_from_type(in_),
                )
            }
            (MatchOperandUnit::Variable(v), _) => {
                if TypeUnit::Variable(v) == *other {
                    (
                        MatchOperand::default(),
                        MatchOperand::not_computed_from_type(
                            other.clone().into(),
                        ),
                    )
                } else {
                    (
                        MatchOperand::not_computed_from_type(
                            TypeUnit::Variable(v).into(),
                        ),
                        MatchOperand::default(),
                    )
                }
            }
            (MatchOperandUnit::Const(idm), TypeUnit::Const { id })
                if idm == *id =>
            {
                (MatchOperand::default(), MatchOperandUnit::Const(idm).into())
            }
            (t, _) => (t.into(), MatchOperand::default()),
        }
    }
}

impl Display for MatchOperandUnit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MatchOperandUnit::Const(c) => {
                write!(f, ":{c}")
            }
            MatchOperandUnit::Tuple(a, b) => {
                if a.0.len() == 1 {
                    if let MatchOperandUnit::Const(c) = a.0[0] {
                        write!(
                            f,
                            "{}",
                            b.clone()
                                .argument_vecs_from_argument_tuple()
                                .iter()
                                .format_with("|", |args, f| {
                                    if args.is_empty() {
                                        f(&c)
                                    } else {
                                        f(&format_args!(
                                            "{c}({})",
                                            args.iter().format(", ")
                                        ))
                                    }
                                })
                        )
                    } else {
                        write!(f, "{a}, {b}")
                    }
                } else {
                    write!(f, "{a}, {b}")
                }
            }
            MatchOperandUnit::Any => {
                write!(f, "Any")
            }
            MatchOperandUnit::Variable(_) => {
                write!(f, "_")
            }
            MatchOperandUnit::NotComputed(_) => {
                write!(f, "_")
            }
        }
    }
}

impl Display for MatchOperand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            write!(f, "EmptyMatchOperand")
        } else {
            write!(f, "{}", self.0.iter().format(" | "))
        }
    }
}

trait MapType {
    fn map_type(self, f: &mut impl FnMut(Type) -> Type) -> Self;

    fn replace_num(self, from: TypeVariable, to: &Type) -> Self
    where
        Self: Sized,
    {
        self.map_type(&mut |t| t.replace_num(from, to))
    }
}

impl MapType for MatchOperand {
    fn map_type(self, f: &mut impl FnMut(Type) -> Type) -> Self {
        self.into_iter().flat_map(|a| a.map_type(f)).collect()
    }
}

impl MatchOperand {
    pub fn append(&mut self, mut other: Self) {
        self.0.append(&mut other.0)
    }

    pub fn union(mut self, other: MatchOperand) -> Self {
        self.append(other);
        self
    }

    pub fn argument_vecs_from_argument_tuple(self) -> Vec<Vec<Self>> {
        use MatchOperandUnit::*;
        self.into_iter()
            .flat_map(|t| match t {
                Const(id) if id == TypeId::Intrinsic(IntrinsicType::Unit) => {
                    vec![Vec::new()]
                }
                Tuple(a1, a2) => a2
                    .argument_vecs_from_argument_tuple()
                    .into_iter()
                    .map(|mut args| {
                        args.insert(0, a1.clone());
                        args
                    })
                    .collect(),
                NotComputed(TypeUnit::Const {
                    id: TypeId::Intrinsic(IntrinsicType::Unit),
                }) => vec![Vec::new()],
                t => {
                    panic!("expected Tuple or Unit but got {t:?}")
                }
            })
            .collect()
    }

    pub fn argument_tuple_from_arguments(ts: Vec<Self>) -> Self {
        ts.into_iter().rev().fold(
            MatchOperandUnit::Const(TypeId::Intrinsic(INTRINSIC_TYPES["()"]))
                .into(),
            |acc, t| MatchOperandUnit::Tuple(t, acc).into(),
        )
    }

    pub fn not_computed_from_type(t: Type) -> Self {
        t.into_iter()
            .map(|a| MatchOperandUnit::NotComputed(unwrap_or_clone(a)))
            .collect()
    }

    pub fn remove_disjoint_part(
        self,
        other: &Type,
        env: &mut Env,
    ) -> (Self, Self) {
        let mut in_ = Self::default();
        let mut out = self;
        for t in other.iter() {
            let i;
            (out, i) = out.remove_disjoint_part_unit(t, env);
            in_.append(i);
        }
        (out, in_)
    }

    fn remove_disjoint_part_unit(
        self,
        other: &TypeUnit,
        env: &mut Env,
    ) -> (Self, Self) {
        if !self.contains_recursion()
            && other.is_non_polymorphic_recursive_fn_apply()
        {
            return self.remove_disjoint_part(
                &Type::from(other.clone()).unwrap_recursive_fn_apply().0,
                env,
            );
        }
        let mut in_ = MatchOperand::default();
        let mut out = MatchOperand::default();
        for t in self {
            let (o, i) = t.remove_disjoint_part(other, env);
            in_.append(i);
            out.append(o);
        }
        (out, in_)
    }

    pub fn split_slow(self, other: &Type) -> (Self, Self) {
        let mut in_ = Self::default();
        let mut out = self;
        for t in other.iter() {
            let i;
            (out, i) = out.split_unit_slow(t);
            in_.append(i);
        }
        (out, in_)
    }

    pub fn split_unit_slow(self, other: &TypeUnit) -> (Self, Self) {
        if !self.contains_recursion()
            && other.is_non_polymorphic_recursive_fn_apply()
        {
            return self
                .split_slow(&other.clone().unwrap_recursive_fn_apply().0);
        }
        let mut in_ = Self::default();
        let mut out = Self::default();
        for t in self {
            let (o, i) = t.split_slow(other);
            in_.append(i);
            out.append(o);
        }
        (out, in_)
    }

    pub fn contains_recursion(&self) -> bool {
        self.0.iter().any(|a| a.contains_recursion())
    }

    pub fn tuple(self, other: Self) -> Self {
        if self.0.is_empty() || other.0.is_empty() {
            Self::default()
        } else {
            MatchOperandUnit::Tuple(self, other).into()
        }
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

pub fn disclose_type_unit(
    type_: TypeUnit,
    data_decls: &mut FxHashMap<TypeId, DataDecl>,
) -> MatchOperand {
    match type_ {
        TypeUnit::Const { id } => {
            debug_assert!(matches!(id, TypeId::Intrinsic(_)));
            MatchOperandUnit::Const(id).into()
        }
        TypeUnit::Tuple(a, b) => match a.matchable_ref() {
            TypeMatchableRef::Const {
                id: id @ TypeId::DeclId(_),
            } => {
                let args = Type::argument_vecs_from_argument_tuple(b);
                let fields = data_decls[&id].clone();
                let t: MatchOperand = MatchOperand::tuple(
                    MatchOperandUnit::Const(TypeId::DeclId(fields.decl_id))
                        .into(),
                    fields.fields.into_iter().rev().fold(
                        MatchOperandUnit::Const(TypeId::Intrinsic(
                            IntrinsicType::Unit,
                        ))
                        .into(),
                        |m, f| {
                            MatchOperand::tuple(
                                MatchOperand::not_computed_from_type(f.type_),
                                m,
                            )
                        },
                    ),
                );
                args.into_iter()
                    .flat_map(|args| {
                        debug_assert_eq!(args.len(), fields.type_parameter_len);
                        args.iter().enumerate().fold(t.clone(), |t, (i, b)| {
                            t.replace_num(TypeVariable::RecursiveIndex(i), b)
                        })
                    })
                    .collect()
            }
            TypeMatchableRef::Union(_) => a
                .into_iter()
                .flat_map(|a| {
                    disclose_type_unit(
                        TypeUnit::Tuple(a.into(), b.clone()),
                        data_decls,
                    )
                })
                .collect(),
            _ => MatchOperand::tuple(
                MatchOperand::not_computed_from_type(a),
                MatchOperand::not_computed_from_type(b),
            ),
        },
        TypeUnit::RecursiveAlias { body } => {
            disclose_type(unwrap_recursive_alias(body), data_decls)
        }
        TypeUnit::Any => MatchOperandUnit::Any.into(),
        t @ TypeUnit::TypeLevelApply { .. } if t.is_recursive_fn_apply() => {
            disclose_type(t.unwrap_recursive_fn_apply().0, data_decls)
        }
        TypeUnit::Variable(v) => MatchOperandUnit::Variable(v).into(),
        TypeUnit::TypeLevelApply { f, a } => {
            MatchOperand::not_computed_from_type(f.type_level_function_apply(a))
        }
        _ => panic!(),
    }
}

pub fn disclose_type(
    type_: Type,
    data_decls: &mut FxHashMap<TypeId, DataDecl>,
) -> MatchOperand {
    type_
        .into_iter()
        .flat_map(|t| disclose_type_unit(unwrap_or_clone(t), data_decls))
        .collect()
}

fn close_type_unit(
    type_: MatchOperandUnit,
    data_decls: &FxHashMap<TypeId, DataDecl>,
    map: &mut TypeVariableMap,
    subtype_relations: &mut SubtypeRelations,
    span: Span,
) -> Result<Type, CompileError> {
    match type_ {
        MatchOperandUnit::Tuple(a, b) => {
            if a.0.len() == 1 {
                match a.0[0] {
                    MatchOperandUnit::Const(id @ TypeId::DeclId(_)) => {
                        let data_decl = &data_decls[&id];
                        let mut ts = Type::default();
                        for b in b.argument_vecs_from_argument_tuple() {
                            let parameter_table = (0..data_decl
                                .type_parameter_len)
                                .map(|_| TypeVariable::new())
                                .collect_vec();
                            for (b, mut field_t) in b.into_iter().zip_eq(
                                data_decl
                                    .fields
                                    .iter()
                                    .map(|f| f.type_.clone()),
                            ) {
                                for (i, a) in parameter_table.iter().enumerate()
                                {
                                    field_t = field_t.replace_num(
                                        TypeVariable::RecursiveIndex(i),
                                        &TypeUnit::Variable(*a).into(),
                                    );
                                }
                                let b = close_type(
                                    b,
                                    data_decls,
                                    map,
                                    subtype_relations,
                                    span.clone(),
                                )?;
                                let r = simplify_subtype_rel(
                                    b.clone(),
                                    field_t.clone(),
                                    None,
                                )
                                .map_err(|reason| {
                                    CompileError::NotSubtypeOf {
                                        sub_type: b.clone(),
                                        super_type: field_t.clone(),
                                        reason,
                                        span: span.clone(),
                                    }
                                })?;
                                for (r0, r1) in r {
                                    subtype_relations.insert((
                                        r0,
                                        r1,
                                        RelOrigin {
                                            left: b.clone(),
                                            right: field_t.clone(),
                                            span: span.clone(),
                                        },
                                    ));
                                }
                            }
                            ts.union_in_place(
                                TypeUnit::Tuple(
                                    TypeUnit::Const { id }.into(),
                                    Type::argument_tuple_from_arguments(
                                        parameter_table
                                            .iter()
                                            .map(|v| {
                                                if let Some(t) =
                                                    subtype_relations
                                                        .possible_strongest(
                                                            map,
                                                            *v,
                                                            &Default::default(),
                                                            &[],
                                                            &Default::default(),
                                                        )
                                                {
                                                    map.insert(
                                                        subtype_relations,
                                                        *v,
                                                        t.clone(),
                                                    );
                                                    t
                                                } else {
                                                    TypeUnit::Variable(*v)
                                                        .into()
                                                }
                                            })
                                            .collect(),
                                    ),
                                )
                                .into(),
                            );
                        }
                        Ok(ts)
                    }
                    _ => Ok(TypeUnit::Tuple(
                        close_type(
                            a,
                            data_decls,
                            map,
                            subtype_relations,
                            span.clone(),
                        )?,
                        close_type(
                            b,
                            data_decls,
                            map,
                            subtype_relations,
                            span,
                        )?,
                    )
                    .into()),
                }
            } else {
                Ok(TypeUnit::Tuple(
                    close_type(
                        a,
                        data_decls,
                        map,
                        subtype_relations,
                        span.clone(),
                    )?,
                    close_type(b, data_decls, map, subtype_relations, span)?,
                )
                .into())
            }
        }
        MatchOperandUnit::Const(id) => Ok(TypeUnit::Const { id }.into()),
        MatchOperandUnit::Any => Ok(TypeUnit::Any.into()),
        MatchOperandUnit::NotComputed(t) => Ok(t.into()),
        MatchOperandUnit::Variable(v) => Ok(TypeUnit::Variable(v).into()),
    }
}

pub fn close_type(
    type_: MatchOperand,
    data_decls: &FxHashMap<TypeId, DataDecl>,
    map: &mut TypeVariableMap,
    subtype_relations: &mut SubtypeRelations,
    span: Span,
) -> Result<Type, CompileError> {
    let t = type_
        .into_iter()
        .map(|t| {
            close_type_unit(t, data_decls, map, subtype_relations, span.clone())
        })
        .try_collect::<_, Vec<_>, _>()?
        .into_iter()
        .flatten()
        .collect();
    Ok(map.normalize_type(t))
}
