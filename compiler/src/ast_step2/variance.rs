use super::types::{self, unwrap_or_clone, Type, TypeUnit, TypeVariable};
use super::TypeId;
use crate::intrinsics::IntrinsicType;
use fxhash::FxHashMap;

#[derive(Debug)]
pub struct VarianceMap {
    type_id_to_union_of_field_types: FxHashMap<TypeId, Type>,
    arg_is_covariant_candidate: FxHashMap<(TypeId, usize), bool>,
    arg_is_contravariant_candidate: FxHashMap<(TypeId, usize), bool>,
    arg_of_type_level_fn_is_covariant_candidate: FxHashMap<Type, bool>,
    arg_of_type_level_fn_is_contravariant_candidate: FxHashMap<Type, bool>,
}

impl VarianceMap {
    pub fn new(union_of_fields: FxHashMap<TypeId, Type>) -> Self {
        VarianceMap {
            type_id_to_union_of_field_types: union_of_fields,
            arg_is_covariant_candidate: [
                ((TypeId::Intrinsic(IntrinsicType::Fn), 0), false),
                ((TypeId::Intrinsic(IntrinsicType::Fn), 1), true),
            ]
            .into_iter()
            .collect(),
            arg_is_contravariant_candidate: [
                ((TypeId::Intrinsic(IntrinsicType::Fn), 0), true),
                ((TypeId::Intrinsic(IntrinsicType::Fn), 1), false),
            ]
            .into_iter()
            .collect(),
            arg_of_type_level_fn_is_covariant_candidate: Default::default(),
            arg_of_type_level_fn_is_contravariant_candidate: Default::default(),
        }
    }

    pub fn add_variance_to_type(&mut self, t: Type) -> Type {
        t.into_iter()
            .map(|t| self.add_variance_to_type_unit(unwrap_or_clone(t)))
            .collect()
    }

    fn add_variance_to_type_unit(&mut self, t: TypeUnit) -> TypeUnit {
        use TypeUnit::*;
        match t {
            RecursiveAlias { body } => RecursiveAlias {
                body: self.add_variance_to_type(body),
            },
            TypeLevelFn(a) => TypeLevelFn(self.add_variance_to_type(a)),
            TypeLevelApply { f, a } => TypeLevelApply {
                f: self.add_variance_to_type(f),
                a: self.add_variance_to_type(a),
            },
            Restrictions {
                t,
                variable_requirements,
                subtype_relations,
            } => Restrictions {
                t: self.add_variance_to_type(t),
                variable_requirements: variable_requirements
                    .into_iter()
                    .map(|(s, t)| (s, self.add_variance_to_type(t)))
                    .collect(),
                subtype_relations: subtype_relations
                    .into_iter()
                    .map(|(a, b)| {
                        (
                            self.add_variance_to_type(a),
                            self.add_variance_to_type(b),
                        )
                    })
                    .collect(),
            },
            t @ (Const { .. } | Variable(_) | Any) => t,
            Tuple(a, b) => match &a.matchable_ref() {
                types::TypeMatchableRef::Const { id } => {
                    Tuple(a, self.add_variance_to_tuple(*id, b, 0))
                }
                _ => Tuple(
                    self.add_variance_to_type(a),
                    self.add_variance_to_type(b),
                ),
            },
            Variance(_, _) => panic!(),
        }
    }

    fn add_variance_to_tuple_unit(
        &mut self,
        id: TypeId,
        t: TypeUnit,
        arg_index: usize,
    ) -> TypeUnit {
        match t {
            t @ TypeUnit::Const {
                id: TypeId::Intrinsic(IntrinsicType::Unit),
            } => t,
            TypeUnit::Tuple(a, b) => {
                let a = self.add_variance_to_type(a);
                let co = self.type_has_arg_in_covariant_position(id, arg_index);
                let contra =
                    self.type_has_arg_in_contravariant_position(id, arg_index);
                let a = if contra && co {
                    TypeUnit::Variance(types::Variance::Invariant, a).into()
                } else if contra {
                    TypeUnit::Variance(types::Variance::Contravariant, a).into()
                } else {
                    a
                };
                TypeUnit::Tuple(
                    a,
                    self.add_variance_to_tuple(id, b, arg_index + 1),
                )
            }
            _ => panic!(),
        }
    }

    fn add_variance_to_tuple(
        &mut self,
        id: TypeId,
        t: Type,
        arg_index: usize,
    ) -> Type {
        t.into_iter()
            .map(|t| {
                self.add_variance_to_tuple_unit(
                    id,
                    unwrap_or_clone(t),
                    arg_index,
                )
            })
            .collect()
    }

    fn type_has_arg_in_covariant_position(
        &mut self,
        id: TypeId,
        arg_index: usize,
    ) -> bool {
        if let Some(b) = self.arg_is_covariant_candidate.get(&(id, arg_index)) {
            *b
        } else {
            self.arg_is_covariant_candidate
                .insert((id, arg_index), false);
            let r = self.t_has_v_in_covariant_position(
                TypeVariable::RecursiveIndex(arg_index),
                &self.type_id_to_union_of_field_types[&id].clone(),
            );
            if r {
                *self
                    .arg_is_covariant_candidate
                    .get_mut(&(id, arg_index))
                    .unwrap() = r;
            }
            r
        }
    }

    fn type_has_arg_in_contravariant_position(
        &mut self,
        id: TypeId,
        arg_index: usize,
    ) -> bool {
        if let Some(b) =
            self.arg_is_contravariant_candidate.get(&(id, arg_index))
        {
            *b
        } else {
            self.arg_is_contravariant_candidate
                .insert((id, arg_index), false);
            let r = self.t_has_v_in_contravariant_position(
                TypeVariable::RecursiveIndex(arg_index),
                &self.type_id_to_union_of_field_types[&id].clone(),
            );
            if r {
                *self
                    .arg_is_contravariant_candidate
                    .get_mut(&(id, arg_index))
                    .unwrap() = r;
            }
            r
        }
    }

    fn t_has_v_in_covariant_position(
        &mut self,
        v: TypeVariable,
        t: &Type,
    ) -> bool {
        t.iter()
            .any(|t| self.t_has_v_in_covariant_position_unit(v, t))
    }

    fn t_has_v_in_covariant_position_unit(
        &mut self,
        v: TypeVariable,
        t: &TypeUnit,
    ) -> bool {
        match t {
            TypeUnit::Variable(w) => v == *w,
            TypeUnit::RecursiveAlias { body: a } | TypeUnit::TypeLevelFn(a) => {
                self.t_has_v_in_covariant_position(
                    v.increment_recursive_index(1),
                    a,
                )
            }
            TypeUnit::TypeLevelApply { f, a } => {
                self.t_has_v_in_covariant_position(v, a)
                    && self.type_level_fn_has_arg_in_covariant_position(f)
                    || self.t_has_v_in_contravariant_position(v, a)
                        && self
                            .type_level_fn_has_arg_in_contravariant_position(f)
            }
            TypeUnit::Restrictions {
                t,
                variable_requirements,
                ..
            } => {
                self.t_has_v_in_covariant_position(v, t)
                    || variable_requirements.iter().any(|(_, t)| {
                        self.t_has_v_in_contravariant_position(v, t)
                    })
            }
            TypeUnit::Const { .. } | TypeUnit::Any => false,
            TypeUnit::Tuple(a, b) => match a.matchable_ref() {
                types::TypeMatchableRef::Const { id } => {
                    self.tuple_has_v_in_covariant_position(v, b, id, 0)
                }
                _ => {
                    self.t_has_v_in_covariant_position(v, a)
                        || self.t_has_v_in_covariant_position(v, b)
                }
            },
            TypeUnit::Variance(super::types::Variance::Invariant, t) => {
                self.t_has_v_in_covariant_position(v, t)
                    || self.t_has_v_in_contravariant_position(v, t)
            }
            TypeUnit::Variance(super::types::Variance::Contravariant, t) => {
                self.t_has_v_in_contravariant_position(v, t)
            }
        }
    }

    fn t_has_v_in_contravariant_position(
        &mut self,
        v: TypeVariable,
        t: &Type,
    ) -> bool {
        t.iter()
            .any(|t| self.t_has_v_in_contravariant_position_unit(v, t))
    }

    fn t_has_v_in_contravariant_position_unit(
        &mut self,
        v: TypeVariable,
        t: &TypeUnit,
    ) -> bool {
        match t {
            TypeUnit::RecursiveAlias { body: a } | TypeUnit::TypeLevelFn(a) => {
                self.t_has_v_in_contravariant_position(
                    v.increment_recursive_index(1),
                    a,
                )
            }
            TypeUnit::TypeLevelApply { f, a } => {
                self.t_has_v_in_covariant_position(v, a)
                    && self.type_level_fn_has_arg_in_contravariant_position(f)
                    || self.t_has_v_in_contravariant_position(v, a)
                        && self.type_level_fn_has_arg_in_covariant_position(f)
            }
            TypeUnit::Restrictions {
                t,
                variable_requirements,
                ..
            } => {
                self.t_has_v_in_contravariant_position(v, t)
                    || variable_requirements
                        .iter()
                        .any(|(_, t)| self.t_has_v_in_covariant_position(v, t))
            }
            TypeUnit::Const { .. } | TypeUnit::Any | TypeUnit::Variable(_) => {
                false
            }
            TypeUnit::Tuple(a, b) => match a.matchable_ref() {
                types::TypeMatchableRef::Const { id } => {
                    self.tuple_has_v_in_contravariant_position(v, b, id, 0)
                }
                _ => {
                    self.t_has_v_in_contravariant_position(v, a)
                        || self.t_has_v_in_contravariant_position(v, b)
                }
            },
            TypeUnit::Variance(super::types::Variance::Invariant, t) => {
                self.t_has_v_in_covariant_position(v, t)
                    || self.t_has_v_in_contravariant_position(v, t)
            }
            TypeUnit::Variance(super::types::Variance::Contravariant, t) => {
                self.t_has_v_in_covariant_position(v, t)
            }
        }
    }

    fn tuple_has_v_in_covariant_position(
        &mut self,
        v: TypeVariable,
        t: &Type,
        id: TypeId,
        arg_index: usize,
    ) -> bool {
        t.iter().any(|t| {
            self.tuple_has_v_in_covariant_position_unit(v, t, id, arg_index)
        })
    }

    fn tuple_has_v_in_covariant_position_unit(
        &mut self,
        v: TypeVariable,
        t: &TypeUnit,
        id: TypeId,
        arg_index: usize,
    ) -> bool {
        match t {
            TypeUnit::Const {
                id: TypeId::Intrinsic(IntrinsicType::Unit),
            } => false,
            TypeUnit::Tuple(a, b) => {
                self.type_has_arg_in_covariant_position(id, arg_index)
                    && self.t_has_v_in_covariant_position(v, a)
                    || self
                        .type_has_arg_in_contravariant_position(id, arg_index)
                        && self.t_has_v_in_contravariant_position(v, a)
                    || self.tuple_has_v_in_covariant_position(
                        v,
                        b,
                        id,
                        arg_index + 1,
                    )
            }
            _ => {
                panic!()
            }
        }
    }

    fn tuple_has_v_in_contravariant_position(
        &mut self,
        v: TypeVariable,
        t: &Type,
        id: TypeId,
        arg_index: usize,
    ) -> bool {
        t.iter().any(|t| {
            self.tuple_has_v_in_contravariant_position_unit(v, t, id, arg_index)
        })
    }

    fn tuple_has_v_in_contravariant_position_unit(
        &mut self,
        v: TypeVariable,
        t: &TypeUnit,
        id: TypeId,
        arg_index: usize,
    ) -> bool {
        match t {
            TypeUnit::Const {
                id: TypeId::Intrinsic(IntrinsicType::Unit),
            } => false,
            TypeUnit::Tuple(a, b) => {
                self.type_has_arg_in_contravariant_position(id, arg_index)
                    && self.t_has_v_in_covariant_position(v, a)
                    || self.type_has_arg_in_covariant_position(id, arg_index)
                        && self.t_has_v_in_contravariant_position(v, a)
                    || self.tuple_has_v_in_contravariant_position(
                        v,
                        b,
                        id,
                        arg_index + 1,
                    )
            }
            _ => {
                panic!()
            }
        }
    }

    fn type_level_fn_has_arg_in_covariant_position(
        &mut self,
        f: &Type,
    ) -> bool {
        if let Some(b) = self.arg_of_type_level_fn_is_covariant_candidate.get(f)
        {
            *b
        } else {
            self.arg_of_type_level_fn_is_covariant_candidate
                .insert(f.clone(), false);
            if f.is_recursive_fn_apply() {
                self.type_level_fn_has_arg_in_covariant_position(
                    &f.clone().unwrap_recursive_fn_apply().0,
                )
            } else {
                let super::types::TypeMatchableRef::TypeLevelFn(t) = f.matchable_ref() else {
                   panic!()
               };
                let r = self.t_has_v_in_covariant_position(
                    TypeVariable::RecursiveIndex(0),
                    t,
                );
                if r {
                    *self
                        .arg_of_type_level_fn_is_covariant_candidate
                        .get_mut(f)
                        .unwrap() = r;
                }
                r
            }
        }
    }

    fn type_level_fn_has_arg_in_contravariant_position(
        &mut self,
        f: &Type,
    ) -> bool {
        if let Some(b) =
            self.arg_of_type_level_fn_is_contravariant_candidate.get(f)
        {
            *b
        } else {
            self.arg_of_type_level_fn_is_contravariant_candidate
                .insert(f.clone(), false);
            if f.is_recursive_fn_apply() {
                self.type_level_fn_has_arg_in_contravariant_position(
                    &f.clone().unwrap_recursive_fn_apply().0,
                )
            } else {
                let super::types::TypeMatchableRef::TypeLevelFn(t) = f.matchable_ref() else {
                   panic!()
               };
                let r = self.t_has_v_in_contravariant_position(
                    TypeVariable::RecursiveIndex(0),
                    t,
                );
                if r {
                    *self
                        .arg_of_type_level_fn_is_contravariant_candidate
                        .get_mut(f)
                        .unwrap() = r;
                }
                r
            }
        }
    }
}
