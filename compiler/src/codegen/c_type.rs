use super::collector::Collector;
use crate::ast_step4::{self, TypeId};
use crate::ast_step5::{FxLambdaId as LambdaId, Type, TypeInner, TypeUnit};
use crate::intrinsics::IntrinsicType;
use fxhash::{FxHashMap, FxHashSet};
use std::fmt::Display;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum CType {
    Int,
    String,
    Aggregate(usize),
    Ref(Box<CType>),
}

impl Display for CType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CType::Int => write!(f, "int"),
            CType::String => write!(f, "char*"),
            CType::Aggregate(i) => write!(f, "struct t{i}"),
            CType::Ref(i) => write!(f, "{i}*"),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum CAggregateType {
    Union(Vec<CType>),
    Struct(Vec<CType>),
}

pub struct Env {
    pub function_context: FxHashMap<LambdaId, Vec<Type>>,
    pub aggregate_types: Collector<CAggregateType>,
    pub memo: FxHashMap<Type, CType>,
    pub fx_type_map: FxHashMap<ast_step4::LambdaId<Type>, LambdaId>,
    pub reffed_aggregates: FxHashSet<usize>,
}

impl Env {
    fn c_type_inner(
        &mut self,
        t: &Type,
        mut type_stack: Option<(usize, Type)>,
    ) -> CType {
        debug_assert!(!t.reference);
        let single = if t.len() == 1 {
            match t.iter().next().unwrap() {
                TypeUnit::Normal { .. } => true,
                TypeUnit::Fn(l, _, _) => l.len() == 1,
            }
        } else {
            false
        };
        let reserved_id;
        if t.recursive {
            let i = self.aggregate_types.get_empty_id();
            debug_assert!(!t.contains_broken_link());
            type_stack = Some((
                i,
                Type {
                    reference: true,
                    ..t.clone()
                },
            ));
            reserved_id = Some(i);
        } else {
            reserved_id = None;
        }
        let mut ts = Vec::new();
        debug_assert!(!t.contains_broken_link_rec(type_stack.is_some() as u32));
        for tu in t.iter() {
            use TypeUnit::*;
            match tu {
                Normal { id, args } => match id {
                    TypeId::Intrinsic(IntrinsicType::String)
                    | TypeId::Intrinsic(IntrinsicType::I64) => {
                        let c_t = match id {
                            TypeId::Intrinsic(IntrinsicType::String) => {
                                CType::String
                            }
                            TypeId::Intrinsic(IntrinsicType::I64) => CType::Int,
                            _ => panic!(),
                        };
                        if single {
                            debug_assert!(reserved_id.is_none());
                            return c_t;
                        }
                        ts.push(c_t);
                    }
                    _ => {
                        let t = CAggregateType::Struct(
                            args.iter()
                                .map(|t| match t {
                                    TypeInner::RecursionPoint(d) => {
                                        assert_eq!(*d, 0);
                                        CType::Ref(Box::new(CType::Aggregate(
                                            type_stack.as_ref().unwrap().0,
                                        )))
                                    }
                                    TypeInner::Type(t) => {
                                        self.c_type(t, type_stack.clone())
                                    }
                                })
                                .collect(),
                        );
                        if single {
                            return match reserved_id {
                                Some(i) => {
                                    debug_assert!(ts.is_empty());
                                    self.aggregate_types.insert_with_id(t, i);
                                    CType::Aggregate(i)
                                }
                                None => CType::Aggregate(
                                    self.aggregate_types.get(t),
                                ),
                            };
                        }
                        ts.push(CType::Aggregate(self.aggregate_types.get(t)));
                    }
                },
                Fn(lambda_id, _, _) => {
                    for l in lambda_id {
                        let l = l.map_type_ref(|t| {
                            if let TypeInner::Type(t) = t {
                                debug_assert!(!t.contains_broken_link());
                                t.clone()
                            } else {
                                panic!()
                            }
                        });
                        let l = self.fx_type_map[&l];
                        let ctx = self.function_context[&l].clone();
                        let c_t = CAggregateType::Struct(
                            ctx.iter()
                                .map(|t| self.c_type(t, type_stack.clone()))
                                .collect(),
                        );
                        match reserved_id {
                            Some(i) if single => {
                                self.aggregate_types.insert_with_id(
                                    CAggregateType::Union(ts),
                                    i,
                                );
                                return CType::Aggregate(i);
                            }
                            _ => (),
                        }
                        ts.push(CType::Aggregate(self.aggregate_types.get(c_t)))
                    }
                }
            }
        }
        if let Some(i) = reserved_id {
            debug_assert!(ts.len() >= 2);
            self.aggregate_types
                .insert_with_id(CAggregateType::Union(ts), i);
            CType::Aggregate(i)
        } else if ts.len() == 1 {
            ts.into_iter().next().unwrap()
        } else {
            CType::Aggregate(
                self.aggregate_types.get(CAggregateType::Union(ts)),
            )
        }
    }

    fn c_type_memoize(
        &mut self,
        t: &Type,
        type_stack: Option<(usize, Type)>,
    ) -> CType {
        if let Some(t) = self.memo.get(t) {
            t.clone()
        } else if type_stack.is_none() {
            let c_t = self.c_type_inner(t, type_stack);
            let o = self.memo.insert(t.clone(), c_t.clone());
            #[cfg(debug_assertions)]
            if let Some(t) = o {
                assert_eq!(t, c_t);
            }
            c_t
        } else {
            self.c_type_inner(t, type_stack)
        }
    }

    pub fn c_type(
        &mut self,
        t: &Type,
        type_stack: Option<(usize, Type)>,
    ) -> CType {
        debug_assert!(!t.contains_broken_link_rec(type_stack.is_some() as u32));
        if t.reference {
            let t = self.c_type_memoize(
                &Type {
                    reference: false,
                    ..t.clone()
                },
                type_stack,
            );
            let i = match t {
                CType::Aggregate(i) => i,
                _ => panic!(),
            };
            self.reffed_aggregates.insert(i);
            CType::Ref(Box::new(t))
        } else {
            self.c_type_memoize(t, type_stack)
        }
    }
}
