use super::{LambdaId, LinkedType, LinkedTypeUnit, Type};
use crate::ast_step2::TypeId;
use crate::intrinsics::IntrinsicType;
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use std::convert::TryInto;
use std::fmt::Display;
use std::{iter, mem};

#[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Copy, Hash)]
pub struct TypePointer(usize);

#[derive(Debug, PartialEq, Clone)]
struct NormalType {
    args: Vec<TypePointer>,
}

#[derive(Debug, PartialEq, Clone, Default)]
pub struct TypeMap {
    normals: FxHashMap<TypeId, NormalType>,
}

#[derive(Debug, PartialEq, Clone)]
enum Terminal {
    TypeMap(TypeMap),
    LambdaId(FxHashSet<LambdaId>),
}

#[derive(Debug, PartialEq, Clone)]
enum Node {
    Pointer(TypePointer),
    Terminal(Terminal),
}

#[derive(Debug, Default)]
pub struct PaddedTypeMap {
    map: Vec<Node>,
}

impl PaddedTypeMap {
    pub fn new_pointer(&mut self) -> TypePointer {
        let p = self.map.len();
        self.map
            .push(Node::Terminal(Terminal::TypeMap(TypeMap::default())));
        TypePointer(p)
    }

    pub fn new_lambda_id_pointer(&mut self) -> TypePointer {
        let p = self.map.len();
        self.map
            .push(Node::Terminal(Terminal::LambdaId(FxHashSet::default())));
        TypePointer(p)
    }

    pub fn union(&mut self, a: TypePointer, b: TypePointer) {
        let a = self.find(a);
        let b = self.find(b);
        let (a, b) = if a < b { (a, b) } else { (b, a) };
        if a != b {
            let b_t = mem::replace(&mut self.map[b.0], Node::Pointer(a));
            let mut pairs = Vec::new();
            if let (Node::Terminal(a_t), Node::Terminal(b_t)) =
                (&mut self.map[a.0], b_t)
            {
                match (a_t, b_t) {
                    (Terminal::TypeMap(a_t), Terminal::TypeMap(b_t)) => {
                        for (b_id, b_normal) in b_t.normals {
                            if let Some(a_normal) = a_t.normals.get(&b_id) {
                                for (a, b) in
                                    a_normal.args.iter().zip(b_normal.args)
                                {
                                    pairs.push((*a, b));
                                }
                            } else {
                                a_t.normals.insert(b_id, b_normal);
                            }
                        }
                    }
                    (Terminal::LambdaId(a), Terminal::LambdaId(b)) => {
                        a.extend(b)
                    }
                    _ => panic!(),
                }
            } else {
                panic!()
            };
            for (a, b) in pairs {
                self.union(a, b);
            }
        }
    }

    pub fn insert_function(
        &mut self,
        p: TypePointer,
        arg: TypePointer,
        ret: TypePointer,
        fn_id: TypePointer,
    ) {
        debug_assert!(matches!(self.dereference(fn_id), Terminal::LambdaId(_)));
        let t = self.dereference_mut(p);
        let Terminal::TypeMap(t) = t else {
            panic!()
        };
        if let Some(f) = t.normals.get(&TypeId::Intrinsic(IntrinsicType::Fn)) {
            let f_0 = f.args[0];
            let f_1 = f.args[1];
            let f_2 = f.args[2];
            self.union(f_0, arg);
            self.union(f_1, ret);
            self.union(f_2, fn_id);
        } else {
            t.normals.insert(
                TypeId::Intrinsic(IntrinsicType::Fn),
                NormalType {
                    args: vec![arg, ret, fn_id],
                },
            );
        }
    }

    pub fn insert_lambda_id(&mut self, p: TypePointer, id: LambdaId) {
        let t = self.dereference_mut(p);
        let Terminal::LambdaId(t) = t else {
            panic!()
        };
        t.insert(id);
    }

    pub fn insert_normal(
        &mut self,
        p: TypePointer,
        id: TypeId,
        args: Vec<TypePointer>,
    ) {
        let t = self.dereference_mut(p);
        let Terminal::TypeMap(t) = t else {
            panic!()
        };
        let abs = if let Some(t) = t.normals.get(&id) {
            t.args.iter().copied().zip(args).collect_vec()
        } else {
            t.normals.insert(id, NormalType { args });
            return;
        };
        for (a, b) in abs {
            self.union(a, b);
        }
    }

    pub fn find(&mut self, p: TypePointer) -> TypePointer {
        let next_p = match &self.map[p.0] {
            Node::Pointer(p) => *p,
            Node::Terminal(_) => {
                return p;
            }
        };
        let next_p = self.find(next_p);
        self.map[p.0] = Node::Pointer(next_p);
        debug_assert_ne!(p, next_p);
        next_p
    }

    pub fn get_fn(
        &mut self,
        p: TypePointer,
    ) -> (TypePointer, TypePointer, TypePointer) {
        let p = self.find(p);
        if let Node::Terminal(Terminal::TypeMap(t)) = &self.map[p.0] {
            t.normals
                .get(&TypeId::Intrinsic(IntrinsicType::Fn))
                .map(|f| (f.args[0], f.args[1], f.args[2]))
        } else {
            panic!()
        }
        .unwrap_or_else(|| {
            let a = self.new_pointer();
            let b = self.new_pointer();
            let fn_id = self.new_lambda_id_pointer();
            self.insert_function(p, a, b, fn_id);
            (a, b, fn_id)
        })
    }

    pub fn get_type_with_replace_map(
        &mut self,
        p: TypePointer,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
    ) -> Type {
        let replace_map = replace_map
            .iter()
            .flat_map(|(a, b)| {
                let a = self.find(*a);
                let b = self.find(*b);
                if a == b {
                    None
                } else {
                    Some((a, b))
                }
            })
            .collect();
        self.get_type_rec(p, &replace_map, Default::default())
            .try_into()
            .unwrap()
    }

    fn get_type_rec(
        &mut self,
        p: TypePointer,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        mut trace: FxHashSet<TypePointer>,
    ) -> LinkedType {
        let p = self.find(p);
        if let Some(v) = replace_map.get(&p) {
            let t = self.get_type_rec(*v, replace_map, trace);
            return t;
        }
        if trace.contains(&p) {
            return LinkedType(
                iter::once(LinkedTypeUnit::Pointer(p)).collect(),
            );
        }
        trace.insert(p);
        let t = match &self.map[p.0] {
            Node::Terminal(Terminal::TypeMap(type_map)) => {
                let mut t = Vec::default();
                for (type_id, normal_type) in &type_map.normals {
                    t.push((*type_id, normal_type.args.clone()));
                }
                LinkedType(
                    t.into_iter()
                        .map(|(id, args)| LinkedTypeUnit::Normal {
                            id,
                            args: args
                                .into_iter()
                                .map(|t| {
                                    self.get_type_rec(
                                        t,
                                        replace_map,
                                        trace.clone(),
                                    )
                                })
                                .collect(),
                        })
                        .collect(),
                )
            }
            Node::Terminal(Terminal::LambdaId(id)) => LinkedType(
                id.iter().map(|id| LinkedTypeUnit::LambdaId(*id)).collect(),
            ),
            Node::Pointer(_) => panic!(),
        };
        let (t, replaced) =
            t.replace_pointer(p, &LinkedTypeUnit::RecursionPoint.into());
        if replaced {
            LinkedTypeUnit::RecursiveAlias(t).into()
        } else {
            t
        }
    }

    fn dereference(&mut self, p: TypePointer) -> &Terminal {
        let p = self.find(p);
        if let Node::Terminal(t) = &self.map[p.0] {
            t
        } else {
            panic!()
        }
    }

    fn dereference_mut(&mut self, p: TypePointer) -> &mut Terminal {
        let p = self.find(p);
        if let Node::Terminal(t) = &mut self.map[p.0] {
            t
        } else {
            panic!()
        }
    }

    pub fn clone_pointer(&mut self, p: TypePointer) -> TypePointer {
        self.clone_pointer_rec(p, &mut Default::default())
    }

    pub fn clone_pointer_rec(
        &mut self,
        p: TypePointer,
        replace_map: &mut FxHashMap<TypePointer, TypePointer>,
    ) -> TypePointer {
        let p = self.find(p);
        if let Some(p) = replace_map.get(&p) {
            return *p;
        }
        let new_p = self.new_pointer();
        replace_map.insert(p, new_p);
        let t = self.dereference(p).clone();
        let t = match t {
            Terminal::TypeMap(t) => Terminal::TypeMap(TypeMap {
                normals: t
                    .normals
                    .iter()
                    .map(|(id, t)| {
                        (
                            *id,
                            NormalType {
                                args: t
                                    .args
                                    .iter()
                                    .map(|p| {
                                        let p = self.find(*p);
                                        self.clone_pointer_rec(p, replace_map)
                                    })
                                    .collect(),
                            },
                        )
                    })
                    .collect(),
            }),
            Terminal::LambdaId(t) => Terminal::LambdaId(t),
        };
        self.map[new_p.0] = Node::Terminal(t);
        new_p
    }
}

impl Display for TypePointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "p{}", self.0)
    }
}
