pub use self::replace_map::ReplaceMap;
use super::{LambdaId, LinkedType, LinkedTypeUnit, TypeForHash};
use crate::ast_step2::TypeId;
use crate::intrinsics::IntrinsicType;
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use std::collections::BTreeSet;
use std::convert::TryInto;
use std::fmt::Display;
use std::{iter, mem};

#[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Copy, Hash)]
pub struct TypePointer(usize);

#[derive(Debug, PartialEq, Clone, Default)]
pub struct TypeMap {
    pub normals: FxHashMap<TypeId, Vec<TypePointer>>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Terminal {
    TypeMap(TypeMap),
    LambdaId(FxHashSet<LambdaId<TypePointer>>),
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
                                for (a, b) in a_normal.iter().zip(b_normal) {
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
            let f_0 = f[0];
            let f_1 = f[1];
            let f_2 = f[2];
            self.union(f_0, arg);
            self.union(f_1, ret);
            self.union(f_2, fn_id);
        } else {
            t.normals.insert(
                TypeId::Intrinsic(IntrinsicType::Fn),
                vec![arg, ret, fn_id],
            );
        }
    }

    pub fn insert_lambda_id(
        &mut self,
        p: TypePointer,
        id: LambdaId<TypePointer>,
    ) {
        let t = self.dereference_mut(p);
        let Terminal::LambdaId(t) = t else {
            panic!()
        };
        t.insert(id);
    }

    pub fn get_lambda_id<'a>(
        &'a mut self,
        p: TypePointer,
        replace_map: &mut ReplaceMap,
    ) -> &'a FxHashSet<LambdaId<TypePointer>> {
        let t = self.dereference_with_replace_map(p, replace_map);
        let Terminal::LambdaId(t) = t else {
            panic!()
        };
        t
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
            t.iter().copied().zip(args).collect_vec()
        } else {
            t.normals.insert(id, args);
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
                .map(|f| (f[0], f[1], f[2]))
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
        replace_map: &mut ReplaceMap,
    ) -> TypeForHash {
        self.get_type(p, replace_map, Default::default())
            .try_into()
            .unwrap()
    }

    fn get_type(
        &mut self,
        p: TypePointer,
        replace_map: &mut ReplaceMap,
        mut trace: FxHashSet<TypePointer>,
    ) -> LinkedType {
        let p = replace_map.get(p, self);
        if trace.contains(&p) {
            return LinkedType {
                ts: iter::once(LinkedTypeUnit::Pointer(p)).collect(),
                recursive: false,
            };
        }
        trace.insert(p);
        let t = match &self.map[p.0] {
            Node::Terminal(Terminal::TypeMap(type_map)) => {
                let mut t = Vec::default();
                for (type_id, normal_type) in &type_map.normals {
                    t.push((*type_id, normal_type.clone()));
                }
                LinkedType {
                    ts: t
                        .into_iter()
                        .map(|(id, args)| LinkedTypeUnit::Normal {
                            id,
                            args: args
                                .into_iter()
                                .map(|t| {
                                    self.get_type(t, replace_map, trace.clone())
                                })
                                .collect(),
                        })
                        .collect(),
                    recursive: false,
                }
            }
            Node::Terminal(Terminal::LambdaId(ids)) => {
                let mut new_ids = BTreeSet::new();
                for id in ids.clone() {
                    let id = id.map_type(|t| {
                        self.get_type(t, replace_map, trace.clone())
                    });
                    new_ids.insert(LinkedTypeUnit::LambdaId(id));
                }
                LinkedType {
                    ts: new_ids,
                    recursive: false,
                }
            }
            Node::Pointer(_) => panic!(),
        };
        let r = t.replace_pointer(p, 0);
        let mut t = r.t;
        if r.replaced {
            t.recursive = true;
        };
        t
    }

    fn dereference(&mut self, p: TypePointer) -> &Terminal {
        let p = self.find(p);
        if let Node::Terminal(t) = &self.map[p.0] {
            t
        } else {
            panic!()
        }
    }

    pub fn dereference_without_find(&self, p: TypePointer) -> &Terminal {
        if let Node::Terminal(t) = &self.map[p.0] {
            t
        } else {
            panic!()
        }
    }

    fn dereference_with_replace_map(
        &mut self,
        p: TypePointer,
        replace_map: &mut ReplaceMap,
    ) -> &Terminal {
        let p = replace_map.get(p, self);
        self.dereference(p)
    }

    fn dereference_mut(&mut self, p: TypePointer) -> &mut Terminal {
        let p = self.find(p);
        if let Node::Terminal(t) = &mut self.map[p.0] {
            t
        } else {
            panic!()
        }
    }

    pub fn clone_pointer(
        &mut self,
        p: TypePointer,
        replace_map: &mut ReplaceMap,
    ) -> TypePointer {
        let p = self.find(p);
        if let Some(p) = replace_map.get_option(p, self) {
            return p;
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
                            t.iter()
                                .map(|p| {
                                    let p = self.find(*p);
                                    self.clone_pointer(p, replace_map)
                                })
                                .collect(),
                        )
                    })
                    .collect(),
            }),
            Terminal::LambdaId(t) => Terminal::LambdaId(
                t.into_iter()
                    .map(|t| {
                        LambdaId(t.0, self.clone_pointer(t.1, replace_map))
                    })
                    .collect(),
            ),
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

mod replace_map {
    use super::PaddedTypeMap;
    use crate::ast_step4::TypePointer;
    use fxhash::FxHashMap;

    #[derive(Debug, Default, Clone, PartialEq, Eq)]
    pub struct ReplaceMap(FxHashMap<TypePointer, TypePointer>);

    impl ReplaceMap {
        pub fn merge(mut self, other: Self) -> Self {
            self.0.extend(other.0);
            self
        }

        pub fn get(
            &mut self,
            p: TypePointer,
            map: &mut PaddedTypeMap,
        ) -> TypePointer {
            let p = map.find(p);
            if let Some(p2) = self.0.get(&p) {
                let p2 = self.get(*p2, map);
                self.0.insert(p, p2);
                p2
            } else {
                p
            }
        }

        pub fn get_option(
            &mut self,
            p: TypePointer,
            map: &mut PaddedTypeMap,
        ) -> Option<TypePointer> {
            if let Some(p2) = self.0.get(&p) {
                let p2 = self.get(*p2, map);
                self.0.insert(p, p2);
                Some(p2)
            } else {
                None
            }
        }

        pub fn insert(&mut self, from: TypePointer, to: TypePointer) {
            self.0.insert(from, to);
        }
    }
}

impl Display for Terminal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Terminal::TypeMap(tm) => {
                write!(
                    f,
                    "{}",
                    tm.normals.iter().format_with(" | ", |(id, args), f| {
                        f(&format_args!("{id}({})", args.iter().format(", ")))
                    })
                )
            }
            Terminal::LambdaId(l) => {
                write!(f, "lambda({})", l.iter().format(" | "))
            }
        }
    }
}
