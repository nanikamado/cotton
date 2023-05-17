use super::LambdaId;
use crate::ast_step1::{
    ConstructorNames, PaddedTypeMap, Terminal, TypeId, TypePointer,
};
use crate::intrinsics::IntrinsicType;
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use std::collections::BTreeSet;
use std::fmt::{self, Display};
use std::iter::once;

#[derive(PartialEq, Eq, PartialOrd, Ord, Default, Clone, Hash)]
pub struct Type<R = u32> {
    ts: Vec<TypeUnit<R>>,
    pub recursive: bool,
    pub reference: bool,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum TypeInner<R = u32> {
    RecursionPoint(R),
    Type(Type<R>),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum TypeUnit<R = u32> {
    Normal { id: TypeId, args: Vec<TypeInner<R>> },
    Fn(BTreeSet<LambdaId<TypeInner<R>>>, TypeInner<R>, TypeInner<R>),
}

impl From<TypeUnit> for Type {
    fn from(value: TypeUnit) -> Self {
        Type {
            ts: once(value).collect(),
            recursive: false,
            reference: false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
enum IndexOrPointer {
    Index(u32),
    Pointer(TypePointer),
}

impl Type {
    pub fn iter(&self) -> impl Iterator<Item = &TypeUnit> {
        self.ts.iter()
    }

    pub fn len(&self) -> usize {
        self.ts.len()
    }

    pub fn contains_broken_link_rec(&self, depth: u32) -> bool {
        let depth = self.recursive as u32 + depth;
        self.ts.iter().any(|t| match t {
            TypeUnit::Normal { id: _, args } => {
                args.iter().any(|a| a.contains_broken_link(depth))
            }
            TypeUnit::Fn(l, a, r) => {
                l.iter().any(|l| l.root_t.contains_broken_link(depth))
                    || a.contains_broken_link(depth)
                    || r.contains_broken_link(depth)
            }
        })
    }

    pub fn contains_broken_link(&self) -> bool {
        self.contains_broken_link_rec(0)
    }

    pub fn deref(self) -> Self {
        debug_assert!(self.recursive);
        debug_assert!(self.reference);
        Self {
            reference: false,
            ..self
        }
    }

    pub fn get_ref(self) -> Self {
        debug_assert!(self.recursive);
        debug_assert!(!self.reference);
        Self {
            reference: true,
            ..self
        }
    }
}

impl TypeInner {
    pub fn contains_broken_link(&self, depth: u32) -> bool {
        match self {
            TypeInner::RecursionPoint(d) => *d >= depth,
            TypeInner::Type(t) => t.contains_broken_link_rec(depth),
        }
    }
}

#[derive(Debug, Default)]
pub struct UnhashableTypeMemo {
    type_memo: FxHashMap<TypePointer, TypeInner<IndexOrPointer>>,
    type_memo_for_hash: FxHashMap<TypePointer, TypeInner<IndexOrPointer>>,
}

fn remove_pointer_from_type_inner(t: TypeInner<IndexOrPointer>) -> TypeInner {
    match t {
        TypeInner::RecursionPoint(IndexOrPointer::Pointer(_)) => {
            panic!()
        }
        TypeInner::RecursionPoint(IndexOrPointer::Index(d)) => {
            TypeInner::RecursionPoint(d)
        }
        TypeInner::Type(Type {
            ts,
            recursive,
            reference,
        }) => TypeInner::Type(Type {
            ts: ts.into_iter().map(remove_pointer_from_type_unit).collect(),
            recursive,
            reference,
        }),
    }
}

fn remove_pointer_from_type_unit(t: TypeUnit<IndexOrPointer>) -> TypeUnit {
    match t {
        TypeUnit::Normal { id, args } => TypeUnit::Normal {
            id,
            args: args
                .into_iter()
                .map(remove_pointer_from_type_inner)
                .collect(),
        },
        TypeUnit::Fn(id, a, b) => TypeUnit::Fn(
            id.into_iter()
                .map(|l| l.map_type(remove_pointer_from_type_inner))
                .collect(),
            remove_pointer_from_type_inner(a),
            remove_pointer_from_type_inner(b),
        ),
    }
}

impl UnhashableTypeMemo {
    pub fn get_type(
        &mut self,
        p: TypePointer,
        map: &mut PaddedTypeMap,
    ) -> Type {
        self.get_type_aux(p, map, false)
    }

    pub fn get_type_for_hash(
        &mut self,
        p: TypePointer,
        map: &mut PaddedTypeMap,
    ) -> Type {
        self.get_type_aux(p, map, true)
    }

    fn get_type_aux(
        &mut self,
        p: TypePointer,
        map: &mut PaddedTypeMap,
        for_hash: bool,
    ) -> Type {
        let t = self.get_type_inner(p, &Default::default(), map, for_hash);
        match remove_pointer_from_type_inner(t) {
            TypeInner::RecursionPoint(_) => panic!(),
            TypeInner::Type(t) => {
                debug_assert!(!t.contains_broken_link());
                t
            }
        }
    }

    fn get_lambda_ids(
        &mut self,
        p: TypePointer,
        trace: &FxHashSet<TypePointer>,
        map: &mut PaddedTypeMap,
    ) -> BTreeSet<LambdaId<TypeInner<IndexOrPointer>>> {
        let Terminal::LambdaId(ids) = map.dereference_without_find(p) else {
            panic!()
        };
        let mut new_ids = BTreeSet::new();
        for id in ids.clone() {
            let id = id.map_type(|p| self.get_type_inner(p, trace, map, true));
            new_ids.insert(id);
        }
        new_ids
    }

    fn get_type_inner(
        &mut self,
        p: TypePointer,
        trace: &FxHashSet<TypePointer>,
        map: &mut PaddedTypeMap,
        for_hash: bool,
    ) -> TypeInner<IndexOrPointer> {
        if for_hash {
            if let Some(t) = self.type_memo_for_hash.get(&p) {
                return t.clone();
            }
        } else if let Some(t) = self.type_memo.get(&p) {
            return t.clone();
        }
        if trace.contains(&p) {
            return TypeInner::RecursionPoint(IndexOrPointer::Pointer(p));
        }
        let mut trace = trace.clone();
        trace.insert(p);
        let t = match &map.dereference_without_find(p) {
            Terminal::TypeMap(type_map) => {
                let mut t = Vec::new();
                for (type_id, normal_type) in &type_map.normals {
                    t.push((*type_id, normal_type.clone()));
                }
                TypeInner::Type(Type {
                    ts: t
                        .into_iter()
                        .map(|(id, args)| {
                            self.get_type_from_id_and_args_rec(
                                id, &args, &trace, map, for_hash,
                            )
                        })
                        .collect(),
                    recursive: false,
                    reference: false,
                })
            }
            Terminal::LambdaId(_) => panic!(),
        };
        let r = replace_pointer(t, p, 0);
        let mut t = r.t;
        if r.replaced {
            if let TypeInner::Type(t) = &mut t {
                t.recursive = true;
                t.reference = true;
            } else {
                panic!()
            }
        };
        if !r.contains_pointer {
            let o = if for_hash {
                self.type_memo_for_hash.insert(p, t.clone())
            } else {
                self.type_memo.insert(p, t.clone())
            };
            debug_assert!(o.is_none());
        }
        t
    }

    fn get_type_from_id_and_args_rec(
        &mut self,
        id: TypeId,
        args: &[TypePointer],
        trace: &FxHashSet<TypePointer>,
        map: &mut PaddedTypeMap,
        for_hash: bool,
    ) -> TypeUnit<IndexOrPointer> {
        if let TypeId::Intrinsic(IntrinsicType::Fn) = id {
            debug_assert_eq!(args.len(), 3);
            let mut args = args.iter();
            let a = self.get_type_inner(
                *args.next().unwrap(),
                trace,
                map,
                for_hash,
            );
            let b = self.get_type_inner(
                *args.next().unwrap(),
                trace,
                map,
                for_hash,
            );
            let empty_trace;
            let lambda_id = self.get_lambda_ids(
                *args.next().unwrap(),
                if for_hash {
                    trace
                } else {
                    empty_trace = Default::default();
                    &empty_trace
                },
                map,
            );
            TypeUnit::Fn(lambda_id, a, b)
        } else {
            TypeUnit::Normal {
                id,
                args: args
                    .iter()
                    .map(|t| self.get_type_inner(*t, trace, map, for_hash))
                    .collect(),
            }
        }
    }
}

struct ReplacePointerResult {
    t: TypeInner<IndexOrPointer>,
    replaced: bool,
    contains_pointer: bool,
}

fn replace_pointer(
    t: TypeInner<IndexOrPointer>,
    from: TypePointer,
    depth: u32,
) -> ReplacePointerResult {
    match t {
        TypeInner::RecursionPoint(IndexOrPointer::Index(i)) => {
            ReplacePointerResult {
                t: TypeInner::RecursionPoint(IndexOrPointer::Index(i)),
                replaced: false,
                contains_pointer: i > depth,
            }
        }
        TypeInner::RecursionPoint(IndexOrPointer::Pointer(i)) => {
            if i == from {
                ReplacePointerResult {
                    t: TypeInner::RecursionPoint(IndexOrPointer::Index(depth)),
                    replaced: true,
                    contains_pointer: false,
                }
            } else {
                ReplacePointerResult {
                    t: TypeInner::RecursionPoint(IndexOrPointer::Pointer(i)),
                    replaced: false,
                    contains_pointer: true,
                }
            }
        }
        TypeInner::Type(t) => {
            let depth = t.recursive as u32 + depth;
            let mut new_t = Vec::new();
            let mut replaced = false;
            let mut contains_pointer = false;
            use TypeUnit::*;
            for u in t.ts {
                match u {
                    Normal { id, args } => {
                        let args = args
                            .into_iter()
                            .map(|arg| {
                                let r = replace_pointer(arg, from, depth);
                                replaced |= r.replaced;
                                contains_pointer |= r.contains_pointer;
                                r.t
                            })
                            .collect();
                        new_t.push(Normal { id, args });
                    }
                    Fn(l, a, b) => {
                        let l = l
                            .into_iter()
                            .map(|l| {
                                l.map_type(|t| {
                                    let r = replace_pointer(t, from, depth);
                                    replaced |= r.replaced;
                                    contains_pointer |= r.contains_pointer;
                                    r.t
                                })
                            })
                            .collect();
                        let r = replace_pointer(a, from, depth);
                        replaced |= r.replaced;
                        contains_pointer |= r.contains_pointer;
                        let a = r.t;
                        let r = replace_pointer(b, from, depth);
                        replaced |= r.replaced;
                        contains_pointer |= r.contains_pointer;
                        let b = r.t;
                        new_t.push(Fn(l, a, b));
                    }
                }
            }
            ReplacePointerResult {
                t: TypeInner::Type(Type {
                    ts: new_t,
                    recursive: t.recursive,
                    reference: t.reference,
                }),
                replaced,
                contains_pointer,
            }
        }
    }
}

pub enum GetTagNormalResult {
    NotTagged,
    Impossible,
    Tagged(u32, TypeUnit),
}

pub fn get_tag_normal(ot: &Type, type_id: TypeId) -> GetTagNormalResult {
    debug_assert_ne!(type_id, TypeId::Intrinsic(IntrinsicType::Fn));
    let mut tag = 0;
    if ot.len() == 1 {
        let t = ot.ts.first().unwrap();
        match t {
            TypeUnit::Normal { id, .. } => {
                return if *id == type_id {
                    GetTagNormalResult::NotTagged
                } else {
                    GetTagNormalResult::Impossible
                };
            }
            TypeUnit::Fn(_, _, _) => panic!(),
        }
    }
    for t in &ot.ts {
        match t {
            TypeUnit::Normal { id, args } if *id == type_id => {
                let t = if ot.recursive {
                    TypeUnit::Normal {
                        id: *id,
                        args: args
                            .iter()
                            .map(|a| a.clone().replace_index(ot, 0))
                            .collect(),
                    }
                } else {
                    t.clone()
                };
                return GetTagNormalResult::Tagged(tag, t);
            }
            TypeUnit::Fn(lambda_ids, _, _) => {
                tag += lambda_ids.len() as u32;
            }
            _ => {
                tag += 1;
            }
        }
    }
    GetTagNormalResult::Impossible
}

impl TypeInner {
    pub fn replace_index(self, to: &Type, depth: u32) -> Self {
        debug_assert!(to.reference);
        match self {
            TypeInner::RecursionPoint(a) if a == depth => {
                TypeInner::Type(to.clone())
            }
            TypeInner::RecursionPoint(a) => TypeInner::RecursionPoint(a),
            TypeInner::Type(Type {
                ts,
                recursive,
                reference,
            }) => TypeInner::Type(Type {
                ts: ts
                    .into_iter()
                    .map(|t| t.replace_index(to, depth + recursive as u32))
                    .collect(),
                recursive,
                reference,
            }),
        }
    }
}

impl TypeUnit {
    pub fn replace_index(self, to: &Type, depth: u32) -> Self {
        debug_assert!(to.reference);
        match self {
            TypeUnit::Normal { id, args } => TypeUnit::Normal {
                id,
                args: args
                    .into_iter()
                    .map(|t| t.replace_index(to, depth))
                    .collect(),
            },
            TypeUnit::Fn(ids, a, b) => TypeUnit::Fn(
                ids,
                a.replace_index(to, depth),
                b.replace_index(to, depth),
            ),
        }
    }
}

pub struct DisplayTypeWithEnv<'a, T>(pub &'a T, pub &'a ConstructorNames);

impl<R: fmt::Debug> fmt::Display for DisplayTypeWithEnv<'_, Type<R>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.recursive {
            write!(f, "rec[")?;
        }
        if self.0.reference {
            write!(f, "&")?;
        }
        match self.0.ts.len() {
            0 => write!(f, "Never"),
            1 => {
                write!(
                    f,
                    "{}",
                    DisplayTypeWithEnv(self.0.ts.first().unwrap(), self.1)
                )
            }
            _ => write!(
                f,
                "({})",
                self.0.ts.iter().format_with(" | ", |t, f| f(
                    &DisplayTypeWithEnv(t, self.1)
                ))
            ),
        }?;
        if self.0.recursive {
            write!(f, "]")?;
        }
        Ok(())
    }
}

impl<R: fmt::Debug> Display for DisplayTypeWithEnv<'_, TypeInner<R>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            TypeInner::RecursionPoint(d) => {
                write!(f, "d{d:?}")
            }
            TypeInner::Type(t) => {
                write!(f, "{}", DisplayTypeWithEnv(t, self.1))
            }
        }
    }
}

impl<R: fmt::Debug> Display for DisplayTypeWithEnv<'_, TypeUnit<R>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeUnit::*;
        match self.0 {
            Normal { args, id } => {
                debug_assert_ne!(*id, TypeId::Intrinsic(IntrinsicType::Fn));
                match id {
                    TypeId::UserDefined(u) => {
                        write!(f, "{}", self.1.get(*u))?;
                    }
                    TypeId::Intrinsic(d) => {
                        write!(f, "{d:?}")?;
                    }
                }
                if !args.is_empty() {
                    write!(
                        f,
                        "[{}]",
                        args.iter().format_with(", ", |a, f| f(
                            &DisplayTypeWithEnv(a, self.1)
                        ))
                    )?;
                };
                Ok(())
            }
            Fn(id, a, b) => {
                let id_paren = id.len() >= 2;
                write!(
                    f,
                    "({}) -{}{}{}-> {}",
                    DisplayTypeWithEnv(a, self.1),
                    if id_paren { "(" } else { "" },
                    id.iter().format_with(" | ", |a, f| f(
                        &DisplayTypeWithEnv(a, self.1)
                    )),
                    if id_paren { ")" } else { "" },
                    DisplayTypeWithEnv(b, self.1)
                )
            }
        }
    }
}

impl<R: fmt::Debug> Display for DisplayTypeWithEnv<'_, LambdaId<TypeInner<R>>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "f{}({})",
            self.0.id,
            DisplayTypeWithEnv(&self.0.root_t, self.1)
        )
    }
}

impl<R: fmt::Debug> fmt::Debug for Type<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.recursive {
            write!(f, "rec[")?;
        }
        if self.reference {
            write!(f, "&")?;
        }
        match self.ts.len() {
            0 => write!(f, "Never"),
            1 => write!(f, "{:?}", self.ts.first().unwrap()),
            _ => write!(f, "({:?})", self.ts.iter().format(" | ")),
        }?;
        if self.recursive {
            write!(f, "]")?;
        }
        Ok(())
    }
}

impl<R: fmt::Debug> fmt::Debug for TypeInner<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeInner::RecursionPoint(d) => {
                write!(f, "d{d:?}")
            }
            TypeInner::Type(t) => write!(f, "{t:?}"),
        }
    }
}

impl<R: fmt::Debug> fmt::Debug for TypeUnit<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeUnit::*;
        match self {
            Normal { args, id } => {
                debug_assert_ne!(*id, TypeId::Intrinsic(IntrinsicType::Fn));
                if args.is_empty() {
                    write!(f, "{id}")
                } else {
                    write!(f, "{}[{:?}]", id, args.iter().format(", "))
                }
            }
            Fn(id, a, b) => {
                let id_paren = id.len() >= 2;
                write!(
                    f,
                    "({a:?}) -{}{}{}-> {b:?}",
                    if id_paren { "(" } else { "" },
                    id.iter()
                        .format_with(" | ", |a, f| f(&format_args!("{:?}", a))),
                    if id_paren { ")" } else { "" },
                )
            }
        }
    }
}
