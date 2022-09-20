use self::padded_type_map::{PaddedTypeMap, TypePointer};
use crate::{
    ast_step2::{self, decl_id::DeclId, ConstructorId, TypeId},
    ast_step3::VariableId,
    ast_step4::{self, DataDecl},
    intrinsics::{IntrinsicType, IntrinsicVariable},
};
use fxhash::FxHashMap;
use itertools::Itertools;
use std::{
    collections::BTreeSet,
    convert::{TryFrom, TryInto},
    fmt::Display,
    iter,
};
use strum::IntoEnumIterator;

#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a, T = Type<'a>> {
    pub name: &'a str,
    pub value: ExprWithType<'a, T>,
    pub decl_id: DeclId,
}

pub type ExprWithType<'a, T = Type<'a>> = (Expr<'a, T>, T);

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a, T = Type<'a>> {
    Lambda(Vec<FnArm<'a, T>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident {
        name: &'a str,
        variable_id: VariableId,
        type_args: Option<Vec<T>>,
    },
    Call(Box<ExprWithType<'a, T>>, Box<ExprWithType<'a, T>>),
    DoBlock(Vec<ExprWithType<'a, T>>),
}

/// Represents a multi-case pattern which matches if any of the `PatternUnit` in it matches.
/// It should have at least one `PatternUnit`.
pub type Pattern<'a, T = Type<'a>> = (Vec<PatternUnit<'a, T>>, T);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit<'a, T> {
    I64(&'a str),
    Str(&'a str),
    Constructor {
        id: ConstructorId<'a>,
        args: Vec<Pattern<'a, T>>,
    },
    Binder(&'a str, DeclId),
    Underscore,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a, T = Type<'a>> {
    pub pattern: Vec<Pattern<'a, T>>,
    pub expr: ExprWithType<'a, T>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Clone)]
struct LinkedType<'a>(BTreeSet<LinkedTypeUnit<'a>>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum LinkedTypeUnit<'a, T = LinkedType<'a>> {
    Normal {
        name: &'a str,
        id: TypeId,
        args: Vec<T>,
    },
    Fn(T, T),
    RecursionPoint,
    RecursiveAlias(LinkedType<'a>),
    Pointer(TypePointer),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Clone)]
pub struct Type<'a>(BTreeSet<TypeUnit<'a>>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum TypeUnit<'a> {
    Normal {
        name: &'a str,
        id: TypeId,
        args: Vec<Type<'a>>,
    },
    Fn(Type<'a>, Type<'a>),
    RecursiveAlias(Type<'a>),
    RecursionPoint,
}

impl<'a> TryFrom<LinkedType<'a>> for Type<'a> {
    type Error = ();

    fn try_from(value: LinkedType<'a>) -> Result<Self, Self::Error> {
        use TypeUnit::*;
        Ok(Type(
            value
                .0
                .into_iter()
                .map(|t| match t {
                    LinkedTypeUnit::Normal { name, id, args } => {
                        let args = args
                            .into_iter()
                            .map(Type::try_from)
                            .collect::<Result<_, _>>()?;
                        Ok(Normal { name, id, args })
                    }
                    LinkedTypeUnit::Fn(a, b) => {
                        Ok(Fn(a.try_into()?, b.try_into()?))
                    }
                    LinkedTypeUnit::RecursionPoint => Ok(RecursionPoint),
                    LinkedTypeUnit::RecursiveAlias(a) => {
                        Ok(RecursiveAlias(a.try_into()?))
                    }
                    LinkedTypeUnit::Pointer(_) => Err(()),
                })
                .collect::<Result<_, _>>()?,
        ))
    }
}

impl<'a> From<ast_step4::Ast<'a>> for Ast<'a> {
    fn from(ast: ast_step4::Ast<'a>) -> Self {
        let global_variables = ast
            .variable_decl
            .iter()
            .map(|d| VariableId::Decl(d.decl_id))
            .collect_vec();
        let mut map = PaddedTypeMap::new(&global_variables);
        for d in IntrinsicVariable::iter() {
            let p = map.new_pointer();
            unify_type_with_type(&d.to_type(), p, &mut map);
            map.global_variables.insert(VariableId::Intrinsic(d), p);
        }
        let variable_decl = ast
            .variable_decl
            .into_iter()
            .map(|d| VariableDecl {
                name: d.name,
                value: {
                    let p = map.global_variables[&VariableId::Decl(d.decl_id)];
                    let e =
                        (expr(d.value, p, &Default::default(), &mut map), p);
                    e
                },
                decl_id: d.decl_id,
            })
            .collect_vec()
            .into_iter()
            .map(|d| VariableDecl {
                value: dereference_types(d.value, &mut map),
                name: d.name,
                decl_id: d.decl_id,
            })
            .collect();
        Self {
            variable_decl,
            data_decl: ast.data_decl,
            entry_point: ast.entry_point,
        }
    }
}

impl<'a> LinkedType<'a> {
    fn replace_pointer(self, from: TypePointer, to: &Self) -> (Self, bool) {
        let mut t = BTreeSet::default();
        let mut replaced = false;
        for u in self.0 {
            match u {
                LinkedTypeUnit::Pointer(p) if p == from => {
                    t.extend(to.0.iter().cloned());
                    replaced = true;
                }
                LinkedTypeUnit::Fn(a, b) => {
                    let (a, r) = a.replace_pointer(from, to);
                    replaced |= r;
                    let (b, r) = b.replace_pointer(from, to);
                    replaced |= r;
                    t.insert(LinkedTypeUnit::Fn(a, b));
                }
                LinkedTypeUnit::Normal { name, id, args } => {
                    let args = args
                        .into_iter()
                        .map(|arg| {
                            let (arg, r) = arg.replace_pointer(from, to);
                            replaced |= r;
                            arg
                        })
                        .collect();
                    t.insert(LinkedTypeUnit::Normal { name, id, args });
                }
                LinkedTypeUnit::RecursiveAlias(u) => {
                    let (u, r) = u.replace_pointer(from, to);
                    t.insert(LinkedTypeUnit::RecursiveAlias(u));
                    replaced = r;
                }
                u => {
                    t.insert(u);
                }
            }
        }
        (LinkedType(t), replaced)
    }
}

impl<'a> From<LinkedTypeUnit<'a>> for LinkedType<'a> {
    fn from(t: LinkedTypeUnit<'a>) -> Self {
        LinkedType(iter::once(t).collect())
    }
}

mod padded_type_map {
    use super::{LinkedType, LinkedTypeUnit, Type};
    use crate::{ast_step2::TypeId, ast_step3::VariableId};
    use fxhash::{FxHashMap, FxHashSet};
    use itertools::Itertools;
    use std::{convert::TryInto, iter, mem};

    #[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Copy, Hash)]
    pub struct TypePointer(usize);

    #[derive(Debug, PartialEq, Clone)]
    struct NormalType<'a> {
        name: &'a str,
        args: Vec<TypePointer>,
    }

    #[derive(Debug, PartialEq, Clone, Default)]
    pub struct TypeMap<'a> {
        function: Option<(TypePointer, TypePointer)>,
        normals: FxHashMap<TypeId, NormalType<'a>>,
    }

    #[derive(Debug, PartialEq, Clone)]
    pub enum Node<'a> {
        Pointer(TypePointer),
        Terminal(TypeMap<'a>),
    }

    pub struct PaddedTypeMap<'a> {
        map: Vec<Node<'a>>,
        pub global_variables: FxHashMap<VariableId, TypePointer>,
    }

    impl<'a> PaddedTypeMap<'a> {
        pub fn new(global_variables: &[VariableId]) -> Self {
            let map = vec![
                Node::Terminal(TypeMap::default());
                global_variables.len()
            ];
            Self {
                map,
                global_variables: global_variables
                    .iter()
                    .zip(0..)
                    .map(|(d, i)| (*d, TypePointer(i)))
                    .collect(),
            }
        }

        pub fn new_pointer(&mut self) -> TypePointer {
            let p = self.map.len();
            self.map.push(Node::Terminal(TypeMap::default()));
            TypePointer(p)
        }

        pub fn union(&mut self, a: TypePointer, b: TypePointer) {
            let a = self.find(a);
            debug_assert_eq!(a, self.find(a));
            let b = self.find(b);
            debug_assert_eq!(b, self.find(b));
            let (a, b) = if a < b { (a, b) } else { (b, a) };
            if a != b {
                let b_t = mem::replace(&mut self.map[b.0], Node::Pointer(a));
                let mut pairs = Vec::new();
                if let (Node::Terminal(a_t), Node::Terminal(b_t)) =
                    (&mut self.map[a.0], b_t)
                {
                    match (a_t.function, b_t.function) {
                        (Some((a1, a2)), Some((b1, b2))) => {
                            pairs.push((a1, b1));
                            pairs.push((a2, b2));
                        }
                        (_, Some(b)) => {
                            a_t.function = Some(b);
                        }
                        _ => (),
                    }
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
        ) {
            let p = self.find(p);
            if let Node::Terminal(t) = &mut self.map[p.0] {
                if let Some((a, b)) = t.function {
                    self.union(a, arg);
                    self.union(b, ret);
                } else {
                    t.function = Some((arg, ret));
                }
            } else {
                panic!()
            }
        }

        pub fn insert_normal(
            &mut self,
            p: TypePointer,
            id: TypeId,
            name: &'a str,
            args: Vec<TypePointer>,
        ) {
            let p = self.find(p);
            let abs = if let Node::Terminal(t) = &mut self.map[p.0] {
                if let Some(t) = t.normals.get(&id) {
                    t.args.iter().copied().zip(args).collect_vec()
                } else {
                    t.normals.insert(id, NormalType { name, args });
                    return;
                }
            } else {
                panic!()
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

        pub fn get_fn(&mut self, p: TypePointer) -> (TypePointer, TypePointer) {
            let p = self.find(p);
            if let Node::Terminal(t) = &self.map[p.0] {
                t.function
            } else {
                panic!()
            }
            .unwrap_or_else(|| {
                let a = self.new_pointer();
                let b = self.new_pointer();
                self.insert_function(p, a, b);
                (a, b)
            })
        }

        pub fn get_type(&mut self, p: TypePointer) -> Type<'a> {
            self.get_type_rec(p, Default::default()).try_into().unwrap()
        }

        fn get_type_rec(
            &mut self,
            p: TypePointer,
            mut parents: FxHashSet<TypePointer>,
        ) -> LinkedType<'a> {
            let p = self.find(p);
            if parents.contains(&p) {
                return LinkedType(
                    iter::once(LinkedTypeUnit::Pointer(p)).collect(),
                );
            }
            parents.insert(p);
            let t = if let Node::Terminal(type_map) = &self.map[p.0] {
                let mut t = Vec::default();
                if let Some((a, b)) = type_map.function {
                    t.push(LinkedTypeUnit::Fn(a, b));
                }
                for (type_id, normal_type) in &type_map.normals {
                    let n = LinkedTypeUnit::Normal {
                        name: normal_type.name,
                        id: *type_id,
                        args: normal_type.args.clone(),
                    };
                    t.push(n);
                }
                LinkedType(
                    t.into_iter()
                        .map(|t| match t {
                            LinkedTypeUnit::Fn(a, b) => LinkedTypeUnit::Fn(
                                self.get_type_rec(a, parents.clone()),
                                self.get_type_rec(b, parents.clone()),
                            ),
                            LinkedTypeUnit::Normal { name, id, args } => {
                                LinkedTypeUnit::Normal {
                                    name,
                                    id,
                                    args: args
                                        .into_iter()
                                        .map(|t| {
                                            self.get_type_rec(
                                                t,
                                                parents.clone(),
                                            )
                                        })
                                        .collect(),
                                }
                            }
                            LinkedTypeUnit::RecursiveAlias(_)
                            | LinkedTypeUnit::RecursionPoint
                            | LinkedTypeUnit::Pointer(_) => panic!(),
                        })
                        .collect(),
                )
            } else {
                panic!()
            };
            let (t, replaced) =
                t.replace_pointer(p, &LinkedTypeUnit::RecursionPoint.into());
            if replaced {
                LinkedTypeUnit::RecursiveAlias(t).into()
            } else {
                t
            }
        }
    }
}

fn expr<'a>(
    (e, _): ast_step4::ExprWithType<'a>,
    type_pointer: TypePointer,
    local_variables: &FxHashMap<VariableId, TypePointer>,
    map: &mut PaddedTypeMap<'a>,
) -> Expr<'a, TypePointer> {
    match e {
        ast_step4::Expr::Lambda(arms) => {
            let arms = arms
                .into_iter()
                .map(|arm| fn_arm(arm, local_variables, type_pointer, map))
                .collect();
            Expr::Lambda(arms)
        }
        ast_step4::Expr::Number(a) => {
            map.insert_normal(
                type_pointer,
                TypeId::Intrinsic(IntrinsicType::I64),
                "I64",
                Vec::new(),
            );
            Expr::Number(a)
        }
        ast_step4::Expr::StrLiteral(a) => {
            map.insert_normal(
                type_pointer,
                TypeId::Intrinsic(IntrinsicType::String),
                "String",
                Vec::new(),
            );
            Expr::StrLiteral(a)
        }
        ast_step4::Expr::Ident {
            name,
            variable_id,
            type_args: Some(type_args),
        } => {
            let type_id = match variable_id {
                VariableId::Decl(d) => TypeId::DeclId(d),
                VariableId::Intrinsic(i) => {
                    use crate::intrinsics::IntrinsicVariable::*;
                    TypeId::Intrinsic(match i {
                        True => IntrinsicType::True,
                        False => IntrinsicType::False,
                        Unit => IntrinsicType::Unit,
                        _ => panic!(),
                    })
                }
            };
            let (type_args, p) =
                make_constructor_type(type_args.len(), name, type_id, map);
            map.union(type_pointer, p);
            Expr::Ident {
                name,
                variable_id,
                type_args: Some(type_args),
            }
        }
        ast_step4::Expr::Ident {
            name,
            variable_id,
            type_args: None,
        } => {
            if let Some(v) = local_variables.get(&variable_id) {
                map.union(type_pointer, *v);
            } else if let Some(v) = map.global_variables.get(&variable_id) {
                map.union(type_pointer, *v);
            } else {
                panic!()
            }
            Expr::Ident {
                name,
                variable_id,
                type_args: None,
            }
        }
        ast_step4::Expr::Call(f, a) => {
            let f_t = map.new_pointer();
            let a_t = map.new_pointer();
            let (para, ret) = map.get_fn(f_t);
            let f = expr(*f, f_t, local_variables, map);
            let a = expr(*a, a_t, local_variables, map);
            map.union(a_t, para);
            map.union(type_pointer, ret);
            Expr::Call((f, f_t).into(), (a, a_t).into())
        }
        ast_step4::Expr::DoBlock(es) => {
            let es: Vec<_> = es
                .into_iter()
                .map(|e| {
                    let p = map.new_pointer();
                    (expr(e, p, local_variables, map), p)
                })
                .collect();
            map.union(type_pointer, es.last().unwrap().1);
            Expr::DoBlock(es)
        }
    }
}

fn dereference_types<'a>(
    (e, t): (Expr<'a, TypePointer>, TypePointer),
    map: &mut PaddedTypeMap<'a>,
) -> (Expr<'a, Type<'a>>, Type<'a>) {
    let e = match e {
        Expr::Lambda(arms) => Expr::Lambda(
            arms.into_iter()
                .map(|arm| dereference_types_in_fn_arm(arm, map))
                .collect(),
        ),
        Expr::Call(a, b) => Expr::Call(
            dereference_types(*a, map).into(),
            dereference_types(*b, map).into(),
        ),
        Expr::DoBlock(es) => Expr::DoBlock(
            es.into_iter().map(|e| dereference_types(e, map)).collect(),
        ),
        Expr::Number(a) => Expr::Number(a),
        Expr::StrLiteral(a) => Expr::StrLiteral(a),
        Expr::Ident {
            name,
            variable_id,
            type_args,
        } => Expr::Ident {
            name,
            variable_id,
            type_args: type_args.map(|args| {
                args.into_iter().map(|t| map.get_type(t)).collect()
            }),
        },
    };
    (e, map.get_type(t))
}

fn dereference_types_in_fn_arm<'a>(
    arm: FnArm<'a, TypePointer>,
    map: &mut PaddedTypeMap<'a>,
) -> FnArm<'a, Type<'a>> {
    FnArm {
        pattern: arm
            .pattern
            .into_iter()
            .map(|p| dereference_types_in_pattern(p, map))
            .collect(),
        expr: dereference_types(arm.expr, map),
    }
}

fn dereference_types_in_pattern<'a>(
    (pattern, t): Pattern<'a, TypePointer>,
    map: &mut PaddedTypeMap<'a>,
) -> Pattern<'a, Type<'a>> {
    use PatternUnit::*;
    let pattern = pattern
        .into_iter()
        .map(|p| match p {
            I64(a) => I64(a),
            Str(a) => Str(a),
            Constructor { id, args } => Constructor {
                id,
                args: args
                    .into_iter()
                    .map(|p| dereference_types_in_pattern(p, map))
                    .collect(),
            },
            Binder(a, b) => Binder(a, b),
            Underscore => Underscore,
        })
        .collect();
    (pattern, map.get_type(t))
}

fn make_constructor_type<'a>(
    field_len: usize,
    name: &'a str,
    id: TypeId,
    map: &mut PaddedTypeMap<'a>,
) -> (Vec<TypePointer>, TypePointer) {
    let r = map.new_pointer();
    let mut args = Vec::new();
    let mut f = r;
    for _ in 0..field_len {
        let p = map.new_pointer();
        args.push(p);
        let f_old = f;
        f = map.new_pointer();
        map.insert_function(f, p, f_old);
    }
    args.reverse();
    map.insert_normal(r, id, name, args.clone());
    (args, f)
}

fn fn_arm<'a>(
    arm: ast_step4::FnArm<'a>,
    local_variables: &FxHashMap<VariableId, TypePointer>,
    mut type_pointer: TypePointer,
    map: &mut PaddedTypeMap<'a>,
) -> FnArm<'a, TypePointer> {
    let mut local_variables = local_variables.clone();
    let mut pattern = Vec::new();
    for p in arm.pattern {
        let arg;
        (arg, type_pointer) = map.get_fn(type_pointer);
        pattern.push(unify_type_with_pattern(
            arg,
            &p,
            &mut local_variables,
            map,
        ));
    }
    let expr = expr(arm.expr, type_pointer, &local_variables, map);
    FnArm {
        pattern,
        expr: (expr, type_pointer),
    }
}

fn unify_type_with_pattern<'a>(
    type_pointer: TypePointer,
    pattern: &ast_step2::Pattern<'a>,
    local_variables: &mut FxHashMap<VariableId, TypePointer>,
    map: &mut PaddedTypeMap<'a>,
) -> Pattern<'a, TypePointer> {
    if pattern.len() != 1 {
        unimplemented!()
    } else {
        use crate::ast_step2::PatternUnit::*;
        let pattern = match &pattern[0] {
            I64(a) => {
                map.insert_normal(
                    type_pointer,
                    TypeId::Intrinsic(IntrinsicType::I64),
                    "I64",
                    Vec::new(),
                );
                PatternUnit::I64(a)
            }
            Str(a) => {
                map.insert_normal(
                    type_pointer,
                    TypeId::Intrinsic(IntrinsicType::String),
                    "String",
                    Vec::new(),
                );
                PatternUnit::Str(a)
            }
            Constructor { id, args } => {
                let args = args
                    .iter()
                    .map(|pattern| {
                        let p = map.new_pointer();
                        unify_type_with_pattern(
                            p,
                            pattern,
                            local_variables,
                            map,
                        )
                    })
                    .collect_vec();
                map.insert_normal(
                    type_pointer,
                    (*id).into(),
                    id.name(),
                    args.iter().map(|(_, p)| *p).collect(),
                );
                PatternUnit::Constructor { id: *id, args }
            }
            Binder(name, d, _) => {
                local_variables.insert(VariableId::Decl(*d), type_pointer);
                PatternUnit::Binder(name, *d)
            }
            Underscore => PatternUnit::Underscore,
            TypeRestriction(_, _) => unimplemented!(),
        };
        (vec![pattern], type_pointer)
    }
}

impl Display for Type<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0.len() {
            0 => write!(f, "∅"),
            1 => write!(f, "{}", self.0.iter().next().unwrap()),
            _ => write!(f, "{{{}}}", self.0.iter().format(" | ")),
        }
    }
}

impl Display for TypeUnit<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeUnit::Normal { name, args, .. } => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "{}[{}]", name, args.iter().format(", "))
                }
            }
            TypeUnit::Fn(a, b) => {
                if a.0.len() == 1
                    && matches!(a.0.iter().next().unwrap(), TypeUnit::Fn(_, _))
                {
                    write!(f, "({}) -> {}", a, b)
                } else {
                    write!(f, "{} -> {}", a, b)
                }
            }
            TypeUnit::RecursiveAlias(t) => write!(f, "rec[{}]", t),
            TypeUnit::RecursionPoint => write!(f, "d0"),
        }
    }
}

fn unify_type_with_type<'a>(
    t: &ast_step2::types::Type<'a>,
    p: TypePointer,
    map: &mut PaddedTypeMap<'a>,
) {
    for t in t.iter() {
        use ast_step2::types::TypeUnit::*;
        match &**t {
            Fn(a, b) => {
                let (p_a, p_b) = map.get_fn(p);
                unify_type_with_type(a, p_a, map);
                unify_type_with_type(b, p_b, map);
            }
            Tuple(a, b) => {
                let len = tuple_len(b);
                let args = (0..len).map(|_| map.new_pointer()).collect_vec();
                for a in a.iter() {
                    if let Const { name, id } = &**a {
                        unify_type_with_tuple(b, &args, map);
                        map.insert_normal(p, *id, name, args.clone());
                    } else {
                        panic!()
                    }
                }
            }
            Const { .. } | RecursiveAlias { .. } | Variable(_) => {
                unimplemented!()
            }
        }
    }
}

fn unify_type_with_tuple<'a>(
    t: &ast_step2::types::Type<'a>,
    ps: &[TypePointer],
    map: &mut PaddedTypeMap<'a>,
) {
    for t in t.iter() {
        match &**t {
            ast_step2::types::TypeUnit::Const { id, .. }
                if *id == TypeId::Intrinsic(IntrinsicType::Unit) =>
            {
                debug_assert!(ps.is_empty());
            }
            ast_step2::types::TypeUnit::Tuple(h, t) => {
                unify_type_with_type(h, ps[0], map);
                unify_type_with_tuple(t, &ps[1..], map);
            }
            _ => panic!(),
        }
    }
}

fn tuple_len(tuple: &ast_step2::types::Type<'_>) -> usize {
    use ast_step2::types::TypeUnit::*;
    tuple
        .iter()
        .next()
        .map(|t| match &**t {
            Const { id, .. }
                if *id == TypeId::Intrinsic(IntrinsicType::Unit) =>
            {
                0
            }
            Tuple(_, t) => 1 + tuple_len(t),
            _ => panic!(),
        })
        .unwrap_or(0)
}
