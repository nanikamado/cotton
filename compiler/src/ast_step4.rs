pub use self::padded_type_map::{PaddedTypeMap, TypePointer};
use crate::{
    ast_step2::{self, decl_id::DeclId, name_id::Name, ConstructorId, TypeId},
    ast_step3::VariableId,
    ast_step3::{self, DataDecl},
    intrinsics::{IntrinsicConstructor, IntrinsicType, IntrinsicVariable},
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

#[derive(Debug)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl<TypePointer>>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: DeclId,
    pub map: PaddedTypeMap,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<T = Type> {
    pub name: Name,
    pub value: ExprWithType<T>,
    pub decl_id: DeclId,
}

pub type ExprWithType<T = Type> = (Expr<T>, T);

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash, Copy)]
pub enum VariableKind {
    Local,
    Global,
    Constructor,
    Intrinsic,
    IntrinsicConstructor,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<T = Type> {
    Lambda(Vec<FnArm<T>>),
    Number(Name),
    StrLiteral(Name),
    Ident {
        name: Name,
        variable_id: VariableId,
        variable_kind: VariableKind,
    },
    GlobalVariable {
        name: Name,
        decl_id: DeclId,
        replace_map: FxHashMap<TypePointer, TypePointer>,
    },
    Call(Box<ExprWithType<T>>, Box<ExprWithType<T>>),
    DoBlock(Vec<ExprWithType<T>>),
}

/// Represents a multi-case pattern which matches if any of the `PatternUnit` in it matches.
/// It should have at least one `PatternUnit`.
pub type Pattern<T = Type> = (Vec<PatternUnit<T>>, T);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit<T> {
    I64(Name),
    Str(Name),
    Constructor {
        name: Name,
        id: ConstructorId,
        args: Vec<Pattern<T>>,
    },
    Binder(Name, DeclId),
    Underscore,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<T = Type> {
    pub pattern: Vec<Pattern<T>>,
    pub expr: ExprWithType<T>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Clone)]
struct LinkedType(BTreeSet<LinkedTypeUnit>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum LinkedTypeUnit<T = LinkedType> {
    Normal {
        name: Name,
        id: TypeId,
        args: Vec<T>,
    },
    Fn(T, T),
    RecursionPoint,
    RecursiveAlias(LinkedType),
    Pointer(TypePointer),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Clone)]
pub struct Type(BTreeSet<TypeUnit>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum TypeUnit {
    Normal {
        name: Name,
        id: TypeId,
        args: Vec<Type>,
    },
    Fn(Type, Type),
    RecursiveAlias(Type),
    RecursionPoint,
}

impl TryFrom<LinkedType> for Type {
    type Error = ();

    fn try_from(value: LinkedType) -> Result<Self, Self::Error> {
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

impl Ast {
    pub fn from(
        ast: ast_step3::Ast,
        type_names: &FxHashMap<TypeId, Name>,
    ) -> Self {
        let mut memo = VariableMemo::new(ast.variable_decl, &ast.data_decl);
        for d in IntrinsicVariable::iter() {
            let p = memo.type_map.new_pointer();
            unify_type_with_ast_sep2_type(
                &d.to_type(),
                p,
                &mut memo.type_map,
                type_names,
            );
            memo.intrinsic_variables
                .insert(VariableId::IntrinsicVariable(d), p);
        }
        for d in IntrinsicConstructor::iter() {
            let p = memo.type_map.new_pointer();
            unify_type_with_ast_sep2_type(
                &d.to_type(),
                p,
                &mut memo.type_map,
                type_names,
            );
            memo.intrinsic_variables
                .insert(VariableId::IntrinsicConstructor(d), p);
        }
        memo.get_type_global(
            VariableId::Decl(ast.entry_point),
            &Default::default(),
        );
        let map = memo.type_map;
        Self {
            variable_decl: memo.global_variables_done,
            data_decl: ast.data_decl,
            entry_point: ast.entry_point,
            map,
        }
    }
}

impl LinkedType {
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

impl From<LinkedTypeUnit> for LinkedType {
    fn from(t: LinkedTypeUnit) -> Self {
        LinkedType(iter::once(t).collect())
    }
}

mod padded_type_map {
    use super::{LinkedType, LinkedTypeUnit, Type};
    use crate::ast_step2::{name_id::Name, TypeId};
    use fxhash::{FxHashMap, FxHashSet};
    use itertools::Itertools;
    use std::{convert::TryInto, fmt::Display, iter, mem};

    #[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Copy, Hash)]
    pub struct TypePointer(usize);

    #[derive(Debug, PartialEq, Clone)]
    struct NormalType {
        name: Name,
        args: Vec<TypePointer>,
    }

    #[derive(Debug, PartialEq, Clone, Default)]
    pub struct TypeMap {
        function: Option<(TypePointer, TypePointer)>,
        normals: FxHashMap<TypeId, NormalType>,
    }

    #[derive(Debug, PartialEq, Clone)]
    pub enum Node {
        Pointer(TypePointer),
        Terminal(TypeMap),
    }

    #[derive(Debug, Default)]
    pub struct PaddedTypeMap {
        map: Vec<Node>,
    }

    impl PaddedTypeMap {
        pub fn new_pointer(&mut self) -> TypePointer {
            let p = self.map.len();
            self.map.push(Node::Terminal(TypeMap::default()));
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
            let t = self.dereference_mut(p);
            if let Some((a, b)) = t.function {
                self.union(a, arg);
                self.union(b, ret);
            } else {
                t.function = Some((arg, ret));
            }
        }

        pub fn insert_normal(
            &mut self,
            p: TypePointer,
            id: TypeId,
            name: Name,
            args: Vec<TypePointer>,
        ) {
            let t = self.dereference_mut(p);
            let abs = if let Some(t) = t.normals.get(&id) {
                t.args.iter().copied().zip(args).collect_vec()
            } else {
                t.normals.insert(id, NormalType { name, args });
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
                                self.get_type_rec(
                                    a,
                                    replace_map,
                                    trace.clone(),
                                ),
                                self.get_type_rec(
                                    b,
                                    replace_map,
                                    trace.clone(),
                                ),
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
                                                replace_map,
                                                trace.clone(),
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

        fn dereference(&mut self, p: TypePointer) -> &TypeMap {
            let p = self.find(p);
            if let Node::Terminal(t) = &self.map[p.0] {
                t
            } else {
                panic!()
            }
        }

        fn dereference_mut(&mut self, p: TypePointer) -> &mut TypeMap {
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
            let t = Node::Terminal(TypeMap {
                function: t.function.map(|(a, b)| {
                    let a = self.find(a);
                    let b = self.find(b);
                    (
                        self.clone_pointer_rec(a, replace_map),
                        self.clone_pointer_rec(b, replace_map),
                    )
                }),
                normals: t
                    .normals
                    .iter()
                    .map(|(id, t)| {
                        (
                            *id,
                            NormalType {
                                name: t.name,
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
            });
            self.map[new_p.0] = t;
            new_p
        }
    }

    impl Display for TypePointer {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "p{}", self.0)
        }
    }
}

struct VariableMemo<'b> {
    pub type_map: PaddedTypeMap,
    pub global_variable_types: FxHashMap<VariableId, TypePointer>,
    pub intrinsic_variables: FxHashMap<VariableId, TypePointer>,
    pub global_variables_step4: FxHashMap<DeclId, ast_step3::VariableDecl>,
    pub global_variables_done: Vec<VariableDecl<TypePointer>>,
    pub data_decls: FxHashMap<DeclId, &'b ast_step3::DataDecl>,
}

impl<'b> VariableMemo<'b> {
    pub fn new(
        global_variables: Vec<ast_step3::VariableDecl>,
        data_decls: &'b [ast_step3::DataDecl],
    ) -> Self {
        Self {
            type_map: Default::default(),
            global_variable_types: Default::default(),
            intrinsic_variables: Default::default(),
            global_variables_step4: global_variables
                .into_iter()
                .map(|d| (d.decl_id, d))
                .collect(),
            global_variables_done: Default::default(),
            data_decls: data_decls.iter().map(|d| (d.decl_id, d)).collect(),
        }
    }

    fn get_type_global(
        &mut self,
        variable_id: VariableId,
        trace: &FxHashMap<VariableId, TypePointer>,
    ) -> Option<(TypePointer, bool)> {
        if let Some(p) = trace.get(&variable_id) {
            Some((*p, true))
        } else {
            let p =
                if let Some(p) = self.global_variable_types.get(&variable_id) {
                    Some(*p)
                } else if let VariableId::Decl(decl_id) = variable_id {
                    let d = self.global_variables_step4.remove(&decl_id)?;
                    let p = self.type_map.new_pointer();
                    let mut trace = trace.clone();
                    trace.insert(VariableId::Decl(decl_id), p);
                    let d = VariableDecl {
                        name: d.name,
                        value: (
                            self.expr(d.value, p, &Default::default(), &trace),
                            p,
                        ),
                        decl_id,
                    };
                    self.global_variable_types.insert(variable_id, p);
                    self.global_variables_done.push(d);
                    Some(p)
                } else {
                    None
                }?;
            Some((p, false))
        }
    }

    fn expr(
        &mut self,
        (e, _): ast_step3::ExprWithType,
        type_pointer: TypePointer,
        local_variables: &FxHashMap<VariableId, TypePointer>,
        trace: &FxHashMap<VariableId, TypePointer>,
    ) -> Expr<TypePointer> {
        match e {
            ast_step3::Expr::Lambda(arms) => {
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        self.fn_arm(arm, local_variables, type_pointer, trace)
                    })
                    .collect();
                Expr::Lambda(arms)
            }
            ast_step3::Expr::Number(a) => {
                self.type_map.insert_normal(
                    type_pointer,
                    TypeId::Intrinsic(IntrinsicType::I64),
                    Name::from_str("I64"),
                    Vec::new(),
                );
                Expr::Number(a)
            }
            ast_step3::Expr::StrLiteral(a) => {
                self.type_map.insert_normal(
                    type_pointer,
                    TypeId::Intrinsic(IntrinsicType::String),
                    Name::from_str("String"),
                    Vec::new(),
                );
                Expr::StrLiteral(a)
            }
            ast_step3::Expr::Ident {
                name,
                variable_id,
                variable_kind:
                    variable_kind @ (VariableKind::Constructor
                    | VariableKind::IntrinsicConstructor),
            } => {
                let type_id = match variable_id {
                    VariableId::Decl(d) => TypeId::DeclId(d),
                    VariableId::IntrinsicVariable(_) => {
                        panic!()
                    }
                    VariableId::IntrinsicConstructor(i) => {
                        use crate::intrinsics::IntrinsicConstructor::*;
                        TypeId::Intrinsic(match i {
                            True => IntrinsicType::True,
                            False => IntrinsicType::False,
                            Unit => IntrinsicType::Unit,
                        })
                    }
                };
                let field_len = match variable_id {
                    VariableId::Decl(d) => self.data_decls[&d].field_len,
                    VariableId::IntrinsicConstructor(_) => 0,
                    VariableId::IntrinsicVariable(_) => {
                        unreachable!()
                    }
                };
                let p = make_constructor_type(
                    field_len,
                    name,
                    type_id,
                    &mut self.type_map,
                );
                self.type_map.union(type_pointer, p);
                Expr::Ident {
                    name,
                    variable_id,
                    variable_kind,
                }
            }
            ast_step3::Expr::Ident {
                name,
                variable_id,
                variable_kind: VariableKind::Local,
            } => {
                let v = local_variables[&variable_id];
                self.type_map.union(type_pointer, v);
                Expr::Ident {
                    name,
                    variable_id,
                    variable_kind: VariableKind::Local,
                }
            }
            ast_step3::Expr::Ident {
                name,
                variable_id,
                variable_kind: VariableKind::Global,
            } => {
                let (p, is_recursive) =
                    self.get_type_global(variable_id, trace).unwrap();
                let decl_id = if let VariableId::Decl(decl_id) = variable_id {
                    decl_id
                } else {
                    panic!()
                };
                if is_recursive {
                    self.type_map.union(p, type_pointer);
                    Expr::GlobalVariable {
                        name,
                        decl_id,
                        replace_map: Default::default(),
                    }
                } else {
                    let mut replace_map = Default::default();
                    let v_cloned =
                        self.type_map.clone_pointer_rec(p, &mut replace_map);
                    self.type_map.union(type_pointer, v_cloned);
                    Expr::GlobalVariable {
                        name,
                        decl_id,
                        replace_map,
                    }
                }
            }
            ast_step3::Expr::Ident {
                name,
                variable_id,
                variable_kind: VariableKind::Intrinsic,
            } => {
                let v = self.intrinsic_variables[&variable_id];
                let v_listener = self.type_map.clone_pointer(v);
                self.type_map.union(type_pointer, v_listener);
                Expr::Ident {
                    name,
                    variable_id,
                    variable_kind: VariableKind::Intrinsic,
                }
            }
            ast_step3::Expr::Call(f, a) => {
                let f_t = self.type_map.new_pointer();
                let a_t = self.type_map.new_pointer();
                let (para, ret) = self.type_map.get_fn(f_t);
                let f = self.expr(*f, f_t, local_variables, trace);
                let a = self.expr(*a, a_t, local_variables, trace);
                self.type_map.union(a_t, para);
                self.type_map.union(type_pointer, ret);
                Expr::Call((f, f_t).into(), (a, a_t).into())
            }
            ast_step3::Expr::DoBlock(es) => {
                let es: Vec<_> = es
                    .into_iter()
                    .map(|e| {
                        let p = self.type_map.new_pointer();
                        (self.expr(e, p, local_variables, trace), p)
                    })
                    .collect();
                self.type_map.union(type_pointer, es.last().unwrap().1);
                Expr::DoBlock(es)
            }
        }
    }

    fn fn_arm(
        &mut self,
        arm: ast_step3::FnArm,
        local_variables: &FxHashMap<VariableId, TypePointer>,
        mut type_pointer: TypePointer,
        trace: &FxHashMap<VariableId, TypePointer>,
    ) -> FnArm<TypePointer> {
        let mut local_variables = local_variables.clone();
        let mut pattern = Vec::new();
        for p in arm.pattern {
            let arg;
            (arg, type_pointer) = self.type_map.get_fn(type_pointer);
            pattern.push(self.unify_type_with_pattern(
                arg,
                &p,
                &mut local_variables,
            ));
        }
        let expr = self.expr(arm.expr, type_pointer, &local_variables, trace);
        FnArm {
            pattern,
            expr: (expr, type_pointer),
        }
    }

    fn unify_type_with_pattern(
        &mut self,
        type_pointer: TypePointer,
        pattern: &ast_step2::Pattern<ast_step2::types::Type>,
        local_variables: &mut FxHashMap<VariableId, TypePointer>,
    ) -> Pattern<TypePointer> {
        if pattern.len() != 1 {
            unimplemented!()
        } else {
            use crate::ast_step2::PatternUnit::*;
            let pattern = match &pattern[0] {
                I64(a) => {
                    self.type_map.insert_normal(
                        type_pointer,
                        TypeId::Intrinsic(IntrinsicType::I64),
                        Name::from_str("I64"),
                        Vec::new(),
                    );
                    PatternUnit::I64(*a)
                }
                Str(a) => {
                    self.type_map.insert_normal(
                        type_pointer,
                        TypeId::Intrinsic(IntrinsicType::String),
                        Name::from_str("String"),
                        Vec::new(),
                    );
                    PatternUnit::Str(*a)
                }
                Constructor { name, id, args } => {
                    let args = args
                        .iter()
                        .map(|pattern| {
                            let p = self.type_map.new_pointer();
                            self.unify_type_with_pattern(
                                p,
                                pattern,
                                local_variables,
                            )
                        })
                        .collect_vec();
                    self.type_map.insert_normal(
                        type_pointer,
                        (*id).into(),
                        *name,
                        args.iter().map(|(_, p)| *p).collect(),
                    );
                    PatternUnit::Constructor {
                        name: *name,
                        id: *id,
                        args,
                    }
                }
                Binder(name, d, _) => {
                    local_variables.insert(VariableId::Decl(*d), type_pointer);
                    PatternUnit::Binder(*name, *d)
                }
                Underscore => PatternUnit::Underscore,
                TypeRestriction(_, _) => unimplemented!(),
            };
            (vec![pattern], type_pointer)
        }
    }
}

fn make_constructor_type(
    field_len: usize,
    name: Name,
    id: TypeId,
    map: &mut PaddedTypeMap,
) -> TypePointer {
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
    f
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0.len() {
            0 => write!(f, "∅"),
            1 => write!(f, "{}", self.0.iter().next().unwrap()),
            _ => write!(f, "{{{}}}", self.0.iter().format(" | ")),
        }
    }
}

impl Display for TypeUnit {
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

fn unify_type_with_ast_sep2_type(
    t: &ast_step2::types::Type,
    p: TypePointer,
    map: &mut PaddedTypeMap,
    type_names: &FxHashMap<TypeId, Name>,
) {
    for t in t.iter() {
        use ast_step2::types::TypeUnit::*;
        match &**t {
            Fn(a, b) => {
                let (p_a, p_b) = map.get_fn(p);
                unify_type_with_ast_sep2_type(a, p_a, map, type_names);
                unify_type_with_ast_sep2_type(b, p_b, map, type_names);
            }
            Tuple(a, b) => {
                let len = tuple_len(b);
                let args = (0..len).map(|_| map.new_pointer()).collect_vec();
                for a in a.iter() {
                    if let Const { id } = &**a {
                        unify_type_with_tuple(b, &args, map, type_names);
                        map.insert_normal(p, *id, type_names[id], args.clone());
                    } else {
                        panic!()
                    }
                }
            }
            Const { .. }
            | RecursiveAlias { .. }
            | Variable(_)
            | TypeLevelApply { .. }
            | TypeLevelFn(_) => {
                unimplemented!()
            }
        }
    }
}

fn unify_type_with_tuple(
    t: &ast_step2::types::Type,
    ps: &[TypePointer],
    map: &mut PaddedTypeMap,
    type_names: &FxHashMap<TypeId, Name>,
) {
    for t in t.iter() {
        match &**t {
            ast_step2::types::TypeUnit::Const { id, .. }
                if *id == TypeId::Intrinsic(IntrinsicType::Unit) =>
            {
                debug_assert!(ps.is_empty());
            }
            ast_step2::types::TypeUnit::Tuple(h, t) => {
                unify_type_with_ast_sep2_type(h, ps[0], map, type_names);
                unify_type_with_tuple(t, &ps[1..], map, type_names);
            }
            _ => panic!(),
        }
    }
}

fn tuple_len(tuple: &ast_step2::types::Type) -> usize {
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
