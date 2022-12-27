mod padded_type_map;

pub use self::padded_type_map::{PaddedTypeMap, TypePointer};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::name_id::Name;
use crate::ast_step2::{self, types, ConstructorId, TypeId};
use crate::ast_step3::{self, DataDecl, VariableId, VariableKind};
use crate::intrinsics::{
    IntrinsicConstructor, IntrinsicType, IntrinsicVariable,
};
use fxhash::FxHashMap;
use itertools::Itertools;
use std::collections::BTreeSet;
use std::convert::{TryFrom, TryInto};
use std::fmt::Display;
use std::iter;
use strum::IntoEnumIterator;

/// Difference between `ast_step3::Ast` and `ast_step4::Ast`:
/// - Types in `ast_step4::Ast` are used to determining runtime representations
/// while the types in `ast_step3::Ast` are used for type checking and name resolving.
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

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<T = Type> {
    Lambda(Vec<FnArm<T>>),
    Number(String),
    StrLiteral(String),
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
    I64(String),
    Str(String),
    Constructor {
        name: Name,
        id: ConstructorId,
        args: Vec<Pattern<T>>,
    },
    Binder(Name, DeclId),
    Underscore,
    TypeRestriction(Pattern<T>, types::Type),
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
    pub fn from(ast: ast_step3::Ast) -> Self {
        let mut memo = VariableMemo::new(ast.variable_decl, &ast.data_decl);
        for d in IntrinsicVariable::iter() {
            let p = memo.type_map.new_pointer();
            unify_type_with_ast_sep2_type(&d.to_type(), p, &mut memo.type_map);
            memo.intrinsic_variables
                .insert(VariableId::IntrinsicVariable(d), p);
        }
        for d in IntrinsicConstructor::iter() {
            let p = memo.type_map.new_pointer();
            unify_type_with_ast_sep2_type(&d.to_type(), p, &mut memo.type_map);
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
                    Vec::new(),
                );
                Expr::Number(a)
            }
            ast_step3::Expr::StrLiteral(a) => {
                self.type_map.insert_normal(
                    type_pointer,
                    TypeId::Intrinsic(IntrinsicType::String),
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
                        Vec::new(),
                    );
                    PatternUnit::I64(a.clone())
                }
                Str(a) => {
                    self.type_map.insert_normal(
                        type_pointer,
                        TypeId::Intrinsic(IntrinsicType::String),
                        Vec::new(),
                    );
                    PatternUnit::Str(a.clone())
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
                TypeRestriction(p, t) => PatternUnit::TypeRestriction(
                    self.unify_type_with_pattern(
                        type_pointer,
                        p,
                        local_variables,
                    ),
                    t.clone(),
                ),
            };
            (vec![pattern], type_pointer)
        }
    }
}

fn make_constructor_type(
    field_len: usize,
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
    map.insert_normal(r, id, args.clone());
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
) {
    for t in t.iter() {
        use ast_step2::types::TypeUnit::*;
        match &**t {
            Fn(a, b) => {
                let (p_a, p_b) = map.get_fn(p);
                unify_type_with_ast_sep2_type(a, p_a, map);
                unify_type_with_ast_sep2_type(b, p_b, map);
            }
            Tuple(a, b) => {
                let len = tuple_len(b);
                let args = (0..len).map(|_| map.new_pointer()).collect_vec();
                for a in a.iter() {
                    if let Const { id } = &**a {
                        unify_type_with_tuple(b, &args, map);
                        map.insert_normal(p, *id, args.clone());
                    } else {
                        panic!()
                    }
                }
            }
            Const { .. }
            | RecursiveAlias { .. }
            | Variable(_)
            | TypeLevelApply { .. }
            | TypeLevelFn(_)
            | Restrictions { .. } => {
                unimplemented!()
            }
        }
    }
}

fn unify_type_with_tuple(
    t: &ast_step2::types::Type,
    ps: &[TypePointer],
    map: &mut PaddedTypeMap,
) {
    for t in t.iter() {
        match &**t {
            ast_step2::types::TypeUnit::Const { id, .. }
                if *id == TypeId::Intrinsic(IntrinsicType::Unit) =>
            {
                debug_assert!(ps.is_empty());
            }
            ast_step2::types::TypeUnit::Tuple(h, t) => {
                unify_type_with_ast_sep2_type(h, ps[0], map);
                unify_type_with_tuple(t, &ps[1..], map);
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
