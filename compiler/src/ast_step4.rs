mod padded_type_map;
mod specialize;

pub use self::padded_type_map::{PaddedTypeMap, TypePointer};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::name_id::Path;
use crate::ast_step2::{types, ConstructorId, TypeId};
use crate::ast_step3::{self, DataDecl, VariableId};
use crate::intrinsics::{
    IntrinsicConstructor, IntrinsicType, IntrinsicVariable,
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use std::collections::BTreeSet;
use std::convert::{TryFrom, TryInto};
use std::fmt::Display;
use std::iter::{self, once};
use strum::IntoEnumIterator;

/// Difference between `ast_step3::Ast` and `ast_step4::Ast`:
/// - Types in `ast_step4::Ast` are used to determining runtime representations
/// while the types in `ast_step3::Ast` are used for type checking and name resolving.
#[derive(Debug)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl<T = Type> {
    pub name: Path,
    pub value: ExprWithType<T>,
    pub decl_id: DeclId,
}

pub type ExprWithType<T = TypePointer> = (Expr<T>, T);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr<T> {
    Lambda {
        lambda_number: u32,
        context: Vec<DeclId>,
        parameter: DeclId,
        parameter_type: T,
        body: Box<ExprWithType<T>>,
    },
    Match {
        arms: Vec<FnArm<T>>,
        arguments: Vec<DeclId>,
    },
    Number(String),
    StrLiteral(String),
    Ident {
        name: String,
        variable_id: VariableId,
    },
    GlobalVariable {
        name: String,
        decl_id: DeclId,
        replace_map: FxHashMap<TypePointer, TypePointer>,
    },
    Call(Box<ExprWithType<T>>, Box<ExprWithType<T>>),
    DoBlock(Vec<ExprWithType<T>>),
}

/// Represents a multi-case pattern which matches if any of the `PatternUnit` in it matches.
/// It should have at least one `PatternUnit`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Pattern<T = TypePointer, E = ExprWithType<T>> {
    pub patterns: Vec<PatternUnit<T, E>>,
    pub type_: T,
}
// pub type Pattern<T = TypePointer, E = ExprWithType<T>> =
//     (Vec<PatternUnit<T, E>>, T);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit<T, E = ExprWithType<T>> {
    I64(String),
    Str(String),
    Constructor {
        name: Path,
        id: ConstructorId,
    },
    Binder(String, DeclId),
    Underscore,
    TypeRestriction(Pattern<T, E>, types::Type),
    Apply {
        pre_pattern: Pattern<T, E>,
        function: E,
        post_pattern: Pattern<T, E>,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm<T = TypePointer> {
    pub pattern: Vec<Pattern<T>>,
    pub expr: ExprWithType<T>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Clone)]
struct LinkedType(BTreeSet<LinkedTypeUnit>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum LinkedTypeUnit<T = LinkedType> {
    Normal { id: TypeId, args: Vec<T> },
    RecursionPoint,
    RecursiveAlias(LinkedType),
    Pointer(TypePointer),
    LambdaId(LambdaId),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Clone)]
pub struct Type(BTreeSet<TypeUnit>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum TypeUnit {
    Normal { id: TypeId, args: Vec<Type> },
    Fn(BTreeSet<LambdaId>, Type, Type),
    RecursiveAlias(Type),
    RecursionPoint,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum LambdaId {
    Normal(u32),
    IntrinsicVariable(IntrinsicVariable, u32),
    Constructor(ConstructorId, u32),
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
                    LinkedTypeUnit::Normal {
                        id: TypeId::Intrinsic(IntrinsicType::Fn),
                        args,
                    } => {
                        debug_assert_eq!(args.len(), 3);
                        let mut args = args.into_iter();
                        let a = args.next().unwrap().try_into()?;
                        let b = args.next().unwrap().try_into()?;
                        let lambda_id = args
                            .next()
                            .unwrap()
                            .0
                            .iter()
                            .map(|id| {
                                if let LinkedTypeUnit::LambdaId(lambda_id) = id
                                {
                                    *lambda_id
                                } else {
                                    panic!()
                                }
                            })
                            .collect();
                        Ok(Fn(lambda_id, a, b))
                    }
                    LinkedTypeUnit::Normal { id, args } => {
                        let args = args
                            .into_iter()
                            .map(Type::try_from)
                            .collect::<Result<_, _>>()?;
                        Ok(Normal { id, args })
                    }
                    LinkedTypeUnit::RecursionPoint => Ok(RecursionPoint),
                    LinkedTypeUnit::RecursiveAlias(a) => {
                        Ok(RecursiveAlias(a.try_into()?))
                    }
                    LinkedTypeUnit::Pointer(_) => Err(()),
                    LinkedTypeUnit::LambdaId(_) => panic!(),
                })
                .collect::<Result<_, _>>()?,
        ))
    }
}

impl From<TypeUnit> for Type {
    fn from(value: TypeUnit) -> Self {
        Self(once(value).collect())
    }
}

impl FromIterator<TypeUnit> for Type {
    fn from_iter<T: IntoIterator<Item = TypeUnit>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl Type {
    pub fn iter(&self) -> std::collections::btree_set::Iter<TypeUnit> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl Ast {
    pub fn from(ast: ast_step3::Ast) -> Self {
        let mut memo = VariableMemo::new(ast.variable_decl, &ast.data_decl);
        for d in IntrinsicVariable::iter() {
            let p = unify_type_pointer_with_type(
                &d.to_runtime_type(),
                &mut memo.type_map,
            );
            memo.intrinsic_variables
                .insert(VariableId::IntrinsicVariable(d), p);
        }
        for d in IntrinsicConstructor::iter() {
            let p = unify_type_pointer_with_type(
                &d.to_runtime_type(),
                &mut memo.type_map,
            );
            memo.intrinsic_variables
                .insert(VariableId::IntrinsicConstructor(d), p);
        }
        let entry_point = ast
            .entry_point
            .unwrap_or_else(|| panic!("entry point not found"));
        memo.get_type_global(entry_point, &Default::default());
        let mut memo = specialize::VariableMemo::new(
            memo.global_variables_done,
            memo.type_map,
        );
        let entry_point = memo.monomorphize_decl(entry_point);
        Self {
            variable_decl: memo.monomorphized_variables,
            data_decl: ast.data_decl,
            entry_point,
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
                LinkedTypeUnit::Normal { id, args } => {
                    let args = args
                        .into_iter()
                        .map(|arg| {
                            let (arg, r) = arg.replace_pointer(from, to);
                            replaced |= r;
                            arg
                        })
                        .collect();
                    t.insert(LinkedTypeUnit::Normal { id, args });
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

#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    pub parameter: DeclId,
    pub parameter_type: TypePointer,
    pub body: ExprWithType,
}

struct VariableMemo<'b> {
    type_map: PaddedTypeMap,
    global_variable_types: FxHashMap<VariableId, TypePointer>,
    intrinsic_variables: FxHashMap<VariableId, TypePointer>,
    global_variables_step4: FxHashMap<DeclId, ast_step3::VariableDecl<'b>>,
    global_variables_done: Vec<VariableDecl<TypePointer>>,
    data_decls: FxHashMap<DeclId, &'b ast_step3::DataDecl>,
    functions: Vec<()>,
    used_local_variables: FxHashSet<DeclId>,
}

impl<'b> VariableMemo<'b> {
    pub fn new(
        global_variables: Vec<ast_step3::VariableDecl<'b>>,
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
            functions: Vec::new(),
            used_local_variables: FxHashSet::default(),
        }
    }

    fn get_type_global(
        &mut self,
        decl_id: DeclId,
        trace: &FxHashMap<VariableId, TypePointer>,
    ) -> (TypePointer, bool) {
        if let Some(p) = trace.get(&VariableId::Global(decl_id)) {
            (*p, true)
        } else if let Some(p) =
            self.global_variable_types.get(&VariableId::Global(decl_id))
        {
            (*p, false)
        } else {
            let d = self.global_variables_step4.remove(&decl_id).unwrap();
            let p = self.type_map.new_pointer();
            let mut trace = trace.clone();
            trace.insert(VariableId::Global(decl_id), p);
            let d = VariableDecl {
                name: d.name,
                value: (
                    self.expr(d.value.0, p, &Default::default(), &trace),
                    p,
                ),
                decl_id,
            };
            self.global_variable_types
                .insert(VariableId::Global(decl_id), p);
            self.global_variables_done.push(d);
            (p, false)
        }
    }

    fn expr(
        &mut self,
        e: ast_step3::Expr,
        type_pointer: TypePointer,
        local_variables: &FxHashMap<VariableId, TypePointer>,
        trace: &FxHashMap<VariableId, TypePointer>,
    ) -> Expr<TypePointer> {
        match e {
            ast_step3::Expr::Lambda(arms) => {
                let param_len = arms[0].pattern.len();
                let type_pointer_of_match_operands = (0..param_len)
                    .map(|_| self.type_map.new_pointer())
                    .collect_vec();
                let mut body_type = self.type_map.new_pointer();
                let env_v_tmp = std::mem::take(&mut self.used_local_variables);
                let a: Vec<_> = arms
                    .into_iter()
                    .map(|arm| {
                        self.fn_arm(
                            arm,
                            local_variables,
                            &type_pointer_of_match_operands,
                            body_type,
                            trace,
                        )
                    })
                    .collect();
                let parameter_ids =
                    (0..param_len).map(|_| DeclId::new()).collect_vec();
                let mut body = Expr::Match {
                    arms: a,
                    arguments: parameter_ids.clone(),
                };
                let mut context: Vec<_> = self
                    .used_local_variables
                    .iter()
                    .copied()
                    .chain(parameter_ids)
                    .collect();
                for parameter_type in
                    type_pointer_of_match_operands.into_iter().rev()
                {
                    let new_body_type = self.type_map.new_pointer();
                    let lambda_id = self.type_map.new_lambda_id_pointer();
                    let lambda_number = self.functions.len() as u32;
                    self.type_map.insert_lambda_id(
                        lambda_id,
                        LambdaId::Normal(lambda_number),
                    );
                    self.type_map.insert_function(
                        new_body_type,
                        parameter_type,
                        body_type,
                        lambda_id,
                    );
                    self.functions.push(());
                    body = Expr::Lambda {
                        lambda_number,
                        context: context.clone(),
                        parameter: context.pop().unwrap(),
                        body: Box::new((body, body_type)),
                        parameter_type,
                    };
                    body_type = new_body_type;
                }
                self.type_map.union(body_type, type_pointer);
                self.used_local_variables.extend(env_v_tmp.into_iter());
                body
            }
            ast_step3::Expr::Number(a) => {
                self.type_map.insert_normal(
                    type_pointer,
                    TypeId::Intrinsic(IntrinsicType::I64),
                    Vec::new(),
                );
                Expr::Number(a.to_string())
            }
            ast_step3::Expr::StrLiteral(a) => {
                self.type_map.insert_normal(
                    type_pointer,
                    TypeId::Intrinsic(IntrinsicType::String),
                    Vec::new(),
                );
                Expr::StrLiteral(a.to_string())
            }
            ast_step3::Expr::Ident {
                name,
                variable_id: variable_id @ VariableId::Constructor(d),
            } => {
                let p = make_constructor_type(
                    self.data_decls[&d].field_len,
                    d,
                    &mut self.type_map,
                );
                self.type_map.union(type_pointer, p);
                Expr::Ident { name, variable_id }
            }
            ast_step3::Expr::Ident {
                name,
                variable_id: variable_id @ VariableId::IntrinsicConstructor(i),
            } => {
                use crate::intrinsics::IntrinsicConstructor::*;
                let type_id = TypeId::Intrinsic(match i {
                    True => IntrinsicType::True,
                    False => IntrinsicType::False,
                    Unit => IntrinsicType::Unit,
                });
                self.type_map
                    .insert_normal(type_pointer, type_id, Vec::new());
                Expr::Ident { name, variable_id }
            }
            ast_step3::Expr::Ident {
                name,
                variable_id: variable_id @ VariableId::Local(d),
            } => {
                self.used_local_variables.insert(d);
                let v = local_variables[&variable_id];
                self.type_map.union(type_pointer, v);
                Expr::Ident { name, variable_id }
            }
            ast_step3::Expr::Ident {
                name,
                variable_id: VariableId::Global(decl_id),
            } => {
                let (p, is_recursive) = self.get_type_global(decl_id, trace);
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
                variable_id: variable_id @ VariableId::IntrinsicVariable(_),
            } => {
                let v = self.intrinsic_variables[&variable_id];
                let v_listener = self.type_map.clone_pointer(v);
                self.type_map.union(type_pointer, v_listener);
                Expr::Ident { name, variable_id }
            }
            ast_step3::Expr::Ident {
                name,
                variable_id:
                    variable_id @ VariableId::FieldAccessor { constructor, field },
            } => {
                insert_accessor_type(
                    type_pointer,
                    self.data_decls[&constructor].field_len,
                    TypeId::DeclId(constructor),
                    field,
                    &mut self.type_map,
                );
                Expr::Ident { name, variable_id }
            }
            ast_step3::Expr::Call(f, a) => {
                let f_t = self.type_map.new_pointer();
                let a_t = self.type_map.new_pointer();
                let (para, ret, _fn_id) = self.type_map.get_fn(f_t);
                let f = self.expr(f.0, f_t, local_variables, trace);
                let a = self.expr(a.0, a_t, local_variables, trace);
                self.type_map.union(a_t, para);
                self.type_map.union(type_pointer, ret);
                Expr::Call((f, f_t).into(), (a, a_t).into())
            }
            ast_step3::Expr::DoBlock(es) => {
                let es: Vec<_> = es
                    .into_iter()
                    .map(|e| {
                        let p = self.type_map.new_pointer();
                        (self.expr(e.0, p, local_variables, trace), p)
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
        type_pointer_of_match_operands: &[TypePointer],
        return_type: TypePointer,
        trace: &FxHashMap<VariableId, TypePointer>,
    ) -> FnArm {
        let mut local_variables = local_variables.clone();
        let mut patterns = Vec::new();
        for (pattern, p) in
            arm.pattern.into_iter().zip(type_pointer_of_match_operands)
        {
            patterns.push(self.unify_type_with_pattern(
                *p,
                &pattern,
                &mut local_variables,
                trace,
            ));
        }
        let expr = self.expr(arm.expr.0, return_type, &local_variables, trace);
        FnArm {
            pattern: patterns,
            expr: (expr, return_type),
        }
    }

    fn unify_type_with_pattern(
        &mut self,
        type_pointer: TypePointer,
        pattern: &ast_step3::Pattern,
        local_variables: &mut FxHashMap<VariableId, TypePointer>,
        trace: &FxHashMap<VariableId, TypePointer>,
    ) -> Pattern {
        if pattern.0.len() != 1 {
            unimplemented!()
        } else {
            use crate::ast_step2::PatternUnit::*;
            let pattern = match &pattern.0[0] {
                I64(a) => {
                    self.type_map.insert_normal(
                        type_pointer,
                        TypeId::Intrinsic(IntrinsicType::I64),
                        Vec::new(),
                    );
                    PatternUnit::I64(a.to_string())
                }
                Str(a) => {
                    self.type_map.insert_normal(
                        type_pointer,
                        TypeId::Intrinsic(IntrinsicType::String),
                        Vec::new(),
                    );
                    PatternUnit::Str(a.to_string())
                }
                Constructor {
                    name,
                    id: id @ ConstructorId::DeclId(decl_id),
                    args,
                } => {
                    let args = args
                        .iter()
                        .map(|(pattern, _span)| {
                            let p = self.type_map.new_pointer();
                            self.unify_type_with_pattern(
                                p,
                                pattern,
                                local_variables,
                                trace,
                            )
                        })
                        .collect_vec();
                    self.type_map.insert_normal(
                        type_pointer,
                        (*id).into(),
                        args.iter().map(|p| p.type_).collect(),
                    );
                    let mut p = PatternUnit::Constructor {
                        name: *name,
                        id: *id,
                    };
                    let field_len = args.len();
                    for (i, arg) in args.into_iter().enumerate() {
                        let accessor_t = self.type_map.new_pointer();
                        insert_accessor_type(
                            accessor_t,
                            field_len,
                            TypeId::DeclId(*decl_id),
                            i,
                            &mut self.type_map,
                        );
                        p = PatternUnit::Apply {
                            pre_pattern: Pattern {
                                patterns: vec![p],
                                type_: type_pointer,
                            },
                            function: (
                                Expr::Ident {
                                    name: format!("_{i}"),
                                    variable_id: VariableId::FieldAccessor {
                                        constructor: *decl_id,
                                        field: i,
                                    },
                                },
                                accessor_t,
                            ),
                            post_pattern: arg,
                        };
                    }
                    p
                }
                Constructor {
                    name,
                    id: id @ ConstructorId::Intrinsic(_),
                    args,
                } => {
                    debug_assert!(args.is_empty());
                    self.type_map.insert_normal(
                        type_pointer,
                        (*id).into(),
                        Vec::new(),
                    );
                    PatternUnit::Constructor {
                        name: *name,
                        id: *id,
                    }
                }
                Binder(name, d, _) => {
                    local_variables.insert(VariableId::Local(*d), type_pointer);
                    self.used_local_variables.remove(d);
                    PatternUnit::Binder(name.to_string(), *d)
                }
                ResolvedBinder(d, _) => {
                    local_variables.insert(VariableId::Local(*d), type_pointer);
                    PatternUnit::Binder("unique".to_string(), *d)
                }
                Underscore => PatternUnit::Underscore,
                TypeRestriction(p, t) => PatternUnit::TypeRestriction(
                    self.unify_type_with_pattern(
                        type_pointer,
                        p,
                        local_variables,
                        trace,
                    ),
                    t.clone(),
                ),
                Apply(pre_pattern, applications) => {
                    let mut p = self.unify_type_with_pattern(
                        type_pointer,
                        pre_pattern,
                        local_variables,
                        trace,
                    );
                    for a in applications {
                        let post_pattern_p = self.type_map.new_pointer();
                        let function_p = self.type_map.new_pointer();
                        let p_p = p.type_;
                        p = Pattern {
                            patterns: vec![PatternUnit::Apply {
                                pre_pattern: p,
                                function: (
                                    self.expr(
                                        a.function.clone(),
                                        function_p,
                                        local_variables,
                                        trace,
                                    ),
                                    function_p,
                                ),
                                post_pattern: self.unify_type_with_pattern(
                                    post_pattern_p,
                                    &a.post_pattern,
                                    local_variables,
                                    trace,
                                ),
                            }],
                            type_: p_p,
                        };
                    }
                    return p;
                }
            };
            Pattern {
                patterns: vec![pattern],
                type_: type_pointer,
            }
        }
    }
}

fn make_constructor_type(
    field_len: usize,
    id: DeclId,
    map: &mut PaddedTypeMap,
) -> TypePointer {
    let r = map.new_pointer();
    let mut args = Vec::new();
    let mut f = r;
    for i in (0..field_len).rev() {
        let p = map.new_pointer();
        args.push(p);
        let f_old = f;
        f = map.new_pointer();
        let fn_id = map.new_lambda_id_pointer();
        map.insert_lambda_id(
            fn_id,
            LambdaId::Constructor(ConstructorId::DeclId(id), i as u32),
        );
        map.insert_function(f, p, f_old, fn_id);
    }
    args.reverse();
    map.insert_normal(r, TypeId::DeclId(id), args.clone());
    f
}

fn insert_accessor_type(
    p: TypePointer,
    field_len: usize,
    id: TypeId,
    field: usize,
    map: &mut PaddedTypeMap,
) {
    let args = (0..field_len).map(|_| map.new_pointer()).collect_vec();
    let t = map.new_pointer();
    let fn_id = map.new_lambda_id_pointer();
    map.insert_function(p, t, args[field], fn_id);
    map.insert_normal(t, id, args);
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
            TypeUnit::Normal { args, id } => {
                debug_assert_ne!(*id, TypeId::Intrinsic(IntrinsicType::Fn));
                if args.is_empty() {
                    write!(f, "{id}")
                } else {
                    write!(f, "{}[{}]", id, args.iter().format(", "))
                }
            }
            TypeUnit::RecursiveAlias(t) => write!(f, "rec[{t}]"),
            TypeUnit::RecursionPoint => write!(f, "d0"),
            TypeUnit::Fn(id, a, b) => {
                if a.0.len() == 1
                    && matches!(
                        a.0.iter().next().unwrap(),
                        TypeUnit::Normal {
                            id: TypeId::Intrinsic(IntrinsicType::Fn),
                            ..
                        }
                    )
                {
                    write!(f, "({a}) -{id:?}-> {b}")
                } else {
                    write!(f, "{a} -{id:?}-> {b}")
                }
            }
        }
    }
}

fn unify_type_pointer_with_type(
    t: &Type,
    map: &mut PaddedTypeMap,
) -> TypePointer {
    let p = map.new_pointer();
    for t in t.0.iter() {
        use TypeUnit::*;
        match t {
            Normal { id, args } => {
                let mut p_args = Vec::with_capacity(args.len());
                for a in args {
                    let p = unify_type_pointer_with_type(a, map);
                    p_args.push(p);
                }
                map.insert_normal(p, *id, p_args);
            }
            RecursionPoint | RecursiveAlias(_) => {
                unimplemented!()
            }
            Fn(lambda_id, a, b) => {
                let lambda_id_p = map.new_lambda_id_pointer();
                let a_p = unify_type_pointer_with_type(a, map);
                let b_p = unify_type_pointer_with_type(b, map);
                for i in lambda_id {
                    map.insert_lambda_id(lambda_id_p, *i);
                }
                map.insert_function(p, a_p, b_p, lambda_id_p);
            }
        }
    }
    p
}
