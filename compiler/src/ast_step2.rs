pub mod imports;
mod type_alias_map;
pub mod type_display;
pub mod types;

use self::imports::Imports;
use self::type_alias_map::{SearchMode, TypeAliasMap};
use self::types::{Type, TypeMatchable, TypeUnit, TypeVariable};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::ident_id::IdentId;
use crate::ast_step1::name_id::Name;
use crate::ast_step1::token_map::{TokenMap, TokenMapEntry};
use crate::ast_step1::{self, merge_span};
use crate::ast_step3::VariableRequirement;
use crate::errors::CompileError;
use crate::intrinsics::{
    IntrinsicConstructor, IntrinsicType, INTRINSIC_CONSTRUCTORS,
    INTRINSIC_TYPES,
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use once_cell::sync::Lazy;
use parser::token_id::TokenId;
use parser::Span;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;
use tracing_mutex::stdsync::TracingRwLock as RwLock;
use types::TypeConstructor;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstructorId {
    DeclId(DeclId),
    Intrinsic(IntrinsicConstructor),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeId {
    DeclId(DeclId),
    Intrinsic(IntrinsicType),
    FixedVariable(DeclId),
}

/// Difference between `ast_step1::Ast` and `ast_step2::Ast`:
/// - The names of types and constructors are resolved.
/// - Local variable declarations are converted into lambdas and function calls.
/// - Question notations are desugared.
#[derive(Debug, PartialEq)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
    pub imports: Imports,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: Name,
    pub fields: Vec<TypeVariable>,
    pub type_variable_decls: Vec<(TypeVariable, Name)>,
    pub decl_id: DeclId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelOrigin {
    pub left: Type,
    pub right: Type,
    pub span: Span,
}

impl Ord for RelOrigin {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (&self.left, &self.right, self.span.start, self.span.end).cmp(&(
            &other.left,
            &other.right,
            other.span.start,
            other.span.end,
        ))
    }
}

impl PartialOrd for RelOrigin {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SubtypeRelations(pub BTreeSet<(Type, Type, RelOrigin)>);

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub enum PatternUnitForRestriction {
    I64,
    Str,
    Const {
        id: TypeId,
    },
    Tuple(
        Box<PatternUnitForRestriction>,
        Box<PatternUnitForRestriction>,
    ),
    Binder(Type, DeclId),
    TypeRestriction(Box<PatternUnitForRestriction>, Type),
}

pub type PatternForRestriction = Vec<(PatternUnitForRestriction, Span)>;
pub type PatternRestrictions =
    Vec<(Type, Vec<(PatternUnitForRestriction, Span)>, Span)>;
type ModulePath = Name;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct TypeWithEnv<T = Type>
where
    T: TypeConstructor,
{
    pub constructor: T,
    pub variable_requirements: Vec<VariableRequirement>,
    pub subtype_relations: SubtypeRelations,
    pub already_considered_relations: BTreeSet<(Type, Type)>,
    pub pattern_restrictions: PatternRestrictions,
    pub fn_apply_dummies: BTreeMap<Type, (Type, RelOrigin)>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl {
    pub name: Name,
    pub type_annotation: Option<Annotation>,
    pub value: ExprWithTypeAndSpan<TypeVariable>,
    pub decl_id: DeclId,
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Annotation {
    pub unfixed: Type,
    pub fixed: Type,
    pub implicit_parameters: Vec<(String, Type, DeclId)>,
    pub fixed_parameter_names: FxHashMap<TypeUnit, Name>,
    pub span: Span,
}

pub type ExprWithTypeAndSpan<T> = (Expr<T>, T, Span);

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<T> {
    Lambda(Vec<FnArm<T>>),
    Number(String),
    StrLiteral(String),
    Ident {
        name: Vec<(String, Option<Span>, Option<TokenId>)>,
        ident_id: IdentId,
    },
    ResolvedIdent {
        decl_id: DeclId,
        type_: TypeVariable,
    },
    Call(Box<ExprWithTypeAndSpan<T>>, Box<ExprWithTypeAndSpan<T>>),
    Do(Vec<ExprWithTypeAndSpan<T>>),
    TypeAnnotation(Box<ExprWithTypeAndSpan<T>>, Type),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<T> {
    pub pattern: Vec<(Pattern<T>, Span)>,
    pub expr: ExprWithTypeAndSpan<T>,
}

/// Represents a multi-case pattern which matches if any of the `PatternUnit` in it matches.
/// It should have at least one `PatternUnit`.
pub type Pattern<T> = Vec<PatternUnit<T>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit<T> {
    I64(String),
    Str(String),
    Constructor {
        name: Name,
        id: ConstructorId,
        args: Vec<Pattern<T>>,
    },
    Binder(String, DeclId, T),
    ResolvedBinder(DeclId, T),
    Underscore,
    TypeRestriction(Pattern<T>, Type),
}

#[derive(Debug)]
enum FlatMapEnv {
    FlatMap {
        decl_id: DeclId,
        type_of_decl: TypeVariable,
        pre_calc: ExprWithTypeAndSpan<TypeVariable>,
        question_span: Span,
    },
    Decl(DeclId, ExprWithTypeAndSpan<TypeVariable>),
}

struct WithFlatMapEnv<Value = ExprWithTypeAndSpan<TypeVariable>> {
    value: Value,
    env: Vec<FlatMapEnv>,
}

static TYPE_NAMES: Lazy<RwLock<FxHashMap<TypeId, Name>>> = Lazy::new(|| {
    RwLock::new(
        INTRINSIC_TYPES
            .iter()
            .map(|(name, id)| {
                (TypeId::Intrinsic(*id), Name::from_str_intrinsic(name))
            })
            .collect(),
    )
});

pub fn get_type_name(type_id: TypeId) -> Name {
    *TYPE_NAMES.read().unwrap().get(&type_id).unwrap()
}

impl Ast {
    pub fn from(
        ast: ast_step1::Ast,
        token_map: &mut TokenMap,
        mut imports: Imports,
    ) -> Result<Self, CompileError> {
        let mut data_decls = Vec::new();
        let mut variable_decls = Vec::new();
        let mut env = Env {
            token_map,
            type_alias_map: &mut TypeAliasMap::default(),
            interface_decls: &mut Default::default(),
            imports: &mut imports,
            data_decl_map: &mut FxHashMap::default(),
        };
        collect_decls(
            ast,
            Name::root(),
            &mut env,
            &mut variable_decls,
            &mut data_decls,
        )?;
        let entry_point = variable_decls
            .iter()
            .find(|d| d.name == Name::from_str(Name::pkg_root(), "main"))
            .unwrap_or_else(|| panic!("entry point not found"))
            .decl_id;
        Ok(Self {
            variable_decl: variable_decls,
            data_decl: data_decls,
            imports,
            entry_point,
        })
    }
}

fn collect_decls<'a>(
    ast: ast_step1::Ast<'a>,
    module_path: ModulePath,
    env: &mut Env<'_, 'a>,
    variable_decls: &mut Vec<VariableDecl>,
    data_decls: &mut Vec<DataDecl>,
) -> Result<(), CompileError> {
    collect_data_and_type_alias_decls(
        &ast,
        module_path,
        env.token_map,
        data_decls,
        env.type_alias_map,
        env.imports,
    )?;
    env.data_decl_map
        .extend(data_decls.iter().map(|d| (d.name, d.decl_id)));
    {
        TYPE_NAMES.write().unwrap().extend(
            data_decls
                .iter()
                .map(|d| (TypeId::DeclId(d.decl_id), d.name)),
        );
    }
    collect_interface_decls(&ast, module_path, env)?;
    collect_variable_decls(ast, module_path, variable_decls, env)?;
    Ok(())
}

fn collect_data_and_type_alias_decls<'a>(
    ast: &ast_step1::Ast<'a>,
    module_path: ModulePath,
    token_map: &mut TokenMap,
    data_decls: &mut Vec<DataDecl>,
    type_alias_map: &mut TypeAliasMap<'a>,
    imports: &mut Imports,
) -> Result<(), CompileError> {
    for d in &ast.variable_decl {
        imports.add_true_name(d.name, d.is_public);
    }
    data_decls.extend(ast.data_decl.iter().map(|d| {
        let mut type_variables = FxHashMap::default();
        for ((name, _, id), interfaces) in &d.type_variables.type_variables {
            token_map.insert(*id, TokenMapEntry::TypeVariable);
            type_variables.insert(*name, TypeVariable::new());
            for (_, _, id) in interfaces {
                token_map.insert(*id, TokenMapEntry::Interface);
            }
        }
        imports.add_true_name(d.name, d.is_public);
        DataDecl {
            name: d.name,
            fields: d
                .fields
                .iter()
                .map(|f| {
                    token_map.insert(f.2, TokenMapEntry::TypeVariable);
                    type_variables[f.0]
                })
                .collect(),
            decl_id: d.decl_id,
            type_variable_decls: type_variables
                .into_iter()
                .map(|(n, v)| (v, Name::from_str(module_path, n)))
                .collect(),
        }
    }));
    type_alias_map.add_decls(
        &ast.type_alias_decl,
        token_map,
        module_path,
        imports,
    );
    for m in &ast.modules {
        imports.add_true_name(m.name, m.is_public);
        collect_data_and_type_alias_decls(
            &m.ast,
            m.name,
            token_map,
            data_decls,
            type_alias_map,
            imports,
        )?
    }
    Ok(())
}

fn collect_interface_decls(
    ast: &ast_step1::Ast,
    module_path: ModulePath,
    env: &mut Env<'_, '_>,
) -> Result<(), CompileError> {
    env.interface_decls.extend(
        ast.interface_decl
            .iter()
            .map(|i| {
                env.token_map.insert(i.name.2, TokenMapEntry::Interface);
                Ok((
                    Name::from_str(module_path, i.name.0),
                    i.variables
                        .iter()
                        .map(|(name, t, forall)| {
                            let self_ = TypeVariable::new();
                            let t = type_to_type_with_forall(
                                t.clone(),
                                module_path,
                                std::iter::once((
                                    Name::from_str(module_path, "Self"),
                                    self_,
                                ))
                                .collect(),
                                forall.clone(),
                                &mut Env {
                                    interface_decls: &mut Default::default(),
                                    token_map: env.token_map,
                                    type_alias_map: env.type_alias_map,
                                    imports: env.imports,
                                    data_decl_map: env.data_decl_map,
                                },
                            )?;
                            env.token_map.insert(
                                name.2,
                                TokenMapEntry::VariableDeclInInterface(
                                    t.clone(),
                                ),
                            );
                            Ok((name.0.to_string(), t, self_))
                        })
                        .try_collect()?,
                ))
            })
            .try_collect::<_, Vec<_>, _>()?,
    );
    for m in &ast.modules {
        collect_interface_decls(&m.ast, m.name, env)?;
    }
    Ok(())
}

struct Env<'a, 'b> {
    token_map: &'a mut TokenMap,
    type_alias_map: &'a mut TypeAliasMap<'b>,
    interface_decls: &'a mut FxHashMap<Name, Vec<(String, Type, TypeVariable)>>,
    imports: &'a mut Imports,
    data_decl_map: &'a mut FxHashMap<Name, DeclId>,
}

fn collect_variable_decls(
    ast: ast_step1::Ast,
    module_path: ModulePath,
    variable_decls: &mut Vec<VariableDecl>,
    env: &mut Env<'_, '_>,
) -> Result<(), CompileError> {
    variable_decls.extend(
        ast.variable_decl
            .into_iter()
            .map(|d| -> Result<VariableDecl, CompileError> {
                let WithFlatMapEnv {
                    value:
                        VariableDecl {
                            value,
                            name,
                            type_annotation,
                            decl_id,
                            span,
                        },
                    env: flat_map_env,
                } = variable_decl(d, module_path, env, &Default::default())?;
                Ok(VariableDecl {
                    value: catch_flat_map(WithFlatMapEnv {
                        value,
                        env: flat_map_env,
                    })?,
                    name,
                    type_annotation,
                    decl_id,
                    span,
                })
            })
            .collect::<Result<Vec<_>, CompileError>>()?,
    );
    for m in ast.modules {
        collect_variable_decls(m.ast, m.name, variable_decls, env)?;
    }
    Ok(())
}

impl From<ConstructorId> for TypeId {
    fn from(c: ConstructorId) -> Self {
        match c {
            ConstructorId::DeclId(ident) => Self::DeclId(ident),
            ConstructorId::Intrinsic(i) => Self::Intrinsic(i.into()),
        }
    }
}

impl Display for TypeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeId::FixedVariable(decl_id) => write!(f, "c{}", decl_id),
            id => write!(f, "{}", get_type_name(*id)),
        }
    }
}

impl From<Type> for TypeWithEnv {
    fn from(t: Type) -> Self {
        Self {
            constructor: t,
            ..Default::default()
        }
    }
}

impl<T> From<PatternUnit<T>> for Pattern<T> {
    fn from(p: PatternUnit<T>) -> Self {
        vec![p]
    }
}

fn variable_decl(
    v: ast_step1::VariableDecl,
    module_path: ModulePath,
    env: &mut Env<'_, '_>,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
) -> Result<WithFlatMapEnv<VariableDecl>, CompileError> {
    let expr = expr(v.value, module_path, type_variable_names, env)?;
    let d = VariableDecl {
        type_annotation: v
            .type_annotation
            .map(|(t, forall, span)| {
                let implicit_type_parameters: Vec<_> = forall
                    .type_variables
                    .iter()
                    .map(|(name, _)| Name::from_str(module_path, name.0))
                    .collect();
                let t = type_to_type_with_forall(
                    t,
                    module_path,
                    type_variable_names.clone(),
                    forall,
                    env,
                )?;
                let mut fixed_parameter_names = FxHashMap::default();
                let (mut fixed_t, parameters) = t.clone().remove_parameters();
                for (p, name) in parameters
                    .into_iter()
                    .zip_eq(implicit_type_parameters.iter())
                {
                    let new_const = TypeUnit::Const {
                        id: TypeId::FixedVariable(DeclId::new()),
                    };
                    fixed_t = fixed_t.replace_num(p, &new_const.clone().into());
                    fixed_parameter_names.insert(new_const, *name);
                }
                let variable_requirements = match fixed_t.matchable() {
                    TypeMatchable::Restrictions {
                        t,
                        variable_requirements,
                        subtype_relations,
                    } => {
                        fixed_t = if subtype_relations.is_empty() {
                            t
                        } else {
                            TypeUnit::Restrictions {
                                t,
                                variable_requirements: Vec::new(),
                                subtype_relations,
                            }
                            .into()
                        };
                        variable_requirements
                    }
                    t => {
                        fixed_t = t.into();
                        Vec::new()
                    }
                };
                Ok(Annotation {
                    unfixed: t,
                    fixed: fixed_t,
                    implicit_parameters: variable_requirements
                        .into_iter()
                        .map(|(name, t)| (name, t, DeclId::new()))
                        .collect(),
                    fixed_parameter_names,
                    span,
                })
            })
            .transpose()?,
        value: expr.value,
        decl_id: v.decl_id,
        span: v.span,
        name: v.name,
    };
    Ok(WithFlatMapEnv {
        value: d,
        env: expr.env,
    })
}

fn catch_flat_map(
    e: WithFlatMapEnv,
) -> Result<ExprWithTypeAndSpan<TypeVariable>, CompileError> {
    let mut expr = e.value;
    for flat_map_env in e.env.into_iter().rev() {
        match flat_map_env {
            FlatMapEnv::FlatMap {
                decl_id,
                type_of_decl,
                pre_calc,
                question_span,
            } => {
                let continuation = Expr::Lambda(vec![FnArm {
                    pattern: vec![(
                        vec![PatternUnit::ResolvedBinder(
                            decl_id,
                            type_of_decl,
                        )],
                        0..0,
                    )],
                    expr,
                }]);
                expr = (
                    Expr::Call(
                        Box::new((
                            Expr::Call(
                                Box::new((
                                    Expr::Ident {
                                        name: vec![(
                                            "flat_map".to_string(),
                                            None,
                                            None,
                                        )],
                                        ident_id: IdentId::new(),
                                    },
                                    TypeVariable::new(),
                                    question_span,
                                )),
                                Box::new(pre_calc),
                            ),
                            TypeVariable::new(),
                            0..0,
                        )),
                        Box::new((continuation, TypeVariable::new(), 0..0)),
                    ),
                    TypeVariable::new(),
                    0..0,
                );
            }
            FlatMapEnv::Decl(name, e) => {
                let l = Expr::Lambda(vec![FnArm {
                    pattern: vec![(
                        PatternUnit::ResolvedBinder(name, e.1).into(),
                        0..0,
                    )],
                    expr,
                }]);
                expr = (
                    Expr::Call(
                        Box::new((l, TypeVariable::new(), 0..0)),
                        Box::new(e),
                    ),
                    TypeVariable::new(),
                    0..0,
                );
            }
        }
    }
    Ok(expr)
}

fn expr(
    e: ast_step1::ExprWithSpan,
    module_path: ModulePath,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    env: &mut Env<'_, '_>,
) -> Result<WithFlatMapEnv, CompileError> {
    use Expr::*;
    let span = e.1;
    let (flat_map_env, e) = match e.0 {
        ast_step1::Expr::Lambda(arms) => (
            Vec::new(),
            Lambda(
                arms.into_iter()
                    .map(move |arm| {
                        fn_arm(arm, module_path, type_variable_names, env)
                    })
                    .collect::<Result<_, _>>()?,
            ),
        ),
        ast_step1::Expr::Number(n) => (Vec::new(), Number(n.to_string())),
        ast_step1::Expr::StrLiteral(s) => {
            (Vec::new(), StrLiteral(s.to_string()))
        }
        ast_step1::Expr::Ident { path } => {
            let ident_id = IdentId::new();
            env.token_map
                .insert(path.last().unwrap().2, TokenMapEntry::Ident(ident_id));
            (
                Vec::new(),
                Ident {
                    name: path
                        .into_iter()
                        .map(|(a, b, c)| (a.to_string(), b, c))
                        .collect(),
                    ident_id,
                },
            )
        }
        ast_step1::Expr::Decl(_) => {
            panic!()
        }
        ast_step1::Expr::Call(f, a) => {
            let f = expr(*f, module_path, type_variable_names, env)?;
            let mut a = expr(*a, module_path, type_variable_names, env)?;
            if f.env.is_empty() {
                (a.env, Call(Box::new(f.value), Box::new(a.value)))
            } else {
                let decl_id = DeclId::new();
                let mut env = f.env;
                let f_span = f.value.2.clone();
                let f_type = f.value.1;
                env.push(FlatMapEnv::Decl(decl_id, f.value));
                env.append(&mut a.env);
                (
                    env,
                    Call(
                        Box::new((
                            Expr::ResolvedIdent {
                                decl_id,
                                type_: f_type,
                            },
                            f_type,
                            f_span,
                        )),
                        Box::new(a.value),
                    ),
                )
            }
        }
        ast_step1::Expr::Do(es) => {
            let mut new_es = Vec::new();
            let mut es_span = 0..0;
            for e in es.into_iter().rev() {
                (new_es, es_span) = add_expr_in_do(
                    e,
                    module_path,
                    new_es,
                    es_span,
                    type_variable_names,
                    env,
                )?;
            }
            new_es.reverse();
            return Ok(WithFlatMapEnv {
                value: (Do(new_es), TypeVariable::new(), span),
                env: Vec::new(),
            });
        }
        ast_step1::Expr::Question(e, question_span) => {
            let e = expr(*e, module_path, type_variable_names, env)?;
            let mut env = e.env;
            let decl_id = DeclId::new();
            let type_of_decl = TypeVariable::new();
            env.push(FlatMapEnv::FlatMap {
                decl_id,
                type_of_decl,
                pre_calc: e.value,
                question_span,
            });
            (
                env,
                Expr::ResolvedIdent {
                    decl_id,
                    type_: type_of_decl,
                },
            )
        }
        ast_step1::Expr::TypeAnnotation(e, t, forall) => {
            let e = expr(*e, module_path, type_variable_names, env)?;
            let t = type_to_type_with_forall(
                t,
                module_path,
                type_variable_names.clone(),
                forall,
                env,
            )?;
            (e.env, Expr::TypeAnnotation(Box::new(e.value), t))
        }
    };
    Ok(WithFlatMapEnv {
        value: (e, TypeVariable::new(), span),
        env: flat_map_env,
    })
}

fn add_expr_in_do(
    e: ast_step1::ExprWithSpan,
    module_path: ModulePath,
    mut es: Vec<ExprWithTypeAndSpan<TypeVariable>>,
    es_span: Span,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    env: &mut Env<'_, '_>,
) -> Result<(Vec<ExprWithTypeAndSpan<TypeVariable>>, Span), CompileError> {
    match e {
        (ast_step1::Expr::Decl(d), d_span) => {
            let d = variable_decl(*d, module_path, env, type_variable_names)?;
            if es.is_empty() {
                Ok((
                    vec![
                        (
                            Expr::Ident {
                                name: vec![("()".to_string(), None, None)],
                                ident_id: IdentId::new(),
                            },
                            TypeVariable::new(),
                            d_span.clone(),
                        ),
                        catch_flat_map(WithFlatMapEnv {
                            value: d.value.value,
                            env: d.env,
                        })?,
                    ],
                    d_span,
                ))
            } else {
                es.reverse();
                let l = Expr::Lambda(vec![FnArm {
                    pattern: vec![(
                        PatternUnit::Binder(
                            d.value.name.to_string(),
                            d.value.decl_id,
                            TypeVariable::new(),
                        )
                        .into(),
                        d.value.span,
                    )],
                    expr: (Expr::Do(es), TypeVariable::new(), es_span.clone()),
                }]);
                Ok((
                    vec![catch_flat_map(WithFlatMapEnv {
                        value: (
                            Expr::Call(
                                Box::new((
                                    l,
                                    TypeVariable::new(),
                                    d_span.clone(),
                                )),
                                Box::new(d.value.value),
                            ),
                            TypeVariable::new(),
                            d_span.clone(),
                        ),
                        env: d.env,
                    })?],
                    merge_span(&es_span, &d_span),
                ))
            }
        }
        e => {
            let e_span = e.1.clone();
            let e = expr(e, module_path, type_variable_names, env)?;
            es.push(e.value);
            let span = merge_span(&es_span, &e_span);
            if e.env.is_empty() {
                Ok((es, span))
            } else {
                es.reverse();
                Ok((
                    vec![catch_flat_map(WithFlatMapEnv {
                        value: (Expr::Do(es), TypeVariable::new(), es_span),
                        env: e.env,
                    })?],
                    span,
                ))
            }
        }
    }
}

fn fn_arm(
    arm: ast_step1::FnArm,
    module_path: ModulePath,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    env: &mut Env<'_, '_>,
) -> Result<FnArm<TypeVariable>, CompileError> {
    Ok(FnArm {
        pattern: arm
            .pattern
            .into_iter()
            .map(|(p, span)| Ok((pattern(p, module_path, env)?, span)))
            .try_collect()?,
        expr: catch_flat_map(expr(
            arm.expr,
            module_path,
            type_variable_names,
            env,
        )?)?,
    })
}

impl Name {
    fn is_same_as_or_ancestor_of(self, path: Name) -> bool {
        if self.is_root() || self == path {
            true
        } else if let Some((path, _)) = path.split() {
            self.is_same_as_or_ancestor_of(path)
        } else {
            false
        }
    }
}

impl TypeId {
    fn get(name: Name, env: &mut Env<'_, '_>) -> Result<TypeId, CompileError> {
        if let Some(id) = env.data_decl_map.get(&name) {
            Ok(TypeId::DeclId(*id))
        } else if let Some(i) = INTRINSIC_TYPES.get(&name.to_string().as_str())
        {
            Ok(TypeId::Intrinsic(*i))
        } else {
            panic!();
        }
    }
}

impl ConstructorId {
    fn get(
        name: Name,
        data_decl_map: &FxHashMap<Name, DeclId>,
    ) -> ConstructorId {
        if let Some(id) = data_decl_map.get(&name) {
            ConstructorId::DeclId(*id)
        } else if let Some(i) =
            INTRINSIC_CONSTRUCTORS.get(name.to_string().as_str())
        {
            ConstructorId::Intrinsic(*i)
        } else {
            panic!("{:?} not found", name)
        }
    }
}

fn pattern(
    p: ast_step1::Pattern,
    module_path: ModulePath,
    env: &mut Env<'_, '_>,
) -> Result<Pattern<TypeVariable>, CompileError> {
    use PatternUnit::*;
    Ok(match p {
        ast_step1::Pattern::Number(n) => I64(n.parse().unwrap()),
        ast_step1::Pattern::StrLiteral(s) => Str(s.to_string()),
        ast_step1::Pattern::Constructor { path, args } => {
            let n = env
                .imports
                .get_true_names_with_path(
                    module_path,
                    module_path,
                    &path,
                    env.token_map,
                )?
                .collect_vec();
            if n.is_empty() {
                panic!("{:?} not found", path);
            } else if n.len() == 2 {
                panic!(
                    "there are {} candidates for {:?}. \
                Multiple dispatching on pattern is not implemented.",
                    n.len(),
                    path
                );
            }
            let id = ConstructorId::get(n[0], env.data_decl_map);
            env.token_map
                .insert(path.last().unwrap().2, TokenMapEntry::Constructor(id));
            Constructor {
                name: env.imports.get_true_name_with_path(
                    module_path,
                    module_path,
                    &path,
                    env.token_map,
                )?,
                id,
                args: args
                    .into_iter()
                    .map(|arg| pattern(arg, module_path, env))
                    .try_collect()?,
            }
        }
        ast_step1::Pattern::Binder(name) => {
            let decl_id = DeclId::new();
            env.token_map.insert(name.2, TokenMapEntry::Decl(decl_id));
            Binder(name.0.to_string(), decl_id, TypeVariable::new())
        }
        ast_step1::Pattern::Underscore => Underscore,
        ast_step1::Pattern::TypeRestriction(p, t, forall) => {
            let t = type_to_type_with_forall(
                t,
                module_path,
                Default::default(),
                forall,
                env,
            )?;
            let p = pattern(*p, module_path, env)?;
            TypeRestriction(p, t)
        }
    }
    .into())
}

fn type_to_type(
    t: &ast_step1::Type,
    module_path: ModulePath,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    search_type: SearchMode,
    env: &mut Env<'_, '_>,
) -> Result<Type, CompileError> {
    match (t.path.len(), t.path.last().unwrap().0) {
        (1, "|") => Ok(t
            .args
            .iter()
            .map(|a| {
                type_to_type(
                    a,
                    module_path,
                    type_variable_names,
                    search_type,
                    env,
                )
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect()),
        (1, "->") => Ok(TypeUnit::Fn(
            type_to_type(
                &t.args[0],
                module_path,
                type_variable_names,
                search_type,
                env,
            )?,
            type_to_type(
                &t.args[1],
                module_path,
                type_variable_names,
                search_type,
                env,
            )?,
        )
        .into()),
        _ => {
            let n = env.imports.get_true_name_with_path_unchecked(
                module_path,
                module_path,
                &t.path,
                env.token_map,
            )?;
            if let Some(n) = type_variable_names.get(&n) {
                env.token_map.insert(
                    t.path.last().unwrap().2,
                    TokenMapEntry::TypeVariable,
                );
                let mut new_t = Type::from(TypeUnit::Variable(*n));
                for a in &t.args {
                    new_t = new_t.type_level_function_apply(type_to_type(
                        a,
                        module_path,
                        type_variable_names,
                        search_type,
                        env,
                    )?);
                }
                Ok(new_t)
            } else if let Some(mut unaliased) = {
                env.get_type_from_alias(
                    (n, t.path.last().unwrap().2),
                    type_variable_names,
                    if search_type == SearchMode::Normal {
                        SearchMode::Alias
                    } else {
                        SearchMode::AliasSub
                    },
                )?
            } {
                for a in &t.args {
                    unaliased =
                        unaliased.type_level_function_apply(type_to_type(
                            a,
                            module_path,
                            type_variable_names,
                            search_type,
                            env,
                        )?);
                }
                Ok(unaliased)
            } else {
                let mut tuple = Type::label_from_str("()");
                for a in t
                    .args
                    .iter()
                    .map(|a| {
                        type_to_type(
                            a,
                            module_path,
                            type_variable_names,
                            search_type,
                            env,
                        )
                    })
                    .try_collect::<_, Vec<_>, _>()?
                    .into_iter()
                    .rev()
                {
                    tuple = TypeUnit::Tuple(a, tuple).into();
                }
                let id = TypeId::get(
                    env.imports.get_true_name_with_path_unchecked(
                        module_path,
                        module_path,
                        &t.path,
                        env.token_map,
                    )?,
                    env,
                )?;
                env.token_map.insert(
                    t.path.last().unwrap().2,
                    TokenMapEntry::TypeId(id),
                );
                Ok(TypeUnit::Tuple(TypeUnit::Const { id }.into(), tuple).into())
            }
        }
    }
}

fn type_to_type_with_forall(
    t: ast_step1::Type,
    module_path: ModulePath,
    mut type_variable_names: FxHashMap<Name, TypeVariable>,
    forall: ast_step1::Forall,
    env: &mut Env<'_, '_>,
) -> Result<Type, CompileError> {
    let mut variable_requirements = Vec::new();
    let mut type_parameters = Vec::new();
    for (s, interface_names) in forall.type_variables {
        env.token_map.insert(s.2, TokenMapEntry::TypeVariable);
        let v = TypeVariable::new();
        for name in interface_names {
            env.token_map.insert(name.2, TokenMapEntry::Interface);
            for (name, t, self_) in
                &env.interface_decls[&Name::from_str(module_path, name.0)]
            {
                variable_requirements.push((
                    name.clone(),
                    t.clone()
                        .replace_num(*self_, &TypeUnit::Variable(v).into()),
                ))
            }
        }
        type_parameters.push(v);
        type_variable_names.insert(Name::from_str(module_path, s.0), v);
    }
    let mut t = type_to_type(
        &t,
        module_path,
        &type_variable_names,
        SearchMode::Normal,
        env,
    )?;
    if !variable_requirements.is_empty() {
        t = TypeUnit::Restrictions {
            t,
            variable_requirements,
            subtype_relations: Default::default(),
        }
        .into();
    }
    for p in type_parameters.into_iter().rev() {
        t = t.replace_num(
            p,
            &TypeUnit::Variable(TypeVariable::RecursiveIndex(0)).into(),
        );
        t = TypeUnit::TypeLevelFn(t).into();
    }
    Ok(t)
}

impl std::fmt::Display for ConstructorId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstructorId::Intrinsic(a) => std::fmt::Debug::fmt(a, f),
            ConstructorId::DeclId(a) => a.fmt(f),
        }
    }
}
#[derive(Debug, Clone)]
struct Forall(Vec<TypeVariable>);

impl IntoIterator for SubtypeRelations {
    type Item = (Type, Type, RelOrigin);
    type IntoIter = std::collections::btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'b> IntoIterator for &'b SubtypeRelations {
    type Item = &'b (Type, Type, RelOrigin);
    type IntoIter =
        std::collections::btree_set::Iter<'b, (Type, Type, RelOrigin)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl FromIterator<(Type, Type, RelOrigin)> for SubtypeRelations {
    fn from_iter<T: IntoIterator<Item = (Type, Type, RelOrigin)>>(
        iter: T,
    ) -> Self {
        let mut s = Self::default();
        for r in iter {
            s.insert(r);
        }
        s
    }
}

impl SubtypeRelations {
    pub fn iter(&self) -> impl Iterator<Item = &(Type, Type, RelOrigin)> {
        self.0.iter()
    }

    pub fn insert(&mut self, value: (Type, Type, RelOrigin)) -> bool {
        debug_assert!(!value.0.contains_restriction());
        debug_assert!(!value.1.contains_restriction());
        self.0.insert(value)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl Extend<(Type, Type, RelOrigin)> for SubtypeRelations {
    fn extend<T: IntoIterator<Item = (Type, Type, RelOrigin)>>(
        &mut self,
        iter: T,
    ) {
        for r in iter {
            self.insert(r);
        }
    }
}

impl Display for PatternUnitForRestriction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternUnitForRestriction::I64 => write!(f, "I64Lit"),
            PatternUnitForRestriction::Str => write!(f, "StrLit"),
            PatternUnitForRestriction::Binder(b, decl_id) => {
                write!(f, "Bind({b}, id = {decl_id})")
            }
            PatternUnitForRestriction::Const { id } => {
                write!(f, ":{id}")
            }
            PatternUnitForRestriction::Tuple(a, b) => write!(f, "({a}, {b})"),
            PatternUnitForRestriction::TypeRestriction(p, t) => {
                write!(f, "({p} : {t})")
            }
        }
    }
}

impl PatternUnitForRestriction {
    pub fn covariant_type_variables(&self) -> Vec<TypeVariable> {
        match self {
            PatternUnitForRestriction::I64
            | PatternUnitForRestriction::Str
            | PatternUnitForRestriction::Const { .. } => Default::default(),
            PatternUnitForRestriction::Binder(t, _) => {
                t.covariant_type_variables()
            }
            PatternUnitForRestriction::Tuple(a, b) => a
                .covariant_type_variables()
                .into_iter()
                .chain(b.covariant_type_variables())
                .collect(),
            PatternUnitForRestriction::TypeRestriction(p, _) => {
                p.covariant_type_variables()
            }
        }
    }

    pub fn contravariant_type_variables(&self) -> Vec<TypeVariable> {
        match self {
            PatternUnitForRestriction::I64
            | PatternUnitForRestriction::Str
            | PatternUnitForRestriction::Const { .. } => Default::default(),
            PatternUnitForRestriction::Binder(t, _) => {
                t.contravariant_type_variables()
            }
            PatternUnitForRestriction::Tuple(a, b) => a
                .contravariant_type_variables()
                .into_iter()
                .chain(b.contravariant_type_variables())
                .collect(),
            PatternUnitForRestriction::TypeRestriction(p, _) => {
                p.contravariant_type_variables()
            }
        }
    }

    pub fn all_type_variables_vec(&self) -> Vec<TypeVariable> {
        match self {
            PatternUnitForRestriction::I64
            | PatternUnitForRestriction::Str
            | PatternUnitForRestriction::Const { .. } => Default::default(),
            PatternUnitForRestriction::Binder(t, _) => {
                t.all_type_variables_vec()
            }
            PatternUnitForRestriction::Tuple(a, b) => a
                .all_type_variables_vec()
                .into_iter()
                .chain(b.all_type_variables_vec())
                .collect(),
            PatternUnitForRestriction::TypeRestriction(p, _) => {
                p.all_type_variables_vec()
            }
        }
    }

    pub fn all_type_variables(&self) -> FxHashSet<TypeVariable> {
        self.all_type_variables_vec().into_iter().collect()
    }

    pub fn decl_type_map(&self) -> Vec<(DeclId, &Type)> {
        match self {
            PatternUnitForRestriction::I64
            | PatternUnitForRestriction::Str
            | PatternUnitForRestriction::Const { .. } => Default::default(),
            PatternUnitForRestriction::Binder(t, decl_id) => {
                vec![(*decl_id, t)]
            }
            PatternUnitForRestriction::Tuple(a, b) => a
                .decl_type_map()
                .into_iter()
                .chain(b.decl_type_map())
                .collect(),
            PatternUnitForRestriction::TypeRestriction(p, _) => {
                p.decl_type_map()
            }
        }
    }

    pub fn map_type<F>(self, f: F) -> Self
    where
        F: FnMut(Type) -> Type,
    {
        self.map_type_rec(f).0
    }

    fn map_type_rec<F>(self, mut f: F) -> (Self, F)
    where
        F: FnMut(Type) -> Type,
    {
        use PatternUnitForRestriction::*;
        match self {
            a @ (I64 | Str | Const { .. }) => (a, f),
            Tuple(a, b) => {
                let (a, f) = a.map_type_rec(f);
                let (b, f) = b.map_type_rec(f);
                (Tuple(a.into(), b.into()), f)
            }
            Binder(t, decl_id) => (Binder(f(t), decl_id), f),
            TypeRestriction(p, t) => {
                let (p, mut f) = p.map_type_rec(f);
                (TypeRestriction(Box::new(p), f(t)), f)
            }
        }
    }
}

pub fn collect_tuple_rev(tuple: &Type) -> Vec<Vec<&Type>> {
    tuple
        .iter()
        .flat_map(|tuple| match &**tuple {
            TypeUnit::Tuple(h, t) => collect_tuple_rev(t)
                .into_iter()
                .map(|mut v| {
                    v.push(h);
                    v
                })
                .collect(),
            TypeUnit::Const {
                id: TypeId::Intrinsic(IntrinsicType::Unit),
                ..
            } => vec![Vec::new()],
            _ => panic!(),
        })
        .collect()
}
