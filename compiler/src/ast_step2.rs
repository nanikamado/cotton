pub mod imports;
mod type_alias_map;
pub mod type_display;
pub mod types;

use self::imports::Imports;
use self::type_alias_map::{SearchMode, TypeAliasMap};
use self::types::{Type, TypeMatchable, TypeUnit, TypeVariable};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::ident_id::IdentId;
use crate::ast_step1::name_id::Path;
use crate::ast_step1::token_map::{TokenMap, TokenMapEntry};
use crate::ast_step1::{self, merge_span};
use crate::ast_step3::{VariableId, VariableRequirement};
use crate::errors::CompileError;
use crate::intrinsics::{IntrinsicConstructor, IntrinsicType, INTRINSIC_TYPES};
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use once_cell::sync::Lazy;
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
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Field {
    pub type_: TypeVariable,
    pub name: Path,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: Path,
    pub fields: Vec<Field>,
    pub type_variable_decls: Vec<(TypeVariable, Path)>,
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
    Apply(Box<PatternUnitForRestriction>),
}

pub type PatternForRestriction = Vec<(PatternUnitForRestriction, Span)>;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct PatternRestriction {
    pub type_: Type,
    pub pattern: PatternForRestriction,
    pub span: Span,
    pub allow_inexhaustive: bool,
}

pub type PatternRestrictions = Vec<PatternRestriction>;
type ModulePath = Path;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
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
pub struct VariableDecl<'a> {
    pub name: Path,
    pub type_annotation: Option<Annotation>,
    pub value: ExprWithTypeAndSpan<'a, TypeVariable>,
    pub decl_id: DeclId,
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Annotation {
    pub unfixed: Type,
    pub fixed: Type,
    pub implicit_parameters: Vec<(String, Type, DeclId)>,
    pub fixed_parameter_names: FxHashMap<TypeUnit, Path>,
    pub span: Span,
}

pub type ExprWithTypeAndSpan<'a, T> = (Expr<'a, T>, T, Span);

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a, T> {
    Lambda(Vec<FnArm<'a, T>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident {
        name: &'a parser::Path,
        ident_id: IdentId,
    },
    ResolvedIdent {
        variable_id: VariableId,
        type_: Type,
        name: Option<Path>,
    },
    Call(
        Box<ExprWithTypeAndSpan<'a, T>>,
        Box<ExprWithTypeAndSpan<'a, T>>,
    ),
    Do(Vec<ExprWithTypeAndSpan<'a, T>>),
    TypeAnnotation(Box<ExprWithTypeAndSpan<'a, T>>, Type),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a, T> {
    pub pattern: Vec<(Pattern<'a, T>, Span)>,
    pub expr: ExprWithTypeAndSpan<'a, T>,
}

/// Represents a multi-case pattern which matches if any of the `PatternUnit` in it matches.
/// It should have at least one `PatternUnit`.
#[derive(Debug, PartialEq, Clone)]
pub struct Pattern<'a, T, E = ExprWithTypeAndSpan<'a, TypeVariable>>(
    pub Vec<PatternUnit<'a, T, E>>,
);

#[derive(Debug, PartialEq, Clone)]
pub enum PatternUnit<'a, T, E = ExprWithTypeAndSpan<'a, TypeVariable>> {
    I64(&'a str),
    Str(&'a str),
    Constructor {
        name: Path,
        id: ConstructorId,
        args: Vec<Pattern<'a, T, E>>,
    },
    Binder(String, DeclId, T),
    ResolvedBinder(DeclId, T),
    Underscore,
    TypeRestriction(Pattern<'a, T, E>, Type),
    Apply(Box<Pattern<'a, T, E>>, Vec<ApplyPattern<'a, T, E>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct ApplyPattern<'a, T, E> {
    pub function: E,
    pub post_pattern: Pattern<'a, T, E>,
}

#[derive(Debug)]
enum FlatMapEnv<'a> {
    FlatMap {
        decl_id: DeclId,
        type_of_decl: TypeVariable,
        pre_calc: ExprWithTypeAndSpan<'a, TypeVariable>,
        question_span: Span,
    },
    Decl(DeclId, ExprWithTypeAndSpan<'a, TypeVariable>),
}

struct WithFlatMapEnv<'a, Value = ExprWithTypeAndSpan<'a, TypeVariable>> {
    value: Value,
    env: Vec<FlatMapEnv<'a>>,
}

static TYPE_NAMES: Lazy<RwLock<FxHashMap<TypeId, Path>>> = Lazy::new(|| {
    RwLock::new(
        INTRINSIC_TYPES
            .iter()
            .map(|(name, id)| {
                (TypeId::Intrinsic(*id), Path::from_str_intrinsic(name))
            })
            .collect(),
    )
});

pub fn get_type_name(type_id: TypeId) -> Path {
    *TYPE_NAMES.read().unwrap().get(&type_id).unwrap()
}

impl<'a> Ast<'a> {
    pub fn from(
        ast: ast_step1::Ast<'a>,
        token_map: &mut TokenMap,
        imports: &mut Imports,
    ) -> Result<Self, CompileError> {
        let mut data_decls = Vec::new();
        let mut variable_decls = Vec::new();
        let mut env = Env {
            token_map,
            type_alias_map: &mut TypeAliasMap::default(),
            interface_decls: &mut Default::default(),
            imports,
            data_decl_map: &mut FxHashMap::default(),
            field_names: &mut Default::default(),
        };
        collect_decls(
            ast,
            Path::root(),
            &mut env,
            &mut variable_decls,
            &mut data_decls,
        )?;
        let entry_point = variable_decls
            .iter()
            .find(|d| d.name == Path::from_str(Path::pkg_root(), "main"))
            .unwrap_or_else(|| panic!("entry point not found"))
            .decl_id;
        Ok(Self {
            variable_decl: variable_decls,
            data_decl: data_decls,
            entry_point,
        })
    }
}

fn collect_decls<'a>(
    ast: ast_step1::Ast<'a>,
    module_path: ModulePath,
    env: &mut Env<'_, 'a>,
    variable_decls: &mut Vec<VariableDecl<'a>>,
    data_decls: &mut Vec<DataDecl>,
) -> Result<(), CompileError> {
    collect_data_and_type_alias_decls(&ast, module_path, data_decls, env)?;
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
    data_decls: &mut Vec<DataDecl>,
    env: &mut Env<'_, 'a>,
) -> Result<(), CompileError> {
    for d in &ast.variable_decl {
        env.imports.add_variable(
            d.name,
            VariableId::Global(d.decl_id),
            d.is_public,
        );
    }
    data_decls.extend(ast.data_decl.iter().map(|d| {
        let mut type_variables = FxHashMap::default();
        for ((name, _, id), interfaces) in &d.type_variables.type_variables {
            env.token_map.insert(*id, TokenMapEntry::TypeVariable);
            type_variables.insert(name.as_str(), TypeVariable::new());
            for path in interfaces {
                env.token_map.insert(
                    path.path.last().unwrap().2,
                    TokenMapEntry::Interface,
                );
            }
        }
        env.imports.add_data(
            d.name,
            ConstructorId::DeclId(d.decl_id),
            d.is_public,
        );
        env.imports.add_variable(
            d.name,
            VariableId::Constructor(d.decl_id),
            d.is_public,
        );
        env.imports
            .add_type(d.name, TypeId::DeclId(d.decl_id), d.is_public);
        for (i, f) in d.fields.iter().enumerate() {
            env.imports.add_variable(
                f.name,
                VariableId::FieldAccessor {
                    constructor: d.decl_id,
                    field: i,
                },
                f.is_public,
            );
            env.imports.add_accessor(f.name, d.decl_id, i, f.is_public);
        }
        let d = DataDecl {
            name: d.name,
            fields: d
                .fields
                .iter()
                .map(|f| {
                    env.token_map
                        .insert(f.type_.2, TokenMapEntry::TypeVariable);
                    Field {
                        type_: type_variables[f.type_.0],
                        name: f.name,
                    }
                })
                .collect(),
            decl_id: d.decl_id,
            type_variable_decls: type_variables
                .into_iter()
                .map(|(n, v)| (v, Path::from_str(module_path, n)))
                .collect(),
        };
        env.field_names
            .insert(ConstructorId::DeclId(d.decl_id), d.clone());
        d
    }));
    env.type_alias_map.add_decls(
        &ast.type_alias_decl,
        env.token_map,
        module_path,
        env.imports,
    );
    for m in &ast.modules {
        env.imports.add_module(m.name, m.is_public);
        collect_data_and_type_alias_decls(&m.ast, m.name, data_decls, env)?
    }
    Ok(())
}

fn collect_interface_decls<'a>(
    ast: &ast_step1::Ast<'a>,
    module_path: ModulePath,
    env: &mut Env<'a, '_>,
) -> Result<(), CompileError> {
    env.interface_decls.extend(
        ast.interface_decl
            .iter()
            .map(|i| {
                env.token_map.insert(i.name.2, TokenMapEntry::Interface);
                let name = Path::from_str(module_path, i.name.0);
                env.imports.add_interface(name, i.is_public);
                Ok((
                    name,
                    i.variables
                        .iter()
                        .map(|(name, t, forall)| {
                            let self_ = TypeVariable::new();
                            let t = type_to_type_with_forall(
                                t.clone(),
                                module_path,
                                std::iter::once((
                                    Path::from_str(module_path, "Self"),
                                    self_,
                                ))
                                .collect(),
                                forall,
                                &mut Env {
                                    interface_decls: &mut Default::default(),
                                    token_map: env.token_map,
                                    type_alias_map: env.type_alias_map,
                                    imports: env.imports,
                                    data_decl_map: env.data_decl_map,
                                    field_names: env.field_names,
                                },
                            )?;
                            env.token_map.insert(
                                name.2,
                                TokenMapEntry::VariableDeclInInterface(
                                    t.clone(),
                                ),
                            );
                            Ok((name.0, t, self_))
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
    interface_decls:
        &'a mut FxHashMap<Path, Vec<(&'a str, Type, TypeVariable)>>,
    imports: &'a mut Imports,
    data_decl_map: &'a mut FxHashMap<Path, DeclId>,
    field_names: &'a mut FxHashMap<ConstructorId, DataDecl>,
}

fn collect_variable_decls<'a>(
    ast: ast_step1::Ast<'a>,
    module_path: ModulePath,
    variable_decls: &mut Vec<VariableDecl<'a>>,
    env: &mut Env<'_, '_>,
) -> Result<(), CompileError> {
    variable_decls.extend(
        ast.variable_decl
            .into_iter()
            .map(|d| -> Result<VariableDecl<'a>, CompileError> {
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

impl<'a, T, U> From<PatternUnit<'a, T, U>> for Pattern<'a, T, U> {
    fn from(p: PatternUnit<'a, T, U>) -> Self {
        Pattern(vec![p])
    }
}

fn variable_decl<'a>(
    v: ast_step1::VariableDecl<'a>,
    module_path: ModulePath,
    env: &mut Env<'_, '_>,
    type_variable_names: &FxHashMap<Path, TypeVariable>,
) -> Result<WithFlatMapEnv<'a, VariableDecl<'a>>, CompileError> {
    let expr = expr(v.value, module_path, type_variable_names, env)?;
    let d = VariableDecl {
        type_annotation: v
            .type_annotation
            .map(|(t, forall, span)| {
                let implicit_type_parameters: Vec<_> = forall
                    .type_variables
                    .iter()
                    .map(|(name, _)| Path::from_str(module_path, &name.0))
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

pub static FLAT_MAP_PATH: Lazy<parser::Path> = Lazy::new(|| parser::Path {
    from_root: false,
    path: vec![("flat_map".to_string(), None, None)],
});

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
                        Pattern(vec![PatternUnit::ResolvedBinder(
                            decl_id,
                            type_of_decl,
                        )]),
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
                                        name: &FLAT_MAP_PATH,
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

fn expr<'a>(
    e: ast_step1::ExprWithSpan<'a>,
    module_path: ModulePath,
    type_variable_names: &FxHashMap<Path, TypeVariable>,
    env: &mut Env<'_, '_>,
) -> Result<WithFlatMapEnv<'a>, CompileError> {
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
        ast_step1::Expr::Number(n) => (Vec::new(), Number(n)),
        ast_step1::Expr::StrLiteral(s) => (Vec::new(), StrLiteral(s)),
        ast_step1::Expr::Ident { path } => {
            let ident_id = IdentId::new();
            env.token_map.insert(
                path.path.last().unwrap().2,
                TokenMapEntry::Ident(ident_id),
            );
            (
                Vec::new(),
                Ident {
                    name: path,
                    ident_id,
                },
            )
        }
        ast_step1::Expr::Record { path, fields } => {
            let (name, id) = env.imports.get_constructor(
                module_path,
                if path.from_root {
                    Path::pkg_root()
                } else {
                    module_path
                },
                &path.path,
                env.token_map,
            )?;
            env.token_map.insert(
                path.path.last().unwrap().2,
                TokenMapEntry::Constructor(id),
            );
            let fields: FxHashMap<_, _> =
                fields.into_iter().map(|((n, _, _), e)| (n, e)).collect();
            let data_decl = env.field_names[&id].clone();
            let ConstructorId::DeclId(id) = id else {
                panic!()
            };
            let mut e: Expr<_> = Expr::ResolvedIdent {
                variable_id: VariableId::Constructor(id),
                type_: constructor_type(&data_decl).into(),
                name: Some(name),
            };
            let mut v = Vec::new();
            for f in &data_decl.fields {
                let mut f = expr(
                    (
                        fields[f.name.split().unwrap().1.as_str()].clone(),
                        span.clone(),
                    ),
                    module_path,
                    type_variable_names,
                    env,
                )?;
                v.append(&mut f.env);
                e = Expr::Call(
                    Box::new((e, TypeVariable::new(), span.clone())),
                    Box::new(f.value),
                );
            }
            (v, e)
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
                                variable_id: VariableId::Local(decl_id),
                                type_: TypeUnit::Variable(f_type).into(),
                                name: None,
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
                    variable_id: VariableId::Local(decl_id),
                    type_: TypeUnit::Variable(type_of_decl).into(),
                    name: None,
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

pub fn constructor_type(d: &DataDecl) -> TypeUnit {
    let fields: Vec<_> = d
        .fields
        .iter()
        .enumerate()
        .map(|(_, _t)| TypeUnit::Variable(TypeVariable::new()).into())
        .rev()
        .collect();
    let mut t = TypeUnit::Tuple(
        TypeUnit::Const {
            id: TypeId::DeclId(d.decl_id),
        }
        .into(),
        Type::argument_tuple_from_arguments(fields.clone()),
    );
    for field in fields.into_iter().rev() {
        t = TypeUnit::Fn(field, t.into())
    }
    t
}

pub static UNIT_PATH: Lazy<parser::Path> = Lazy::new(|| parser::Path {
    from_root: false,
    path: vec![("()".to_string(), None, None)],
});

fn add_expr_in_do<'a>(
    e: ast_step1::ExprWithSpan<'a>,
    module_path: ModulePath,
    mut es: Vec<ExprWithTypeAndSpan<'a, TypeVariable>>,
    es_span: Span,
    type_variable_names: &FxHashMap<Path, TypeVariable>,
    env: &mut Env<'_, '_>,
) -> Result<(Vec<ExprWithTypeAndSpan<'a, TypeVariable>>, Span), CompileError> {
    match e {
        (ast_step1::Expr::Decl(d), d_span) => {
            let d = variable_decl(*d, module_path, env, type_variable_names)?;
            if es.is_empty() {
                Ok((
                    vec![
                        (
                            Expr::Ident {
                                name: &UNIT_PATH,
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

fn fn_arm<'a>(
    arm: ast_step1::FnArm<'a>,
    module_path: ModulePath,
    type_variable_names: &FxHashMap<Path, TypeVariable>,
    env: &mut Env<'_, '_>,
) -> Result<FnArm<'a, TypeVariable>, CompileError> {
    Ok(FnArm {
        pattern: arm
            .pattern
            .into_iter()
            .map(|(p, span)| {
                Ok((pattern(p, module_path, type_variable_names, env)?, span))
            })
            .try_collect()?,
        expr: catch_flat_map(expr(
            arm.expr,
            module_path,
            type_variable_names,
            env,
        )?)?,
    })
}

impl Path {
    fn is_same_as_or_ancestor_of(self, path: Path) -> bool {
        if self.is_root() || self == path {
            true
        } else if let Some((path, _)) = path.split() {
            self.is_same_as_or_ancestor_of(path)
        } else {
            false
        }
    }
}

fn pattern<'a>(
    p: ast_step1::Pattern<'a>,
    module_path: ModulePath,
    type_variable_names: &FxHashMap<Path, TypeVariable>,
    env: &mut Env<'_, '_>,
) -> Result<Pattern<'a, TypeVariable>, CompileError> {
    use PatternUnit::*;
    Ok(match p {
        ast_step1::Pattern::Number(n) => I64(n).into(),
        ast_step1::Pattern::StrLiteral(s) => Str(s).into(),
        ast_step1::Pattern::Constructor { path, args } => {
            let (name, id) = env.imports.get_constructor(
                module_path,
                if path.from_root {
                    Path::pkg_root()
                } else {
                    module_path
                },
                &path.path,
                env.token_map,
            )?;
            env.token_map.insert(
                path.path.last().unwrap().2,
                TokenMapEntry::Constructor(id),
            );
            Constructor {
                name,
                id,
                args: args
                    .into_iter()
                    .map(|arg| {
                        pattern(arg, module_path, type_variable_names, env)
                    })
                    .try_collect()?,
            }
            .into()
        }
        ast_step1::Pattern::Binder(name) => {
            let decl_id = DeclId::new();
            env.token_map.insert(name.2, TokenMapEntry::Decl(decl_id));
            Binder(name.0.to_string(), decl_id, TypeVariable::new()).into()
        }
        ast_step1::Pattern::Underscore => Underscore.into(),
        ast_step1::Pattern::TypeRestriction(p, t, forall) => {
            let t = type_to_type_with_forall(
                t,
                module_path,
                Default::default(),
                forall,
                env,
            )?;
            let p = pattern(*p, module_path, type_variable_names, env)?;
            TypeRestriction(p, t).into()
        }
        ast_step1::Pattern::Apply(pre_pattern, applications) => {
            let mut pre_pattern =
                pattern(*pre_pattern, module_path, type_variable_names, env)?;
            let mut functions;
            if pre_pattern.0.len() == 1 {
                match &mut pre_pattern.0[0] {
                    PatternUnit::Constructor {
                        name: _,
                        id: ConstructorId::DeclId(constructor_id),
                        args,
                    } if args.is_empty() => {
                        let mut new_args =
                            vec![
                                None;
                                env.field_names
                                    [&ConstructorId::DeclId(*constructor_id)]
                                    .fields
                                    .len()
                            ];
                        functions = Vec::new();
                        for a in applications {
                            if let ast_step1::Expr::Ident { path } =
                                &a.function.0
                            {
                                if let Some(field) =
                                    env.imports.get_accessor_with_path(
                                        module_path,
                                        if path.from_root {
                                            Path::pkg_root()
                                        } else {
                                            module_path
                                        },
                                        &path.path,
                                        *constructor_id,
                                        env.token_map,
                                    )?
                                {
                                    debug_assert!(new_args[field].is_none());
                                    new_args[field] = Some(pattern(
                                        a.post_pattern,
                                        module_path,
                                        type_variable_names,
                                        env,
                                    )?);
                                } else {
                                    functions.push(a);
                                }
                            } else {
                                functions.push(a);
                            }
                        }
                        args.extend(new_args.into_iter().map(|a| {
                            a.unwrap_or_else(|| {
                                Pattern(vec![PatternUnit::Underscore])
                            })
                        }));
                    }
                    _ => {
                        functions = applications;
                    }
                }
            } else {
                functions = applications;
            }
            if functions.is_empty() {
                pre_pattern
            } else {
                Apply(
                    Box::new(pre_pattern),
                    functions
                        .into_iter()
                        .map(|a| {
                            Ok(ApplyPattern {
                                function: catch_flat_map(expr(
                                    a.function,
                                    module_path,
                                    type_variable_names,
                                    env,
                                )?)?,
                                post_pattern: pattern(
                                    a.post_pattern,
                                    module_path,
                                    type_variable_names,
                                    env,
                                )?,
                            })
                        })
                        .try_collect()?,
                )
                .into()
            }
        }
    })
}

fn type_to_type(
    t: &ast_step1::Type,
    module_path: ModulePath,
    type_variable_names: &FxHashMap<Path, TypeVariable>,
    search_type: SearchMode,
    env: &mut Env<'_, '_>,
) -> Result<Type, CompileError> {
    match (t.path.path.len(), t.path.path.last().unwrap().0.as_str()) {
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
            let base_path = env.imports.get_module_with_path(
                module_path,
                if t.path.from_root {
                    Path::pkg_root()
                } else {
                    module_path
                },
                &t.path.path[..t.path.path.len() - 1],
                env.token_map,
                &Default::default(),
            )?;
            let (name, span, token_id) = t.path.path.last().unwrap();
            let path = Path::from_str(base_path, name);
            if let Some(n) = type_variable_names.get(&path) {
                env.token_map.insert(*token_id, TokenMapEntry::TypeVariable);
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
            } else {
                let const_or_alias = env.imports.get_type(
                    module_path,
                    base_path,
                    name,
                    span.clone(),
                    env.token_map,
                )?;
                match const_or_alias {
                    imports::ConstOrAlias::Const(id) => {
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
                        env.token_map.insert(
                            t.path.path.last().unwrap().2,
                            TokenMapEntry::TypeId(id),
                        );
                        Ok(TypeUnit::Tuple(
                            TypeUnit::Const { id }.into(),
                            tuple,
                        )
                        .into())
                    }
                    imports::ConstOrAlias::Alias(name) => {
                        let mut unaliased = env
                            .get_type_from_alias(
                                (name, *token_id),
                                type_variable_names,
                                if search_type == SearchMode::Normal {
                                    SearchMode::Alias
                                } else {
                                    SearchMode::AliasSub
                                },
                            )?
                            .unwrap();
                        for a in &t.args {
                            unaliased = unaliased.type_level_function_apply(
                                type_to_type(
                                    a,
                                    module_path,
                                    type_variable_names,
                                    search_type,
                                    env,
                                )?,
                            );
                        }
                        Ok(unaliased)
                    }
                }
            }
        }
    }
}

fn type_to_type_with_forall(
    t: ast_step1::Type,
    module_path: ModulePath,
    mut type_variable_names: FxHashMap<Path, TypeVariable>,
    forall: &parser::Forall,
    env: &mut Env<'_, '_>,
) -> Result<Type, CompileError> {
    let mut variable_requirements = Vec::new();
    let mut type_parameters = Vec::new();
    for (s, interface_names) in &forall.type_variables {
        env.token_map.insert(s.2, TokenMapEntry::TypeVariable);
        let v = TypeVariable::new();
        for path in interface_names {
            let name = env.imports.get_interface(
                module_path,
                if path.from_root {
                    Path::pkg_root()
                } else {
                    module_path
                },
                &path.path,
                env.token_map,
            )?;
            for (name, t, self_) in &env.interface_decls[&name] {
                variable_requirements.push((
                    *name,
                    t.clone()
                        .replace_num(*self_, &TypeUnit::Variable(v).into()),
                ))
            }
        }
        type_parameters.push(v);
        type_variable_names.insert(Path::from_str(module_path, &s.0), v);
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
            variable_requirements: variable_requirements
                .into_iter()
                .map(|(name, t)| (name.to_string(), t))
                .collect(),
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
            PatternUnitForRestriction::Apply(p) => {
                write!(f, "Apply({p})")
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
            PatternUnitForRestriction::Apply(p) => p.covariant_type_variables(),
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
            PatternUnitForRestriction::Apply(p) => {
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
            PatternUnitForRestriction::Apply(p) => p.all_type_variables_vec(),
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
            PatternUnitForRestriction::Apply(p) => p.decl_type_map(),
        }
    }

    pub fn map_type<F>(self, mut f: F) -> Self
    where
        F: FnMut(Type) -> Type,
    {
        self.map_type_rec(&mut f)
    }

    fn map_type_rec<F>(self, f: &mut F) -> Self
    where
        F: FnMut(Type) -> Type,
    {
        use PatternUnitForRestriction::*;
        match self {
            a @ (I64 | Str | Const { .. }) => a,
            Tuple(a, b) => {
                let a = a.map_type_rec(f);
                let b = b.map_type_rec(f);
                Tuple(a.into(), b.into())
            }
            Binder(t, decl_id) => Binder(f(t), decl_id),
            TypeRestriction(p, t) => {
                let p = p.map_type_rec(f);
                TypeRestriction(Box::new(p), f(t))
            }
            Apply(a) => Apply(Box::new(a.map_type_rec(f))),
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
