pub mod imports;
mod type_alias_map;
pub mod type_display;
pub mod types;
mod variance;

use self::imports::Imports;
use self::type_alias_map::{SearchMode, TypeAliasMap};
use self::types::{Type, TypeUnit, TypeVariable};
use self::variance::{DummyVarianceMap, VarianceMapI};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::ident_id::IdentId;
use crate::ast_step1::name_id::Path;
use crate::ast_step1::token_map::{TokenMap, TokenMapEntry};
use crate::ast_step1::{self, merge_span};
use crate::ast_step2::variance::VarianceMap;
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
    pub entry_point: Option<DeclId>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Field {
    pub type_: Type,
    pub name: Path,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: Path,
    pub fields: Vec<Field>,
    pub decl_id: DeclId,
    pub type_parameter_len: usize,
    pub constructed_type: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
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

#[derive(Debug, Clone, PartialEq, Eq, Default, Hash)]
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
        id: ConstructorId,
        args: Vec<(Pattern<'a, T, E>, Span)>,
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

pub fn get_type_name(type_id: TypeId) -> Option<Path> {
    TYPE_NAMES.read().unwrap().get(&type_id).copied()
}

impl<'a> Ast<'a> {
    pub fn from(
        ast: ast_step1::Ast<'a>,
        token_map: &mut TokenMap,
        imports: &mut Imports,
    ) -> Result<Self, CompileError> {
        let mut variable_decls = Vec::new();
        let mut data_decls = Default::default();
        let mut env = Env {
            token_map,
            type_alias_map: &mut TypeAliasMap::default(),
            interface_decls: &mut Default::default(),
            imports,
            data_decl_map: &mut FxHashMap::default(),
            data_decls: &mut data_decls,
        };
        collect_decls(ast, Path::root(), &mut env, &mut variable_decls)?;
        let entry_point = variable_decls
            .iter()
            .find(|d| d.name == Path::from_str(Path::pkg_root(), "main"))
            .map(|d| d.decl_id);
        Ok(Self {
            variable_decl: variable_decls,
            data_decl: data_decls.into_values().collect(),
            entry_point,
        })
    }
}

fn collect_decls<'a>(
    ast: ast_step1::Ast<'a>,
    module_path: ModulePath,
    env: &mut Env<'_, 'a>,
    variable_decls: &mut Vec<VariableDecl<'a>>,
) -> Result<(), CompileError> {
    collect_data_and_type_alias_decls(&ast, module_path, env)?;
    let mut union_of_fields = FxHashMap::default();
    collect_union_of_fields(&ast, module_path, env, &mut union_of_fields)?;
    debug_assert!(env.data_decl_map.is_empty());
    let mut variance_map = VarianceMap::new(union_of_fields);
    collect_interface_decls(&ast, module_path, env, &mut variance_map)?;
    env.data_decl_map
        .extend(env.data_decls.iter().map(|(_, d)| (d.name, d.decl_id)));
    {
        TYPE_NAMES.write().unwrap().extend(
            env.data_decls
                .iter()
                .map(|(_, d)| (TypeId::DeclId(d.decl_id), d.name)),
        );
    }
    collect_variable_decls(
        ast,
        module_path,
        variable_decls,
        env,
        &mut variance_map,
    )?;
    Ok(())
}

fn collect_data_and_type_alias_decls<'a>(
    ast: &ast_step1::Ast<'a>,
    module_path: ModulePath,
    env: &mut Env<'_, 'a>,
) -> Result<(), CompileError> {
    for d in &ast.variable_decl {
        env.imports.add_variable(
            d.name,
            VariableId::Global(d.decl_id),
            d.is_public,
        );
    }
    for d in &ast.data_decl {
        for ((_, _, id), interfaces) in &d.type_variables.type_variables {
            env.token_map.insert(*id, TokenMapEntry::TypeVariable);
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
        env.imports.add_type(
            d.name,
            TypeId::DeclId(d.decl_id),
            d.is_public,
            d.type_variables.type_variables.len(),
        );
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
    }
    env.type_alias_map.add_decls(
        &ast.type_alias_decl,
        env.token_map,
        module_path,
        env.imports,
    );
    for m in &ast.modules {
        env.imports.add_module(m.name, m.is_public);
        collect_data_and_type_alias_decls(&m.ast, m.name, env)?
    }
    Ok(())
}

fn collect_union_of_fields<'a>(
    ast: &ast_step1::Ast<'a>,
    module_path: ModulePath,
    env: &mut Env<'a, '_>,
    union_of_fields: &mut FxHashMap<TypeId, Type>,
) -> Result<(), CompileError> {
    for d in &ast.data_decl {
        let mut type_variables = FxHashMap::default();
        for (i, ((name, _, _), _)) in
            d.type_variables.type_variables.iter().enumerate()
        {
            let v = TypeVariable::RecursiveIndex(i);
            type_variables.insert(Path::from_str(module_path, name), v);
        }
        let mut uof = Type::default();
        for f in &d.fields {
            let type_ = type_to_type(
                &f.type_,
                module_path,
                &type_variables,
                SearchMode::Normal,
                env,
                &mut DummyVarianceMap,
            )?;
            uof.union_in_place(type_.clone());
        }
        union_of_fields.insert(TypeId::DeclId(d.decl_id), uof);
    }
    for m in &ast.modules {
        collect_union_of_fields(&m.ast, m.name, env, union_of_fields)?;
    }
    Ok(())
}

#[allow(clippy::type_complexity)]
fn collect_interface_decls<'a>(
    ast: &ast_step1::Ast<'a>,
    module_path: ModulePath,
    env: &mut Env<'a, '_>,
    variance_map: &mut VarianceMap,
) -> Result<(), CompileError> {
    for d in &ast.data_decl {
        let mut type_variables = FxHashMap::default();
        for (i, ((name, _, _), _)) in
            d.type_variables.type_variables.iter().rev().enumerate()
        {
            let v = TypeVariable::RecursiveIndex(i);
            type_variables.insert(Path::from_str(module_path, name), v);
        }
        let fields: Vec<_> = d
            .fields
            .iter()
            .map(|f| {
                let type_ = type_to_type(
                    &f.type_,
                    module_path,
                    &type_variables,
                    SearchMode::Normal,
                    env,
                    variance_map,
                )?;
                Ok(Field {
                    type_,
                    name: f.name,
                })
            })
            .try_collect()?;
        let type_parameter_len = d.type_variables.type_variables.len();
        let constructed_type = (0..type_parameter_len).fold(
            TypeUnit::Const {
                id: TypeId::Intrinsic(IntrinsicType::Unit),
            }
            .into(),
            |acc, v| {
                let co = variance_map.type_has_arg_in_covariant_position(
                    TypeId::DeclId(d.decl_id),
                    type_parameter_len - 1 - v,
                );
                let contra = variance_map
                    .type_has_arg_in_contravariant_position(
                        TypeId::DeclId(d.decl_id),
                        type_parameter_len - 1 - v,
                    );
                let a: Type =
                    TypeUnit::Variable(TypeVariable::RecursiveIndex(v)).into();
                let a = if contra && co {
                    TypeUnit::Variance(types::Variance::Invariant, a).into()
                } else if contra {
                    TypeUnit::Variance(types::Variance::Contravariant, a).into()
                } else {
                    a
                };
                TypeUnit::Tuple(a, acc).into()
            },
        );
        let d = DataDecl {
            name: d.name,
            fields,
            decl_id: d.decl_id,
            type_parameter_len,
            constructed_type: TypeUnit::Tuple(
                TypeUnit::Const {
                    id: TypeId::DeclId(d.decl_id),
                }
                .into(),
                constructed_type,
            )
            .into(),
        };
        env.data_decls.insert(ConstructorId::DeclId(d.decl_id), d);
    }
    for i in &ast.interface_decl {
        env.token_map.insert(i.name.2, TokenMapEntry::Interface);
        let name = Path::from_str(module_path, i.name.0);
        env.imports.add_interface(name, i.is_public);
        let variables = i
            .variables
            .iter()
            .map(|(name, t)| {
                let self_ = TypeVariable::new();
                let t = type_to_type(
                    t,
                    module_path,
                    &std::iter::once((
                        Path::from_str(module_path, "Self"),
                        self_,
                    ))
                    .collect(),
                    SearchMode::Normal,
                    &mut Env {
                        interface_decls: &mut Default::default(),
                        token_map: env.token_map,
                        type_alias_map: env.type_alias_map,
                        imports: env.imports,
                        data_decl_map: env.data_decl_map,
                        data_decls: env.data_decls,
                    },
                    variance_map,
                )?;
                env.token_map.insert(
                    name.2,
                    TokenMapEntry::VariableDeclInInterface(t.clone()),
                );
                Ok((name.0, t, self_))
            })
            .try_collect()?;
        env.interface_decls.insert(name, variables);
        // interface_decls.push((name, variables));
    }
    for m in &ast.modules {
        collect_interface_decls(&m.ast, m.name, env, variance_map)?;
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
    data_decls: &'a mut FxHashMap<ConstructorId, DataDecl>,
}

fn collect_variable_decls<'a>(
    ast: ast_step1::Ast<'a>,
    module_path: ModulePath,
    variable_decls: &mut Vec<VariableDecl<'a>>,
    env: &mut Env<'_, '_>,
    variance_map: &mut VarianceMap,
) -> Result<(), CompileError> {
    for d in ast.variable_decl {
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
        } = variable_decl(
            d,
            module_path,
            env,
            &Default::default(),
            variance_map,
        )?;
        variable_decls.push(VariableDecl {
            value: catch_flat_map(WithFlatMapEnv {
                value,
                env: flat_map_env,
            })?,
            name,
            type_annotation,
            decl_id,
            span,
        })
    }
    for m in ast.modules {
        collect_variable_decls(
            m.ast,
            m.name,
            variable_decls,
            env,
            variance_map,
        )?;
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
            TypeId::FixedVariable(decl_id) => write!(f, "c{decl_id}"),
            id => {
                if let Some(n) = get_type_name(*id) {
                    write!(f, "{n}")
                } else {
                    write!(f, "{id:?}(name not available)")
                }
            }
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
    variance_map: &mut VarianceMap,
) -> Result<WithFlatMapEnv<'a, VariableDecl<'a>>, CompileError> {
    let expr =
        expr(v.value, module_path, type_variable_names, env, variance_map)?;
    let d = VariableDecl {
        type_annotation: v
            .type_annotation
            .map(|(t, span)| {
                let mut tr = &t;
                let mut implicit_type_parameters = Vec::new();
                while let ast_step1::Type::Forall {
                    parameter,
                    restriction: _,
                    body,
                } = &tr
                {
                    implicit_type_parameters
                        .push(Path::from_str(module_path, &parameter.0));
                    tr = body;
                }
                let t = type_to_type(
                    &t,
                    module_path,
                    type_variable_names,
                    SearchMode::Normal,
                    env,
                    variance_map,
                )?;
                let mut fixed_parameter_names = FxHashMap::default();
                let r = t.clone().remove_parameters();
                let mut fixed_t = r.fixed_type;
                let parameters = r.removed_parameters;
                let mut variable_requirements = r.variable_requirements;
                let mut subtype_relations = r.subtype_relations;
                for (p, name) in parameters
                    .into_iter()
                    .zip_eq(implicit_type_parameters.iter())
                {
                    let new_const = TypeUnit::Const {
                        id: TypeId::FixedVariable(DeclId::new()),
                    };
                    fixed_t = fixed_t.replace_num(p, &new_const.clone().into());
                    variable_requirements = variable_requirements
                        .into_iter()
                        .map(|(name, t)| {
                            (name, t.replace_num(p, &new_const.clone().into()))
                        })
                        .collect();
                    subtype_relations = subtype_relations
                        .into_iter()
                        .map(|(a, b)| {
                            (
                                a.replace_num(p, &new_const.clone().into()),
                                b.replace_num(p, &new_const.clone().into()),
                            )
                        })
                        .collect();
                    fixed_parameter_names.insert(new_const, *name);
                }
                if !subtype_relations.is_empty() {
                    fixed_t = TypeUnit::Restrictions {
                        t: fixed_t,
                        variable_requirements: Vec::new(),
                        subtype_relations,
                    }
                    .into()
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
    variance_map: &mut VarianceMap,
) -> Result<WithFlatMapEnv<'a>, CompileError> {
    use Expr::*;
    let span = e.1;
    let (flat_map_env, e) = match e.0 {
        ast_step1::Expr::Lambda(arms) => (
            Vec::new(),
            Lambda(
                arms.into_iter()
                    .map(move |arm| {
                        fn_arm(
                            arm,
                            module_path,
                            type_variable_names,
                            env,
                            variance_map,
                        )
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
            let data_decl = env.data_decls[&id].clone();
            let ConstructorId::DeclId(id) = id else {
                panic!()
            };
            let mut e: Expr<_> = Expr::ResolvedIdent {
                variable_id: VariableId::Constructor(id),
                type_: constructor_type(&data_decl)
                    .remove_parameters()
                    .fixed_type,
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
                    variance_map,
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
            let f =
                expr(*f, module_path, type_variable_names, env, variance_map)?;
            let mut a =
                expr(*a, module_path, type_variable_names, env, variance_map)?;
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
                    variance_map,
                )?;
            }
            new_es.reverse();
            return Ok(WithFlatMapEnv {
                value: (Do(new_es), TypeVariable::new(), span),
                env: Vec::new(),
            });
        }
        ast_step1::Expr::Question(e, question_span) => {
            let e =
                expr(*e, module_path, type_variable_names, env, variance_map)?;
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
        ast_step1::Expr::TypeAnnotation(e, t) => {
            let e =
                expr(*e, module_path, type_variable_names, env, variance_map)?;
            let t = type_to_type(
                &t,
                module_path,
                type_variable_names,
                SearchMode::Normal,
                env,
                variance_map,
            )?;
            (e.env, Expr::TypeAnnotation(Box::new(e.value), t))
        }
    };
    Ok(WithFlatMapEnv {
        value: (e, TypeVariable::new(), span),
        env: flat_map_env,
    })
}

pub fn constructor_type(d: &DataDecl) -> Type {
    let t = d
        .fields
        .iter()
        .rev()
        .fold(d.constructed_type.clone(), |t, f| {
            Type::arrow(f.type_.clone(), t)
        });
    (0..d.type_parameter_len).fold(t, |t, _| TypeUnit::TypeLevelFn(t).into())
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
    variance_map: &mut VarianceMap,
) -> Result<(Vec<ExprWithTypeAndSpan<'a, TypeVariable>>, Span), CompileError> {
    match e {
        (ast_step1::Expr::Decl(d), d_span) => {
            let d = variable_decl(
                *d,
                module_path,
                env,
                type_variable_names,
                variance_map,
            )?;
            if es.is_empty() {
                es = vec![(
                    Expr::Ident {
                        name: &UNIT_PATH,
                        ident_id: IdentId::new(),
                    },
                    TypeVariable::new(),
                    d_span.clone(),
                )];
            }
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
                            Box::new((l, TypeVariable::new(), d_span.clone())),
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
        e => {
            let e_span = e.1.clone();
            let e =
                expr(e, module_path, type_variable_names, env, variance_map)?;
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
    variance_map: &mut VarianceMap,
) -> Result<FnArm<'a, TypeVariable>, CompileError> {
    Ok(FnArm {
        pattern: arm
            .pattern
            .into_iter()
            .map(|(p, span)| {
                Ok((
                    pattern(
                        p,
                        span.clone(),
                        module_path,
                        type_variable_names,
                        env,
                        variance_map,
                    )?,
                    span,
                ))
            })
            .try_collect()?,
        expr: catch_flat_map(expr(
            arm.expr,
            module_path,
            type_variable_names,
            env,
            variance_map,
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
    span: Span,
    module_path: ModulePath,
    type_variable_names: &FxHashMap<Path, TypeVariable>,
    env: &mut Env<'_, '_>,
    variance_map: &mut VarianceMap,
) -> Result<Pattern<'a, TypeVariable>, CompileError> {
    use PatternUnit::*;
    Ok(match p {
        ast_step1::Pattern::Number(n) => I64(n).into(),
        ast_step1::Pattern::StrLiteral(s) => Str(s).into(),
        ast_step1::Pattern::Constructor { path, args } => {
            let (_, id) = env.imports.get_constructor(
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
                id,
                args: args
                    .into_iter()
                    .map(|(arg, span)| {
                        Ok((
                            pattern(
                                arg,
                                span.clone(),
                                module_path,
                                type_variable_names,
                                env,
                                variance_map,
                            )?,
                            span,
                        ))
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
        ast_step1::Pattern::TypeRestriction(p, t) => {
            let t = type_to_type(
                &t,
                module_path,
                &Default::default(),
                SearchMode::Normal,
                env,
                variance_map,
            )?;
            let p = pattern(
                *p,
                span,
                module_path,
                type_variable_names,
                env,
                variance_map,
            )?;
            TypeRestriction(p, t).into()
        }
        ast_step1::Pattern::Apply(pre_pattern, applications) => {
            let mut pre_pattern = pattern(
                *pre_pattern,
                span.clone(),
                module_path,
                type_variable_names,
                env,
                variance_map,
            )?;
            let mut functions;
            if pre_pattern.0.len() == 1 {
                match &mut pre_pattern.0[0] {
                    PatternUnit::Constructor {
                        id: ConstructorId::DeclId(constructor_id),
                        args,
                    } if args.is_empty() => {
                        let mut new_args =
                            vec![
                                None;
                                env.data_decls
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
                                    new_args[field] = Some((
                                        pattern(
                                            a.post_pattern.0,
                                            a.post_pattern.1.clone(),
                                            module_path,
                                            type_variable_names,
                                            env,
                                            variance_map,
                                        )?,
                                        a.post_pattern.1,
                                    ));
                                } else {
                                    functions.push(a);
                                }
                            } else {
                                functions.push(a);
                            }
                        }
                        args.extend(new_args.into_iter().map(move |a| {
                            a.unwrap_or_else(|| {
                                (
                                    Pattern(vec![PatternUnit::Underscore]),
                                    span.clone(),
                                )
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
                                    variance_map,
                                )?)?,
                                post_pattern: pattern(
                                    a.post_pattern.0,
                                    a.post_pattern.1,
                                    module_path,
                                    type_variable_names,
                                    env,
                                    variance_map,
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
    variance_map: &mut impl VarianceMapI,
) -> Result<Type, CompileError> {
    Ok(match t {
        ast_step1::Type::Ident(p) => {
            if p.path.len() == 1 && p.path.last().unwrap().0 == "|" {
                TypeUnit::TypeLevelFn(
                    TypeUnit::TypeLevelFn(
                        Type::from(TypeUnit::Variable(
                            TypeVariable::RecursiveIndex(0),
                        ))
                        .union_unit(
                            TypeUnit::Variable(TypeVariable::RecursiveIndex(1)),
                        ),
                    )
                    .into(),
                )
                .into()
            } else {
                let base_path = env.imports.get_module_with_path(
                    module_path,
                    if p.from_root {
                        Path::pkg_root()
                    } else {
                        module_path
                    },
                    &p.path[..p.path.len() - 1],
                    env.token_map,
                    &Default::default(),
                )?;
                let (name, span, token_id) = p.path.last().unwrap();
                let path = Path::from_str(base_path, name);
                if let Some(n) = type_variable_names.get(&path) {
                    env.token_map
                        .insert(*token_id, TokenMapEntry::TypeVariable);
                    Type::from(TypeUnit::Variable(*n))
                } else {
                    let const_or_alias = env.imports.get_type(
                        module_path,
                        base_path,
                        name,
                        span.clone(),
                        env.token_map,
                    )?;
                    match const_or_alias {
                        imports::ConstOrAlias::Const(id, parameter_len) => {
                            let mut tuple = Type::label_from_str("()");
                            for i in 0..parameter_len {
                                let co = variance_map
                                    .type_has_arg_in_covariant_position(
                                        id,
                                        parameter_len - 1 - i,
                                    );
                                let contra = variance_map
                                    .type_has_arg_in_contravariant_position(
                                        id,
                                        parameter_len - 1 - i,
                                    );
                                let a: Type = TypeUnit::Variable(
                                    TypeVariable::RecursiveIndex(i),
                                )
                                .into();
                                let a = if contra && co {
                                    TypeUnit::Variance(
                                        types::Variance::Invariant,
                                        a,
                                    )
                                    .into()
                                } else if contra {
                                    TypeUnit::Variance(
                                        types::Variance::Contravariant,
                                        a,
                                    )
                                    .into()
                                } else {
                                    a
                                };
                                tuple = TypeUnit::Tuple(a, tuple).into();
                            }
                            env.token_map.insert(
                                p.path.last().unwrap().2,
                                TokenMapEntry::TypeId(id),
                            );
                            let t = TypeUnit::Tuple(
                                TypeUnit::Const { id }.into(),
                                tuple,
                            )
                            .into();
                            (0..parameter_len).fold(t, |acc, _| {
                                TypeUnit::TypeLevelFn(acc).into()
                            })
                        }
                        imports::ConstOrAlias::Alias(name) => env
                            .get_type_from_alias(
                                (name, *token_id),
                                type_variable_names,
                                if search_type == SearchMode::Normal {
                                    SearchMode::Alias
                                } else {
                                    SearchMode::AliasSub
                                },
                                variance_map,
                            )?
                            .unwrap(),
                    }
                }
            }
        }
        ast_step1::Type::Apply { f, a } => {
            let f = type_to_type(
                f,
                module_path,
                type_variable_names,
                search_type,
                env,
                variance_map,
            )?;
            let a = type_to_type(
                a,
                module_path,
                type_variable_names,
                search_type,
                env,
                variance_map,
            )?;
            f.type_level_function_apply(a)
        }
        ast_step1::Type::Forall {
            parameter,
            restriction,
            body,
        } => {
            env.token_map
                .insert(parameter.2, TokenMapEntry::TypeVariable);
            let v = TypeVariable::new();
            let mut variable_requirements = Vec::new();
            for path in restriction.iter() {
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
                // TODO: assert!(env.interface_decls.contains_key(&name));
                for (name, t, self_) in
                    env.interface_decls.get(&name).iter().flat_map(|v| v.iter())
                {
                    variable_requirements.push((
                        name.to_string(),
                        t.clone()
                            .replace_num(*self_, &TypeUnit::Variable(v).into()),
                    ))
                }
            }
            let mut type_variable_names = type_variable_names.clone();
            type_variable_names
                .insert(Path::from_str(module_path, &parameter.0), v);
            let body = type_to_type(
                body,
                module_path,
                &type_variable_names,
                search_type,
                env,
                variance_map,
            )?;
            let body = if variable_requirements.is_empty() {
                body
            } else {
                TypeUnit::Restrictions {
                    t: body,
                    variable_requirements,
                    subtype_relations: Default::default(),
                }
                .into()
            };
            TypeUnit::TypeLevelFn(body.replace_num(
                v,
                &TypeUnit::Variable(TypeVariable::RecursiveIndex(0)).into(),
            ))
            .into()
        }
        ast_step1::Type::Fn { parameter, body } => {
            let mut type_variable_names = type_variable_names.clone();
            let v = TypeVariable::new();
            type_variable_names
                .insert(Path::from_str(module_path, &parameter.0), v);
            let body = type_to_type(
                body,
                module_path,
                &type_variable_names,
                search_type,
                env,
                variance_map,
            )?;
            TypeUnit::TypeLevelFn(body.replace_num(
                v,
                &TypeUnit::Variable(TypeVariable::RecursiveIndex(0)).into(),
            ))
            .into()
        }
    })
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
                t.all_type_variables_iter().collect()
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
            _ => panic!("{tuple} is not a tuple or unit"),
        })
        .collect()
}

impl Display for PatternRestriction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} = pat[{}] ({:?}){}",
            self.type_,
            self.pattern
                .iter()
                .map(|(p, _)| format!("({p})"))
                .join(" | "),
            self.span,
            if self.allow_inexhaustive {
                format_args!(" (inexhaustive allowed)")
            } else {
                format_args!("")
            }
        )
    }
}

impl From<ConstructorId> for VariableId {
    fn from(value: ConstructorId) -> Self {
        match value {
            ConstructorId::DeclId(d) => VariableId::Constructor(d),
            ConstructorId::Intrinsic(d) => VariableId::IntrinsicConstructor(d),
        }
    }
}
