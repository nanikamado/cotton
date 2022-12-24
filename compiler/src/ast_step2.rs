pub mod decl_id;
pub mod ident_id;
pub mod imports;
pub mod name_id;
pub mod types;

use self::imports::Imports;
use self::name_id::Name;
use self::types::{TypeMatchable, TypeVariable};
use self::{
    decl_id::DeclId,
    ident_id::IdentId,
    types::{Type, TypeUnit},
};
use crate::ast_step1::{merge_span, OpPrecedenceMap};
use crate::ast_step3::{GlobalVariableType, VariableRequirement};
use crate::intrinsics::IntrinsicVariable;
use crate::{
    ast_step1,
    intrinsics::{
        IntrinsicConstructor, IntrinsicType, INTRINSIC_CONSTRUCTORS,
        INTRINSIC_TYPES,
    },
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use once_cell::sync::Lazy;
use parser::token_id::TokenId;
use parser::Span;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;
use strum::IntoEnumIterator;
use tracing_mutex::stdsync::TracingRwLock as RwLock;
pub use types::TypeConstructor;

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

pub struct PrintTypeOfGlobalVariableForUser<'a> {
    pub t: &'a GlobalVariableType,
    pub op_precedence_map: &'a OpPrecedenceMap<'a>,
}

pub struct PrintTypeOfLocalVariableForUser<'a> {
    pub t: &'a Type,
    pub op_precedence_map: &'a OpPrecedenceMap<'a>,
    pub type_variable_decls: &'a FxHashMap<TypeUnit, Name>,
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
    pub implicit_parameters: Vec<(Name, Type, DeclId)>,
    pub fixed_parameter_names: FxHashMap<TypeUnit, Name>,
    pub span: Span,
}

pub type ExprWithTypeAndSpan<T> = (Expr<T>, T, Span);

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<T> {
    Lambda(Vec<FnArm<T>>),
    Number(Name),
    StrLiteral(Name),
    Ident { name: Name, ident_id: IdentId },
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
    Binder(Name, DeclId, T),
    Underscore,
    TypeRestriction(Pattern<T>, Type),
}

#[derive(Debug, PartialEq, Eq)]
pub enum TokenMapEntry {
    Decl(DeclId),
    DataDecl(DeclId),
    Ident(IdentId),
    TypeId(TypeId),
    TypeAlias,
    Constructor(ConstructorId),
    TypeVariable,
    Interface,
    VariableDeclInInterface(Type),
}

enum FlatMapEnv {
    FlatMap {
        variable_name: Name,
        pre_calc: ExprWithTypeAndSpan<TypeVariable>,
        question_span: Span,
    },
    Decl(Name, ExprWithTypeAndSpan<TypeVariable>),
}

struct WithFlatMapEnv<Value = ExprWithTypeAndSpan<TypeVariable>> {
    value: Value,
    env: Vec<FlatMapEnv>,
}

#[derive(Default, Debug, PartialEq, Eq)]
pub struct TokenMap(pub FxHashMap<TokenId, TokenMapEntry>);

impl TokenMap {
    fn insert(&mut self, id: Option<TokenId>, entry: TokenMapEntry) {
        if let Some(id) = id {
            self.0.insert(id, entry);
        }
    }
}

static TYPE_NAMES: Lazy<RwLock<FxHashMap<TypeId, Name>>> = Lazy::new(|| {
    RwLock::new(
        INTRINSIC_TYPES
            .iter()
            .map(|(name, id)| {
                (TypeId::Intrinsic(*id), Name::from_str_type(name))
            })
            .collect(),
    )
});

pub fn get_type_name(type_id: TypeId) -> Name {
    *TYPE_NAMES.read().unwrap().get(&type_id).unwrap()
}

impl Ast {
    pub fn from(ast: ast_step1::Ast) -> (Self, TokenMap) {
        let module_path = Name::root_module();
        let mut token_map = TokenMap::default();
        let mut data_decls = Vec::new();
        let mut type_alias_map = TypeAliasMap::default();
        let mut variable_decls = Vec::new();
        let mut interface_decls = Default::default();
        let mut imports = Imports::default();
        collect_data_and_type_alias_decls(
            &ast,
            module_path,
            &mut token_map,
            &mut data_decls,
            &mut type_alias_map,
            &mut imports,
        );
        let data_decl_map =
            data_decls.iter().map(|d| (d.name, d.decl_id)).collect();
        {
            TYPE_NAMES.write().unwrap().extend(
                data_decls
                    .iter()
                    .map(|d| (TypeId::DeclId(d.decl_id), d.name)),
            );
        }
        collect_interface_decls(
            &ast,
            module_path,
            &mut token_map,
            &mut type_alias_map,
            &mut interface_decls,
            &data_decl_map,
        );
        collect_decls(
            ast,
            module_path,
            &mut variable_decls,
            &mut Env {
                token_map: &mut token_map,
                type_alias_map: &mut type_alias_map,
                interface_decls: &mut interface_decls,
                imports: &mut imports,
                data_decl_map: &data_decl_map,
            },
        );
        let entry_point = variable_decls
            .iter()
            .find(|d| d.name == Name::from_str(module_path, "main"))
            .unwrap_or_else(|| panic!("entry point not found"))
            .decl_id;
        (
            Self {
                variable_decl: variable_decls,
                data_decl: data_decls,
                imports,
                entry_point,
            },
            token_map,
        )
    }
}

fn collect_data_and_type_alias_decls<'a>(
    ast: &ast_step1::Ast<'a>,
    module_path: ModulePath,
    token_map: &mut TokenMap,
    data_decls: &mut Vec<DataDecl>,
    type_alias_map: &mut TypeAliasMap<'a>,
    imports: &mut Imports,
) {
    data_decls.extend(ast.data_decl.iter().map(|d| {
        let decl_id = DeclId::new();
        let mut type_variables = FxHashMap::default();
        token_map.insert(d.name.1, TokenMapEntry::DataDecl(decl_id));
        for ((name, id), interfaces) in &d.type_variables.type_variables {
            token_map.insert(*id, TokenMapEntry::TypeVariable);
            type_variables.insert(*name, TypeVariable::new());
            for (_, id) in interfaces {
                token_map.insert(*id, TokenMapEntry::Interface);
            }
        }
        DataDecl {
            name: Name::from_str(module_path, d.name.0),
            fields: d
                .fields
                .iter()
                .map(|f| {
                    token_map.insert(f.1, TokenMapEntry::TypeVariable);
                    type_variables[f.0]
                })
                .collect(),
            decl_id,
            type_variable_decls: type_variables
                .into_iter()
                .map(|(n, v)| (v, Name::from_str(module_path, n)))
                .collect(),
        }
    }));
    type_alias_map.0.extend(ast.type_alias_decl.iter().map(|a| {
        token_map.insert(a.name.1, TokenMapEntry::TypeAlias);
        (
            Name::from_str(module_path, a.name.0),
            (a.body.clone(), AliasComputation::NotUnaliased),
        )
    }));
    for v in IntrinsicVariable::iter() {
        let a = Name::from_str(module_path, v.to_str());
        let b = Name::from_str_intrinsic(v.to_str());
        imports.insert(a, b);
    }
    for v in IntrinsicConstructor::iter() {
        imports.insert(
            Name::from_str(module_path, v.to_str()),
            Name::from_str_intrinsic(v.to_str()),
        );
    }
    for ((name, _), m) in &ast.modules {
        collect_data_and_type_alias_decls(
            m,
            Name::from_str(module_path, name),
            token_map,
            data_decls,
            type_alias_map,
            imports,
        )
    }
}

fn collect_interface_decls(
    ast: &ast_step1::Ast,
    module_path: ModulePath,
    token_map: &mut TokenMap,
    type_alias_map: &mut TypeAliasMap,
    interface_decls: &mut FxHashMap<Name, Vec<(Name, Type, TypeVariable)>>,
    data_decl_map: &FxHashMap<Name, DeclId>,
) {
    interface_decls.extend(ast.interface_decl.iter().map(|i| {
        token_map.insert(i.name.1, TokenMapEntry::Interface);
        (
            Name::from_str(module_path, i.name.0),
            i.variables
                .iter()
                .map(|(name, t, forall)| {
                    let self_ = TypeVariable::new();
                    let t = type_to_type_with_forall(
                        t.clone(),
                        data_decl_map,
                        std::iter::once((
                            Name::from_str(module_path, "Self"),
                            self_,
                        ))
                        .collect(),
                        type_alias_map,
                        forall.clone(),
                        &Default::default(),
                        token_map,
                    );
                    token_map.insert(
                        name.1,
                        TokenMapEntry::VariableDeclInInterface(t.clone()),
                    );
                    (Name::from_str(module_path, name.0), t, self_)
                })
                .collect(),
        )
    }));
    for (_, m) in &ast.modules {
        collect_interface_decls(
            m,
            module_path,
            token_map,
            type_alias_map,
            interface_decls,
            data_decl_map,
        );
    }
}

struct Env<'a> {
    token_map: &'a mut TokenMap,
    type_alias_map: &'a mut TypeAliasMap<'a>,
    interface_decls: &'a mut FxHashMap<Name, Vec<(Name, Type, TypeVariable)>>,
    imports: &'a mut Imports,
    data_decl_map: &'a FxHashMap<Name, DeclId>,
}

fn collect_decls(
    ast: ast_step1::Ast,
    module_path: ModulePath,
    variable_decls: &mut Vec<VariableDecl>,
    env: &mut Env<'_>,
) {
    variable_decls.extend(ast.variable_decl.into_iter().map(|d| {
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
        } = variable_decl(d, module_path, env, &Default::default());
        VariableDecl {
            value: catch_flat_map(
                WithFlatMapEnv {
                    value,
                    env: flat_map_env,
                },
                module_path,
            ),
            name,
            type_annotation,
            decl_id,
            span,
        }
    }));
    for ((name, _), m) in ast.modules {
        collect_decls(
            m,
            Name::from_str(module_path, name),
            variable_decls,
            env,
        );
    }
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
    env: &mut Env<'_>,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
) -> WithFlatMapEnv<VariableDecl> {
    let decl_id = DeclId::new();
    env.token_map.insert(v.name.1, TokenMapEntry::Decl(decl_id));
    let expr = expr(v.value, module_path, type_variable_names, env);
    let d = VariableDecl {
        name: Name::from_str(module_path, v.name.0),
        type_annotation: v.type_annotation.map(|(t, forall, span)| {
            let implicit_type_parameters: Vec<_> = forall
                .type_variables
                .iter()
                .map(|(name, _)| Name::from_str(module_path, name.0))
                .collect();
            let t = type_to_type_with_forall(
                t,
                env.data_decl_map,
                type_variable_names.clone(),
                env.type_alias_map,
                forall,
                env.interface_decls,
                env.token_map,
            );
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
            Annotation {
                unfixed: t,
                fixed: fixed_t,
                implicit_parameters: variable_requirements
                    .into_iter()
                    .map(|(name, t)| (name, t, DeclId::new()))
                    .collect(),
                fixed_parameter_names,
                span,
            }
        }),
        value: expr.value,
        decl_id,
        span: v.span,
    };
    WithFlatMapEnv {
        value: d,
        env: expr.env,
    }
}

fn catch_flat_map(
    e: WithFlatMapEnv,
    module_path: ModulePath,
) -> ExprWithTypeAndSpan<TypeVariable> {
    let mut expr = e.value;
    for env in e.env.into_iter().rev() {
        match env {
            FlatMapEnv::FlatMap {
                variable_name,
                pre_calc,
                question_span,
            } => {
                let continuation = Expr::Lambda(vec![FnArm {
                    pattern: vec![(
                        vec![PatternUnit::Binder(
                            variable_name,
                            DeclId::new(),
                            TypeVariable::new(),
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
                                        name: Name::from_str(
                                            module_path,
                                            "flat_map",
                                        ),
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
                        PatternUnit::Binder(name, DeclId::new(), e.1).into(),
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
    expr
}

fn expr(
    e: ast_step1::ExprWithSpan,
    module_path: ModulePath,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    env: &mut Env<'_>,
) -> WithFlatMapEnv {
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
                    .collect(),
            ),
        ),
        ast_step1::Expr::Number(n) => {
            (Vec::new(), Number(Name::from_str(module_path, n)))
        }
        ast_step1::Expr::StrLiteral(s) => {
            (Vec::new(), StrLiteral(Name::from_str(module_path, s)))
        }
        ast_step1::Expr::Ident { name, path } => {
            let mut module_path = module_path;
            for (p, _) in path {
                let m = env
                    .imports
                    .get_all_candidates(Name::from_str(module_path, p))
                    .collect_vec();
                debug_assert_eq!(m.len(), 1);
                module_path = m[0];
            }
            let ident_id = IdentId::new();
            env.token_map.insert(name.1, TokenMapEntry::Ident(ident_id));
            (
                Vec::new(),
                Ident {
                    name: Name::from_str(module_path, name.0),
                    ident_id,
                },
            )
        }
        ast_step1::Expr::Decl(_) => {
            panic!()
        }
        ast_step1::Expr::Call(f, a) => {
            let f = expr(*f, module_path, type_variable_names, env);
            let mut a = expr(*a, module_path, type_variable_names, env);
            if f.env.is_empty() {
                (a.env, Call(Box::new(f.value), Box::new(a.value)))
            } else {
                let name = Name::get_unique();
                let mut env = f.env;
                let f_span = f.value.2.clone();
                let f_type = f.value.1;
                env.push(FlatMapEnv::Decl(name, f.value));
                env.append(&mut a.env);
                (
                    env,
                    Call(
                        Box::new((
                            Expr::Ident {
                                name,
                                ident_id: IdentId::new(),
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
                );
            }
            new_es.reverse();
            return WithFlatMapEnv {
                value: (Do(new_es), TypeVariable::new(), span),
                env: Vec::new(),
            };
        }
        ast_step1::Expr::Question(e, question_span) => {
            let e = expr(*e, module_path, type_variable_names, env);
            let mut env = e.env;
            let name = Name::get_unique();
            env.push(FlatMapEnv::FlatMap {
                variable_name: name,
                pre_calc: e.value,
                question_span,
            });
            (
                env,
                Expr::Ident {
                    name,
                    ident_id: IdentId::new(),
                },
            )
        }
        ast_step1::Expr::TypeAnnotation(e, t, forall) => {
            let e = expr(*e, module_path, type_variable_names, env);
            let t = type_to_type_with_forall(
                t,
                env.data_decl_map,
                type_variable_names.clone(),
                env.type_alias_map,
                forall,
                env.interface_decls,
                env.token_map,
            );
            (e.env, Expr::TypeAnnotation(Box::new(e.value), t))
        }
    };
    WithFlatMapEnv {
        value: (e, TypeVariable::new(), span),
        env: flat_map_env,
    }
}

fn add_expr_in_do(
    e: ast_step1::ExprWithSpan,
    module_path: ModulePath,
    mut es: Vec<ExprWithTypeAndSpan<TypeVariable>>,
    es_span: Span,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    env: &mut Env<'_>,
) -> (Vec<ExprWithTypeAndSpan<TypeVariable>>, Span) {
    match e {
        (ast_step1::Expr::Decl(d), d_span) => {
            let d = variable_decl(*d, module_path, env, type_variable_names);
            if es.is_empty() {
                (
                    vec![
                        (
                            Expr::Ident {
                                name: Name::from_str_intrinsic("()"),
                                ident_id: IdentId::new(),
                            },
                            TypeVariable::new(),
                            d_span.clone(),
                        ),
                        catch_flat_map(
                            WithFlatMapEnv {
                                value: d.value.value,
                                env: d.env,
                            },
                            module_path,
                        ),
                    ],
                    d_span,
                )
            } else {
                es.reverse();
                let l = Expr::Lambda(vec![FnArm {
                    pattern: vec![(
                        PatternUnit::Binder(
                            d.value.name,
                            d.value.decl_id,
                            TypeVariable::new(),
                        )
                        .into(),
                        d.value.span,
                    )],
                    expr: (Expr::Do(es), TypeVariable::new(), es_span.clone()),
                }]);
                (
                    vec![catch_flat_map(
                        WithFlatMapEnv {
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
                        },
                        module_path,
                    )],
                    merge_span(&es_span, &d_span),
                )
            }
        }
        e => {
            let e_span = e.1.clone();
            let e = expr(e, module_path, type_variable_names, env);
            es.push(e.value);
            let span = merge_span(&es_span, &e_span);
            if e.env.is_empty() {
                (es, span)
            } else {
                es.reverse();
                (
                    vec![catch_flat_map(
                        WithFlatMapEnv {
                            value: (Expr::Do(es), TypeVariable::new(), es_span),
                            env: e.env,
                        },
                        module_path,
                    )],
                    span,
                )
            }
        }
    }
}

fn fn_arm(
    arm: ast_step1::FnArm,
    module_path: ModulePath,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    env: &mut Env<'_>,
) -> FnArm<TypeVariable> {
    FnArm {
        pattern: arm
            .pattern
            .into_iter()
            .map(|(p, span)| (pattern(p, module_path, env), span))
            .collect(),
        expr: catch_flat_map(
            expr(arm.expr, module_path, type_variable_names, env),
            module_path,
        ),
    }
}

impl TypeId {
    fn get(name: Name, data_decl_map: &FxHashMap<Name, DeclId>) -> TypeId {
        if let Some(id) = data_decl_map.get(&name) {
            TypeId::DeclId(*id)
        } else if let Some(i) = INTRINSIC_TYPES.get(&name.to_string().as_str())
        {
            TypeId::Intrinsic(*i)
        } else {
            panic!("{:?} not fould", name)
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
            panic!("{:?} not fould", name)
        }
    }
}

fn pattern(
    p: ast_step1::Pattern,
    module_path: ModulePath,
    env: &mut Env<'_>,
) -> Pattern<TypeVariable> {
    use PatternUnit::*;
    match p {
        ast_step1::Pattern::Number(n) => I64(n.parse().unwrap()),
        ast_step1::Pattern::StrLiteral(s) => Str(s.to_string()),
        ast_step1::Pattern::Constructor { name, args } => {
            let id = ConstructorId::get(
                Name::from_str_type(name.0),
                env.data_decl_map,
            );
            env.token_map.insert(name.1, TokenMapEntry::Constructor(id));
            Constructor {
                name: Name::from_str_type(name.0),
                id,
                args: args
                    .into_iter()
                    .map(|arg| pattern(arg, module_path, env))
                    .collect(),
            }
        }
        ast_step1::Pattern::Binder(name) => {
            let decl_id = DeclId::new();
            env.token_map.insert(name.1, TokenMapEntry::Decl(decl_id));
            Binder(
                Name::from_str(module_path, name.0),
                decl_id,
                TypeVariable::new(),
            )
        }
        ast_step1::Pattern::Underscore => Underscore,
        ast_step1::Pattern::TypeRestriction(p, t, forall) => {
            let t = type_to_type_with_forall(
                t,
                env.data_decl_map,
                Default::default(),
                env.type_alias_map,
                forall,
                env.interface_decls,
                env.token_map,
            );
            let p = pattern(*p, module_path, env);
            TypeRestriction(p, t)
        }
    }
    .into()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchMode {
    Normal,
    Alias,
    AliasSub,
}

pub fn type_to_type(
    t: &ast_step1::Type,
    data_decl_map: &FxHashMap<Name, DeclId>,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    type_alias_map: &mut TypeAliasMap,
    search_type: SearchMode,
    token_map: &mut TokenMap,
) -> Type {
    match t.name.0 {
        "|" => t
            .args
            .iter()
            .flat_map(|a| {
                type_to_type(
                    a,
                    data_decl_map,
                    type_variable_names,
                    type_alias_map,
                    search_type,
                    token_map,
                )
            })
            .collect(),
        "->" => TypeUnit::Fn(
            type_to_type(
                &t.args[0],
                data_decl_map,
                type_variable_names,
                type_alias_map,
                search_type,
                token_map,
            ),
            type_to_type(
                &t.args[1],
                data_decl_map,
                type_variable_names,
                type_alias_map,
                search_type,
                token_map,
            ),
        )
        .into(),
        _ => {
            if let Some(n) =
                type_variable_names.get(&Name::from_str_type(t.name.0))
            {
                token_map.insert(t.name.1, TokenMapEntry::TypeVariable);
                let mut new_t = Type::from(TypeUnit::Variable(*n));
                for a in &t.args {
                    new_t = new_t.type_level_function_apply(type_to_type(
                        a,
                        data_decl_map,
                        type_variable_names,
                        type_alias_map,
                        search_type,
                        token_map,
                    ));
                }
                new_t
            } else if let Some(mut unaliased) = type_alias_map.get(
                (Name::from_str_type(t.name.0), t.name.1),
                data_decl_map,
                type_variable_names,
                if search_type == SearchMode::Normal {
                    SearchMode::Alias
                } else {
                    SearchMode::AliasSub
                },
                token_map,
            ) {
                for a in &t.args {
                    unaliased =
                        unaliased.type_level_function_apply(type_to_type(
                            a,
                            data_decl_map,
                            type_variable_names,
                            type_alias_map,
                            search_type,
                            token_map,
                        ));
                }
                unaliased
            } else {
                let mut tuple = Type::label_from_str("()");
                for a in t
                    .args
                    .iter()
                    .map(|a| {
                        type_to_type(
                            a,
                            data_decl_map,
                            type_variable_names,
                            type_alias_map,
                            search_type,
                            token_map,
                        )
                    })
                    .rev()
                {
                    tuple = TypeUnit::Tuple(a, tuple).into();
                }
                let id =
                    TypeId::get(Name::from_str_type(t.name.0), data_decl_map);
                token_map.insert(t.name.1, TokenMapEntry::TypeId(id));
                TypeUnit::Tuple(TypeUnit::Const { id }.into(), tuple).into()
            }
        }
    }
}

fn type_to_type_with_forall(
    t: ast_step1::Type,
    data_decl_map: &FxHashMap<Name, DeclId>,
    mut type_variable_names: FxHashMap<Name, TypeVariable>,
    type_alias_map: &mut TypeAliasMap,
    forall: ast_step1::Forall,
    interfaces: &FxHashMap<Name, Vec<(Name, Type, TypeVariable)>>,
    token_map: &mut TokenMap,
) -> Type {
    let mut variable_requirements = Vec::new();
    let mut type_parameters = Vec::new();
    for (s, interface_names) in forall.type_variables {
        token_map.insert(s.1, TokenMapEntry::TypeVariable);
        let v = TypeVariable::new();
        for name in interface_names {
            token_map.insert(name.1, TokenMapEntry::Interface);
            for (name, t, self_) in &interfaces[&Name::from_str_type(name.0)] {
                variable_requirements.push((
                    *name,
                    t.clone()
                        .replace_num(*self_, &TypeUnit::Variable(v).into()),
                ))
            }
        }
        type_parameters.push(v);
        type_variable_names.insert(Name::from_str_type(s.0), v);
    }
    let mut t = type_to_type(
        &t,
        data_decl_map,
        &type_variable_names,
        type_alias_map,
        SearchMode::Normal,
        token_map,
    );
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
    t
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
enum AliasComputation {
    Unaliased(Type),
    NotUnaliased,
}

#[derive(Debug, Clone, Default)]
pub struct TypeAliasMap<'a>(
    FxHashMap<
        Name,
        (
            (ast_step1::Type<'a>, ast_step1::Forall<'a>),
            AliasComputation,
        ),
    >,
);

#[derive(Debug, Clone)]
struct Forall(Vec<TypeVariable>);

impl<'a> TypeAliasMap<'a> {
    fn get(
        &mut self,
        name: (Name, Option<TokenId>),
        data_decl_map: &FxHashMap<Name, DeclId>,
        type_variable_names: &FxHashMap<Name, TypeVariable>,
        search_type: SearchMode,
        token_map: &mut TokenMap,
    ) -> Option<Type> {
        debug_assert_ne!(search_type, SearchMode::Normal);
        if let Some(t) = type_variable_names.get(&name.0) {
            token_map.insert(name.1, TokenMapEntry::TypeAlias);
            return Some(TypeUnit::Variable(*t).into());
        }
        let alias = self.0.get(&name.0)?;
        Some(match (alias, search_type) {
            ((_, AliasComputation::Unaliased(t)), SearchMode::Alias) => {
                token_map.insert(name.1, TokenMapEntry::TypeAlias);
                t.clone()
            }
            ((t, _), _) => {
                let mut type_variable_names: FxHashMap<Name, TypeVariable> =
                    type_variable_names
                        .clone()
                        .into_iter()
                        .map(|(s, v)| {
                            (
                                s,
                                v.increment_recursive_index(
                                    1 + t.1.type_variables.len() as i32,
                                ),
                            )
                        })
                        .collect();
                type_variable_names.insert(
                    name.0,
                    TypeVariable::RecursiveIndex(t.1.type_variables.len()),
                );
                let forall = t
                    .1
                    .clone()
                    .type_variables
                    .into_iter()
                    .map(|(s, interfaces)| {
                        let v = TypeVariable::new();
                        token_map.insert(s.1, TokenMapEntry::TypeVariable);
                        for (_, id) in interfaces {
                            token_map.insert(id, TokenMapEntry::Interface);
                        }
                        type_variable_names.insert(Name::from_str_type(s.0), v);
                        v
                    })
                    .collect_vec();
                let mut t = type_to_type(
                    &t.0.clone(),
                    data_decl_map,
                    &type_variable_names,
                    self,
                    search_type,
                    token_map,
                );
                token_map.insert(name.1, TokenMapEntry::TypeAlias);
                for v in forall.into_iter().rev() {
                    t = TypeUnit::TypeLevelFn(
                        t.replace_num(
                            v,
                            &TypeUnit::Variable(TypeVariable::RecursiveIndex(
                                0,
                            ))
                            .into(),
                        ),
                    )
                    .into();
                }
                let t = if t.contains_variable(TypeVariable::RecursiveIndex(0))
                {
                    TypeUnit::RecursiveAlias { body: t }.into()
                } else {
                    t.increment_recursive_index(0, -1)
                };
                if search_type == SearchMode::Alias {
                    self.0.get_mut(&name.0).unwrap().1 =
                        AliasComputation::Unaliased(t.clone());
                }
                t
            }
        })
    }
}

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

    // pub fn remove(&mut self, value: &(Type, Type)) -> bool {
    //     self.0.remove(value)
    // }

    // pub fn contains(&self, value: &(Type, Type)) -> bool {
    //     self.0.contains(value)
    // }

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

impl Display for PrintTypeOfGlobalVariableForUser<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            fmt_type_with_env(
                &self.t.t,
                self.op_precedence_map,
                &Default::default()
            )
            .0
        )?;
        Ok(())
    }
}

impl Display for PrintTypeOfLocalVariableForUser<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            fmt_type_with_env(
                self.t,
                self.op_precedence_map,
                self.type_variable_decls
            )
            .0
        )?;
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq)]
enum OperatorContext {
    Single,
    Fn,
    Or,
    OtherOperator,
}

fn fmt_type_with_env(
    t: &Type,
    op_precedence_map: &OpPrecedenceMap,
    type_variable_decls: &FxHashMap<TypeUnit, Name>,
) -> (String, OperatorContext) {
    if t.is_empty() {
        ("∅".to_string(), OperatorContext::Single)
    } else if t.len() == 1 {
        fmt_type_unit_with_env(
            t.iter().next().unwrap(),
            op_precedence_map,
            type_variable_decls,
        )
    } else {
        (
            t.iter()
                .format_with(" | ", |t, f| {
                    let (t, t_context) = fmt_type_unit_with_env(
                        t,
                        op_precedence_map,
                        type_variable_decls,
                    );
                    let s = match t_context {
                        OperatorContext::Single | OperatorContext::Or => t,
                        _ => format!("({})", t),
                    };
                    f(&s)
                })
                .to_string(),
            OperatorContext::Or,
        )
    }
}

fn fmt_type_unit_with_env(
    t: &TypeUnit,
    op_precedence_map: &OpPrecedenceMap,
    type_variable_decls: &FxHashMap<TypeUnit, Name>,
) -> (String, OperatorContext) {
    use OperatorContext::*;
    if let Some(s) = type_variable_decls.get(t) {
        return (s.to_string(), Single);
    }
    match t {
        TypeUnit::Fn(a, b) => {
            let (b, b_context) =
                fmt_type_with_env(b, op_precedence_map, type_variable_decls);
            let (a, a_context) =
                fmt_type_with_env(a, op_precedence_map, type_variable_decls);
            let s = match (a_context, b_context) {
                (Single, Single | Fn) => format!("{} -> {}", a, b),
                (Single, _) => format!("{} -> ({})", a, b),
                (_, Single | Fn) => format!("({}) -> {}", a, b),
                _ => format!("({}) -> ({})", a, b),
            };
            (s, Fn)
        }
        TypeUnit::Variable(TypeVariable::Normal(_)) => {
            ("_".to_string(), Single)
        }
        TypeUnit::Variable(d) => (d.to_string(), Single),
        TypeUnit::RecursiveAlias { body } => (
            format!(
                "rec[{}]",
                fmt_type_with_env(body, op_precedence_map, type_variable_decls)
                    .0
            ),
            Single,
        ),
        TypeUnit::Const { id } => (format!(":{}", id), Single),
        TypeUnit::Tuple(hs, ts) => {
            let ts = collect_tuple_rev(ts);
            let hts = hs
                .iter()
                .flat_map(|h| ts.iter().map(move |t| (h, t)))
                .collect_vec();
            if hts.len() == 1 {
                let (h, tuple_rev) = hts[0];
                if let TypeUnit::Const { id } = &**h {
                    fmt_tuple(
                        *id,
                        tuple_rev,
                        op_precedence_map,
                        type_variable_decls,
                    )
                } else {
                    (
                        fmt_tuple_as_tuple(
                            h,
                            tuple_rev,
                            op_precedence_map,
                            type_variable_decls,
                        ),
                        OperatorContext::Single,
                    )
                }
            } else {
                let t = format!(
                    "{}",
                    hts.iter().format_with(" | ", |(h, t), f| {
                        if let TypeUnit::Const { id } = &***h {
                            let (t, t_context) = fmt_tuple(
                                *id,
                                t,
                                op_precedence_map,
                                type_variable_decls,
                            );
                            match t_context {
                                Single | Or => f(&t),
                                _ => f(&format_args!("({})", t)),
                            }
                        } else {
                            f(&fmt_tuple_as_tuple(
                                h,
                                t,
                                op_precedence_map,
                                type_variable_decls,
                            ))
                        }
                    })
                );
                (t, Or)
            }
        }
        TypeUnit::TypeLevelFn(f) => (
            format!(
                "fn[{}]",
                fmt_type_with_env(f, op_precedence_map, type_variable_decls).0
            ),
            Single,
        ),
        TypeUnit::TypeLevelApply { f, a } => {
            let (f, f_context) =
                fmt_type_with_env(f, op_precedence_map, type_variable_decls);
            let (a, _) =
                fmt_type_with_env(a, op_precedence_map, type_variable_decls);
            let s = if f_context == Single {
                format!("{}[{}]", f, a)
            } else {
                format!("({})[{}]", f, a)
            };
            (s, Single)
        }
        TypeUnit::Restrictions {
            t,
            variable_requirements,
            subtype_relations,
        } => (
            format!(
                "{} where {{{subtype_relations}, {}}}",
                t,
                variable_requirements.iter().format_with(
                    ",\n",
                    |(name, t), f| f(&format_args!("?{} : {}", name, t))
                )
            ),
            OtherOperator,
        ),
    }
}

fn fmt_tuple(
    head: TypeId,
    tuple_rev: &[&Type],
    op_precedence_map: &OpPrecedenceMap,
    type_variable_decls: &FxHashMap<TypeUnit, Name>,
) -> (String, OperatorContext) {
    use OperatorContext::*;
    if tuple_rev.is_empty() {
        (head.to_string(), Single)
    } else if tuple_rev.len() == 1 {
        (
            format!(
                "{}[{}]",
                head,
                fmt_type_with_env(
                    tuple_rev[0],
                    op_precedence_map,
                    type_variable_decls
                )
                .0
            ),
            Single,
        )
    } else if op_precedence_map.get(head.to_string().as_str()).is_some() {
        debug_assert_eq!(tuple_rev.len(), 2);
        (
            tuple_rev
                .iter()
                .rev()
                .map(|t| {
                    let (t, t_context) = fmt_type_with_env(
                        t,
                        op_precedence_map,
                        type_variable_decls,
                    );
                    match t_context {
                        Single => t,
                        _ => format!("({})", t),
                    }
                })
                .format(&format!(" {} ", head))
                .to_string(),
            OtherOperator,
        )
    } else {
        (
            format!(
                "{}[{}]",
                head,
                tuple_rev.iter().rev().format_with(", ", |t, f| {
                    let (t, t_context) = fmt_type_with_env(
                        t,
                        op_precedence_map,
                        type_variable_decls,
                    );
                    let s = match t_context {
                        Single => t,
                        _ => format!("({})", t),
                    };
                    f(&s)
                })
            ),
            Single,
        )
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

fn fmt_tuple_as_tuple(
    head: &TypeUnit,
    tuple_rev: &[&Type],
    op_precedence_map: &OpPrecedenceMap,
    type_variable_decls: &FxHashMap<TypeUnit, Name>,
) -> String {
    format!(
        "({}{})",
        fmt_type_unit_with_env(head, op_precedence_map, type_variable_decls).0,
        tuple_rev
            .iter()
            .rev()
            .format_with("", |t, f| f(&format_args!(
                ", {}",
                fmt_type_with_env(t, op_precedence_map, type_variable_decls).0
            )))
    )
}
