pub mod decl_id;
pub mod ident_id;
pub mod types;

use self::types::TypeVariable;
use self::{
    decl_id::DeclId,
    ident_id::IdentId,
    types::{Type, TypeUnit},
};
use crate::ast_step1::OpPrecedenceMap;
use crate::ast_step3::{GlobalVariableType, VariableRequirement};
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
use std::collections::BTreeSet;
use std::fmt::Display;
use std::sync::RwLock;
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
}

/// # Difference between `ast_step1::Ast` and `ast_step2::Ast`
/// - The names of types and constructors are resolved.
/// - Local variable declarations are converted into lambdas and function calls.
#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl<'a> {
    pub name: &'a str,
    pub fields: Vec<TypeVariable>,
    pub type_variable_decls: Vec<(TypeVariable, &'a str)>,
    pub decl_id: DeclId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SubtypeRelations(pub BTreeSet<(Type, Type)>);

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
}

pub type PatternForRestriction<'a> = Vec<PatternUnitForRestriction>;
pub type PatternRestrictions<'a> = Vec<(Type, Vec<PatternUnitForRestriction>)>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct TypeWithEnv<'a, T = Type>
where
    T: TypeConstructor<'a>,
{
    pub constructor: T,
    pub variable_requirements: Vec<VariableRequirement<'a>>,
    pub subtype_relations: SubtypeRelations,
    pub already_considered_relations: SubtypeRelations,
    pub pattern_restrictions: PatternRestrictions<'a>,
}

pub struct PrintTypeOfGlobalVariableForUser<'a> {
    pub t: &'a GlobalVariableType<'a>,
    pub op_precedence_map: &'a OpPrecedenceMap<'a>,
}

pub struct PrintTypeOfLocalVariableForUser<'a> {
    pub t: &'a Type,
    pub op_precedence_map: &'a OpPrecedenceMap<'a>,
    pub type_variable_decls: &'a FxHashMap<TypeVariable, &'a str>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub type_annotation: Option<GlobalVariableType<'a>>,
    pub implicit_parameters: Vec<(&'a str, Type, DeclId)>,
    pub value: ExprWithType<'a, TypeVariable>,
    pub decl_id: DeclId,
}

pub type ExprWithType<'a, T> = (Expr<'a, T>, T);

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a, T> {
    Lambda(Vec<FnArm<'a, T>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident { name: &'a str, ident_id: IdentId },
    Call(Box<ExprWithType<'a, T>>, Box<ExprWithType<'a, T>>),
    Do(Vec<ExprWithType<'a, T>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a, T> {
    pub pattern: Vec<Pattern<'a, T>>,
    pub expr: ExprWithType<'a, T>,
}

/// Represents a multi-case pattern which matches if any of the `PatternUnit` in it matches.
/// It should have at least one `PatternUnit`.
pub type Pattern<'a, T> = Vec<PatternUnit<'a, T>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit<'a, T> {
    I64(&'a str),
    Str(&'a str),
    Constructor {
        name: &'a str,
        id: ConstructorId,
        args: Vec<Pattern<'a, T>>,
    },
    Binder(&'a str, DeclId, T),
    Underscore,
    TypeRestriction(Pattern<'a, T>, Type),
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

#[derive(Default, Debug, PartialEq, Eq)]
pub struct TokenMap(pub FxHashMap<TokenId, TokenMapEntry>);

impl TokenMap {
    fn insert(&mut self, id: Option<TokenId>, entry: TokenMapEntry) {
        if let Some(id) = id {
            self.0.insert(id, entry);
        }
    }
}

pub static TYPE_NAMES: Lazy<RwLock<FxHashMap<TypeId, String>>> =
    Lazy::new(|| {
        RwLock::new(
            INTRINSIC_TYPES
                .iter()
                .map(|(name, id)| (TypeId::Intrinsic(*id), name.to_string()))
                .collect(),
        )
    });

impl<'a> Ast<'a> {
    pub fn from(ast: ast_step1::Ast<'a>) -> (Self, TokenMap) {
        let mut token_map = TokenMap::default();
        let data_decl: Vec<_> = ast
            .data_decl
            .into_iter()
            .map(|d| {
                let decl_id = DeclId::new();
                let mut type_variables = FxHashMap::default();
                token_map.insert(d.name.1, TokenMapEntry::DataDecl(decl_id));
                for ((name, id), interfaces) in d.type_variables.type_variables
                {
                    token_map.insert(id, TokenMapEntry::TypeVariable);
                    type_variables.insert(name, TypeVariable::new());
                    for (_, id) in interfaces {
                        token_map.insert(id, TokenMapEntry::Interface);
                    }
                }
                DataDecl {
                    name: d.name.0,
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
                        .map(|(n, v)| (v, n))
                        .collect(),
                }
            })
            .collect();
        let data_decl_map: FxHashMap<&str, DeclId> =
            data_decl.iter().map(|d| (d.name, d.decl_id)).collect();
        TYPE_NAMES.write().unwrap().extend(
            data_decl
                .iter()
                .map(|d| (TypeId::DeclId(d.decl_id), d.name.to_string())),
        );
        let mut type_alias_map = TypeAliasMap(
            ast.type_alias_decl
                .into_iter()
                .map(|a| {
                    token_map.insert(a.name.1, TokenMapEntry::TypeAlias);
                    (a.name.0, (a.body, AliasComputation::NotUnaliased))
                })
                .collect(),
        );
        let interface_decl: FxHashMap<&str, Vec<_>> = ast
            .interface_decl
            .into_iter()
            .map(|i| {
                token_map.insert(i.name.1, TokenMapEntry::Interface);
                (
                    i.name.0,
                    i.variables
                        .into_iter()
                        .map(|(name, t, forall)| {
                            let self_ = TypeVariable::new();
                            let t = type_to_type(
                                t,
                                &data_decl_map,
                                &forall
                                    .type_variables
                                    .into_iter()
                                    .map(|(s, _)| {
                                        token_map.insert(
                                            s.1,
                                            TokenMapEntry::TypeVariable,
                                        );
                                        (s.0, TypeVariable::new())
                                    })
                                    .chain(std::iter::once(("Self", self_)))
                                    .collect(),
                                &mut type_alias_map,
                                SearchMode::Normal,
                                &mut token_map,
                            );
                            token_map.insert(
                                name.1,
                                TokenMapEntry::VariableDeclInInterface(
                                    t.clone(),
                                ),
                            );
                            (name.0, t, self_)
                        })
                        .collect(),
                )
            })
            .collect();
        let variable_decl: Vec<_> = ast
            .variable_decl
            .into_iter()
            .map(|d| {
                variable_decl(
                    d,
                    &data_decl_map,
                    &Default::default(),
                    &mut type_alias_map,
                    &interface_decl,
                    &mut token_map,
                )
            })
            .collect();
        let entry_point = variable_decl
            .iter()
            .find(|d| d.name == "main")
            .unwrap_or_else(|| panic!("entry point not found"))
            .decl_id;
        (
            Self {
                variable_decl,
                data_decl,
                entry_point,
            },
            token_map,
        )
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
            TypeId::DeclId(decl_id) => write!(f, "{}", decl_id),
            TypeId::Intrinsic(i) => write!(f, "{:?}", i),
        }
    }
}

impl<'a> From<Type> for TypeWithEnv<'a> {
    fn from(t: Type) -> Self {
        Self {
            constructor: t,
            ..Default::default()
        }
    }
}

impl<'a, T> From<PatternUnit<'a, T>> for Pattern<'a, T> {
    fn from(p: PatternUnit<'a, T>) -> Self {
        vec![p]
    }
}

fn variable_decl<'a>(
    v: ast_step1::VariableDecl<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
    type_alias_map: &mut TypeAliasMap<'a>,
    interfaces: &FxHashMap<&'a str, Vec<(&'a str, Type, TypeVariable)>>,
    token_map: &mut TokenMap,
) -> VariableDecl<'a> {
    let mut type_variable_names = type_variable_names.clone();
    let mut implicit_parameters = Vec::new();
    let decl_id = DeclId::new();
    token_map.insert(v.name.1, TokenMapEntry::Decl(decl_id));
    VariableDecl {
        name: v.name.0,
        type_annotation: v.type_annotation.map(|(t, forall)| {
            let mut type_variable_decls = FxHashMap::default();
            type_variable_names.extend(forall.type_variables.into_iter().map(
                |(s, interface_names)| {
                    token_map.insert(s.1, TokenMapEntry::TypeVariable);
                    let v = TypeVariable::new();
                    for name in interface_names {
                        token_map.insert(name.1, TokenMapEntry::Interface);
                        for (name, t, self_) in &interfaces[&name.0] {
                            implicit_parameters.push((
                                *name,
                                t.clone().replace_num(
                                    *self_,
                                    &TypeUnit::Variable(v).into(),
                                ),
                                DeclId::new(),
                            ))
                        }
                    }
                    type_variable_decls.insert(v, s.0);
                    (s.0, v)
                },
            ));
            let type_with_env = type_to_type(
                t,
                data_decl_map,
                &type_variable_names,
                type_alias_map,
                SearchMode::Normal,
                token_map,
            )
            .into();
            GlobalVariableType {
                type_with_env,
                type_variable_decls,
            }
        }),
        value: expr(
            v.value,
            data_decl_map,
            &type_variable_names,
            type_alias_map,
            interfaces,
            token_map,
        ),
        decl_id,
        implicit_parameters,
    }
}

fn expr<'a>(
    e: ast_step1::Expr<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
    type_alias_map: &mut TypeAliasMap<'a>,
    interfaces: &FxHashMap<&'a str, Vec<(&'a str, Type, TypeVariable)>>,
    token_map: &mut TokenMap,
) -> ExprWithType<'a, TypeVariable> {
    use Expr::*;
    let e = match e {
        ast_step1::Expr::Lambda(arms) => Lambda(
            arms.into_iter()
                .map(move |arm| {
                    fn_arm(
                        arm,
                        data_decl_map,
                        type_variable_names,
                        type_alias_map,
                        interfaces,
                        token_map,
                    )
                })
                .collect(),
        ),
        ast_step1::Expr::Number(n) => Number(n),
        ast_step1::Expr::StrLiteral(s) => StrLiteral(s),
        ast_step1::Expr::Ident(name) => {
            let ident_id = IdentId::new();
            token_map.insert(name.1, TokenMapEntry::Ident(ident_id));
            Ident {
                name: name.0,
                ident_id,
            }
        }
        ast_step1::Expr::Decl(d) => {
            let d = variable_decl(
                *d,
                data_decl_map,
                type_variable_names,
                type_alias_map,
                interfaces,
                token_map,
            );
            d.value.0
        }
        ast_step1::Expr::Call(f, a) => Call(
            Box::new(expr(
                *f,
                data_decl_map,
                type_variable_names,
                type_alias_map,
                interfaces,
                token_map,
            )),
            Box::new(expr(
                *a,
                data_decl_map,
                type_variable_names,
                type_alias_map,
                interfaces,
                token_map,
            )),
        ),
        ast_step1::Expr::Do(es) => {
            let mut new_es = Vec::new();
            for e in es.into_iter().rev() {
                new_es = add_expr_in_do(
                    e,
                    new_es,
                    data_decl_map,
                    type_variable_names,
                    type_alias_map,
                    interfaces,
                    token_map,
                );
            }
            new_es.reverse();
            Do(new_es)
        }
    };
    (e, TypeVariable::new())
}

fn add_expr_in_do<'a>(
    e: ast_step1::Expr<'a>,
    mut es: Vec<ExprWithType<'a, TypeVariable>>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
    type_alias_map: &mut TypeAliasMap<'a>,
    interfaces: &FxHashMap<&'a str, Vec<(&'a str, Type, TypeVariable)>>,
    token_map: &mut TokenMap,
) -> Vec<ExprWithType<'a, TypeVariable>> {
    match e {
        ast_step1::Expr::Decl(d) => {
            let d = variable_decl(
                *d,
                data_decl_map,
                type_variable_names,
                type_alias_map,
                interfaces,
                token_map,
            );
            if es.is_empty() {
                vec![
                    (
                        Expr::Ident {
                            name: "()",
                            ident_id: IdentId::new(),
                        },
                        TypeVariable::new(),
                    ),
                    d.value,
                ]
            } else {
                es.reverse();
                let l = Expr::Lambda(vec![FnArm {
                    pattern: vec![PatternUnit::Binder(
                        d.name,
                        d.decl_id,
                        TypeVariable::new(),
                    )
                    .into()],
                    expr: (Expr::Do(es), TypeVariable::new()),
                }]);
                vec![(
                    Expr::Call(
                        Box::new((l, TypeVariable::new())),
                        Box::new(d.value),
                    ),
                    TypeVariable::new(),
                )]
            }
        }
        e => {
            es.push(expr(
                e,
                data_decl_map,
                type_variable_names,
                type_alias_map,
                interfaces,
                token_map,
            ));
            es
        }
    }
}

fn fn_arm<'a>(
    arm: ast_step1::FnArm<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
    type_alias_map: &mut TypeAliasMap<'a>,
    interfaces: &FxHashMap<&'a str, Vec<(&'a str, Type, TypeVariable)>>,
    token_map: &mut TokenMap,
) -> FnArm<'a, TypeVariable> {
    FnArm {
        pattern: arm
            .pattern
            .into_iter()
            .map(|p| pattern(p, data_decl_map, token_map))
            .collect(),
        expr: expr(
            arm.expr,
            data_decl_map,
            type_variable_names,
            type_alias_map,
            interfaces,
            token_map,
        ),
    }
}

impl TypeId {
    fn get(name: &str, data_decl_map: &FxHashMap<&str, DeclId>) -> TypeId {
        if let Some(id) = data_decl_map.get(name) {
            TypeId::DeclId(*id)
        } else if let Some(i) = INTRINSIC_TYPES.get(name) {
            TypeId::Intrinsic(*i)
        } else {
            panic!("{:?} not fould", name)
        }
    }
}

impl ConstructorId {
    fn get(
        name: &str,
        data_decl_map: &FxHashMap<&str, DeclId>,
    ) -> ConstructorId {
        if let Some(id) = data_decl_map.get(name) {
            ConstructorId::DeclId(*id)
        } else if let Some(i) = INTRINSIC_CONSTRUCTORS.get(name) {
            ConstructorId::Intrinsic(*i)
        } else {
            panic!("{:?} not fould", name)
        }
    }
}

fn pattern<'a>(
    p: ast_step1::Pattern<'a>,
    data_decl_map: &FxHashMap<&str, DeclId>,
    token_map: &mut TokenMap,
) -> Pattern<'a, TypeVariable> {
    use PatternUnit::*;
    match p {
        ast_step1::Pattern::Number(n) => I64(n),
        ast_step1::Pattern::StrLiteral(s) => Str(s),
        ast_step1::Pattern::Constructor { name, args } => {
            let id = ConstructorId::get(name.0, data_decl_map);
            token_map.insert(name.1, TokenMapEntry::Constructor(id));
            Constructor {
                name: name.0,
                id,
                args: args
                    .into_iter()
                    .map(|arg| pattern(arg, data_decl_map, token_map))
                    .collect(),
            }
        }
        ast_step1::Pattern::Binder(name) => {
            let decl_id = DeclId::new();
            token_map.insert(name.1, TokenMapEntry::Decl(decl_id));
            Binder(name.0, decl_id, TypeVariable::new())
        }
        ast_step1::Pattern::Underscore => Underscore,
    }
    .into()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchMode {
    Normal,
    Alias,
    AliasSub,
}

pub fn type_to_type<'a>(
    t: ast_step1::Type<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
    type_alias_map: &mut TypeAliasMap<'a>,
    search_type: SearchMode,
    token_map: &mut TokenMap,
) -> Type {
    match t.name.0 {
        "|" => t
            .args
            .into_iter()
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
                t.args[0].clone(),
                data_decl_map,
                type_variable_names,
                type_alias_map,
                search_type,
                token_map,
            ),
            type_to_type(
                t.args[1].clone(),
                data_decl_map,
                type_variable_names,
                type_alias_map,
                search_type,
                token_map,
            ),
        )
        .into(),
        _ => {
            if let Some(n) = type_variable_names.get(t.name.0) {
                token_map.insert(t.name.1, TokenMapEntry::TypeVariable);
                let mut new_t = Type::from(TypeUnit::Variable(*n));
                for a in t.args {
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
                t.name,
                data_decl_map,
                type_variable_names,
                if search_type == SearchMode::Normal {
                    SearchMode::Alias
                } else {
                    SearchMode::AliasSub
                },
                token_map,
            ) {
                for a in t.args {
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
                    .into_iter()
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
                let id = TypeId::get(t.name.0, data_decl_map);
                token_map.insert(t.name.1, TokenMapEntry::TypeId(id));
                TypeUnit::Tuple(TypeUnit::Const { id }.into(), tuple).into()
            }
        }
    }
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
        &'a str,
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
        name: (&'a str, Option<TokenId>),
        data_decl_map: &FxHashMap<&'a str, DeclId>,
        type_variable_names: &FxHashMap<&'a str, TypeVariable>,
        search_type: SearchMode,
        token_map: &mut TokenMap,
    ) -> Option<Type> {
        debug_assert_ne!(search_type, SearchMode::Normal);
        if let Some(t) = type_variable_names.get(&name.0) {
            token_map.insert(name.1, TokenMapEntry::TypeAlias);
            return Some(TypeUnit::Variable(*t).into());
        }
        let alias = self.0.get(name.0)?;
        Some(match (&alias, search_type) {
            ((_, AliasComputation::Unaliased(t)), SearchMode::Alias) => {
                token_map.insert(name.1, TokenMapEntry::TypeAlias);
                t.clone()
            }
            ((t, _), _) => {
                let mut type_variable_names: FxHashMap<&'a str, TypeVariable> =
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
                let forall =
                    t.1.clone()
                        .type_variables
                        .into_iter()
                        .map(|(s, interfaces)| {
                            let v = TypeVariable::new();
                            token_map.insert(s.1, TokenMapEntry::TypeVariable);
                            for (_, id) in interfaces {
                                token_map.insert(id, TokenMapEntry::Interface);
                            }
                            type_variable_names.insert(s.0, v);
                            v
                        })
                        .collect_vec();
                let mut t = type_to_type(
                    t.0.clone(),
                    data_decl_map,
                    &type_variable_names,
                    self,
                    search_type,
                    token_map,
                );
                token_map.insert(name.1, TokenMapEntry::TypeAlias);
                for v in forall {
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
                    t.decrement_recursive_index(0)
                };
                if search_type == SearchMode::Alias {
                    self.0.get_mut(name.0).unwrap().1 =
                        AliasComputation::Unaliased(t.clone());
                }
                t
            }
        })
    }
}

impl IntoIterator for SubtypeRelations {
    type Item = (Type, Type);
    type IntoIter = std::collections::btree_set::IntoIter<(Type, Type)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'b> IntoIterator for &'b SubtypeRelations {
    type Item = &'b (Type, Type);
    type IntoIter = std::collections::btree_set::Iter<'b, (Type, Type)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl FromIterator<(Type, Type)> for SubtypeRelations {
    fn from_iter<T: IntoIterator<Item = (Type, Type)>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl SubtypeRelations {
    pub fn iter(&self) -> std::collections::btree_set::Iter<(Type, Type)> {
        self.0.iter()
    }

    pub fn insert(&mut self, value: (Type, Type)) -> bool {
        self.0.insert(value)
    }

    pub fn remove(&mut self, value: &(Type, Type)) -> bool {
        self.0.remove(value)
    }

    pub fn contains(&self, value: &(Type, Type)) -> bool {
        self.0.contains(value)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl Extend<(Type, Type)> for SubtypeRelations {
    fn extend<T: IntoIterator<Item = (Type, Type)>>(&mut self, iter: T) {
        self.0.extend(iter)
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
        }
    }
}

impl<'a> Display for PrintTypeOfGlobalVariableForUser<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            fmt_type_with_env(
                &self.t.type_with_env.constructor,
                self.op_precedence_map,
                &self.t.type_variable_decls
            )
            .0
        )?;
        let vs = self.t.type_with_env.constructor.all_type_variables();
        if !vs.is_empty() {
            write!(
                f,
                " forall {{ {}{} }}",
                vs.iter().format_with(", ", |v, f| {
                    if let Some(s) = self.t.type_variable_decls.get(v) {
                        f(s)
                    } else {
                        f(v)
                    }
                }),
                &self.t.type_with_env.subtype_relations.iter().format_with(
                    "",
                    |(a, b), f| f(&format_args!(
                        ", {} <: {}",
                        fmt_type_with_env(
                            a,
                            self.op_precedence_map,
                            &self.t.type_variable_decls
                        )
                        .0,
                        fmt_type_with_env(
                            b,
                            self.op_precedence_map,
                            &self.t.type_variable_decls
                        )
                        .0
                    ))
                )
            )?;
        }
        Ok(())
    }
}

impl<'a> Display for PrintTypeOfLocalVariableForUser<'a> {
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

enum OperatorContext {
    Single,
    Fn,
    Or,
    OtherOperator,
}

fn fmt_type_with_env(
    t: &Type,
    op_precedence_map: &OpPrecedenceMap,
    type_variable_decls: &FxHashMap<TypeVariable, &str>,
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
    type_variable_decls: &FxHashMap<TypeVariable, &str>,
) -> (String, OperatorContext) {
    use OperatorContext::*;
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
        TypeUnit::Variable(v) => {
            if let Some(s) = type_variable_decls.get(v) {
                (s.to_string(), Single)
            } else {
                (v.to_string(), Single)
            }
        }
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
                        TYPE_NAMES.read().unwrap().get(id).unwrap(),
                        tuple_rev,
                        op_precedence_map,
                        type_variable_decls,
                    )
                } else {
                    panic!()
                }
            } else {
                let t = format!(
                    "{}",
                    hts.iter().format_with(" | ", |(h, t), f| {
                        if let TypeUnit::Const { id } = &***h {
                            let (t, t_context) = fmt_tuple(
                                TYPE_NAMES.read().unwrap().get(id).unwrap(),
                                t,
                                op_precedence_map,
                                type_variable_decls,
                            );
                            match t_context {
                                Single | Or => f(&t),
                                _ => f(&format_args!("({})", t)),
                            }
                        } else {
                            panic!()
                        }
                    })
                );
                (t, Or)
            }
        }
        TypeUnit::TypeLevelFn(f) => (
            format!(
                "rec[{}]",
                fmt_type_with_env(f, op_precedence_map, type_variable_decls).0
            ),
            Single,
        ),
        TypeUnit::TypeLevelApply { f, a } => {
            let (f, f_context) =
                fmt_type_with_env(f, op_precedence_map, type_variable_decls);
            let (a, a_context) =
                fmt_type_with_env(a, op_precedence_map, type_variable_decls);
            let s = match (f_context, a_context) {
                (Single, Single) => format!("{} {}", f, a),
                (Single, _) => format!("{}, ({})", f, a),
                (_, Single) => format!("({}) -> {}", f, a),
                _ => format!("({}) -> ({})", f, a),
            };
            (s, Fn)
        }
    }
}

fn fmt_tuple(
    head: &str,
    tuple_rev: &[&Type],
    op_precedence_map: &OpPrecedenceMap,
    type_variable_decls: &FxHashMap<TypeVariable, &str>,
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
    } else if op_precedence_map.get(head).is_some() {
        assert_eq!(tuple_rev.len(), 2);
        (
            tuple_rev
                .iter()
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

fn collect_tuple_rev(tuple: &Type) -> Vec<Vec<&Type>> {
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
