pub mod decl_id;
pub mod ident_id;
pub mod types;

use self::types::{unwrap_or_clone, TypeVariable};
use self::{
    decl_id::DeclId,
    ident_id::IdentId,
    types::{Type, TypeUnit},
};
use crate::ast_step1::OpPrecedenceMap;
use crate::ast_step3::VariableRequirement;
use crate::{
    ast_step1,
    intrinsics::{
        IntrinsicConstructor, IntrinsicType, INTRINSIC_CONSTRUCTORS,
        INTRINSIC_TYPES,
    },
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use parser::token_id::TokenId;
use std::collections::BTreeSet;
use std::fmt::Display;
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
    pub decl_id: DeclId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SubtypeRelations<'a>(pub BTreeSet<(Type<'a>, Type<'a>)>);

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub enum PatternUnitForRestriction<'a> {
    I64,
    Str,
    Const {
        name: &'a str,
        id: TypeId,
    },
    Tuple(
        Box<PatternUnitForRestriction<'a>>,
        Box<PatternUnitForRestriction<'a>>,
    ),
    // Constructor {
    //     id: TypeId,
    //     name: &'a str,
    //     args: Vec<PatternUnitForRestriction<'a>>,
    // },
    Binder(Type<'a>, DeclId),
}

pub type PatternForRestriction<'a> = Vec<PatternUnitForRestriction<'a>>;
pub type PatternRestrictions<'a> =
    Vec<(Type<'a>, Vec<PatternUnitForRestriction<'a>>)>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct TypeWithEnv<'a, T = Type<'a>>
where
    T: TypeConstructor<'a>,
{
    pub constructor: T,
    pub variable_requirements: Vec<VariableRequirement<'a>>,
    pub subtype_relations: SubtypeRelations<'a>,
    pub already_considered_relations: SubtypeRelations<'a>,
    pub pattern_restrictions: PatternRestrictions<'a>,
}

pub struct PrintTypeOfGlobalVariableForUser<'a> {
    pub t: &'a TypeWithEnv<'a>,
    pub op_precedence_map: &'a OpPrecedenceMap<'a>,
}

pub struct PrintTypeOfLocalVariableForUser<'a> {
    pub t: &'a Type<'a>,
    pub op_precedence_map: &'a OpPrecedenceMap<'a>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub type_annotation: Option<TypeWithEnv<'a>>,
    pub implicit_parameters: Vec<(&'a str, Type<'a>, DeclId)>,
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
    TypeRestriction(Pattern<'a, T>, Type<'a>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum TokenMapEntry<'a> {
    Decl(DeclId),
    DataDecl(DeclId),
    Ident(IdentId),
    TypeId(TypeId),
    TypeAlias,
    Constructor(ConstructorId),
    TypeVariable,
    Interface,
    VariableDeclInInterface(Type<'a>),
}

#[derive(Default, Debug, PartialEq, Eq)]
pub struct TokenMap<'a>(pub FxHashMap<TokenId, TokenMapEntry<'a>>);

impl<'a> TokenMap<'a> {
    fn insert(&mut self, id: Option<TokenId>, entry: TokenMapEntry<'a>) {
        if let Some(id) = id {
            self.0.insert(id, entry);
        }
    }
}

impl<'a> Ast<'a> {
    pub fn from(ast: ast_step1::Ast<'a>) -> (Self, TokenMap) {
        let mut token_map = TokenMap::default();
        let data_decl: Vec<_> = ast
            .data_decl
            .into_iter()
            .map(|d| {
                let decl_id = DeclId::new();
                token_map.insert(d.name.1, TokenMapEntry::DataDecl(decl_id));
                for ((_, id), interfaces) in d.type_variables.type_variables {
                    token_map.insert(id, TokenMapEntry::TypeVariable);
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
                            TypeVariable::new()
                        })
                        .collect(),
                    decl_id,
                }
            })
            .collect();
        let data_decl_map: FxHashMap<&str, DeclId> =
            data_decl.iter().map(|d| (d.name, d.decl_id)).collect();
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

impl<'a> From<Type<'a>> for TypeWithEnv<'a> {
    fn from(t: Type<'a>) -> Self {
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
    interfaces: &FxHashMap<&'a str, Vec<(&'a str, Type<'a>, TypeVariable)>>,
    token_map: &mut TokenMap,
) -> VariableDecl<'a> {
    let mut type_variable_names = type_variable_names.clone();
    let mut implicit_parameters = Vec::new();
    let decl_id = DeclId::new();
    token_map.insert(v.name.1, TokenMapEntry::Decl(decl_id));
    VariableDecl {
        name: v.name.0,
        type_annotation: v.type_annotation.map(|(t, forall)| {
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
                    (s.0, v)
                },
            ));
            type_to_type(
                t,
                data_decl_map,
                &type_variable_names,
                type_alias_map,
                SearchMode::Normal,
                token_map,
            )
            .into()
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
    interfaces: &FxHashMap<&'a str, Vec<(&'a str, Type<'a>, TypeVariable)>>,
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
    interfaces: &FxHashMap<&'a str, Vec<(&'a str, Type<'a>, TypeVariable)>>,
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
    interfaces: &FxHashMap<&'a str, Vec<(&'a str, Type<'a>, TypeVariable)>>,
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
    fn get<'a>(
        name: &'a str,
        data_decl_map: &FxHashMap<&str, DeclId>,
    ) -> TypeId {
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
) -> Type<'a> {
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
                TypeUnit::Variable(*n).into()
            } else if let Some(i) = INTRINSIC_TYPES.get(&t.name.0) {
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
                let id = TypeId::Intrinsic(*i);
                token_map.insert(t.name.1, TokenMapEntry::TypeId(id));
                TypeUnit::Tuple(
                    TypeUnit::Const { name: t.name.0, id }.into(),
                    tuple,
                )
                .into()
            } else if let Some((mut unaliased, forall)) = type_alias_map.get(
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
                for (from, to) in forall.0.into_iter().zip(t.args) {
                    unaliased = unaliased.replace_num(
                        from,
                        &type_to_type(
                            to,
                            data_decl_map,
                            type_variable_names,
                            type_alias_map,
                            search_type,
                            token_map,
                        ),
                    );
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
                TypeUnit::Tuple(
                    TypeUnit::Const { name: t.name.0, id }.into(),
                    tuple,
                )
                .into()
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
enum AliasComputation<'a> {
    Unaliased(Type<'a>, Forall),
    NotUnaliased,
}

#[derive(Debug, Clone, Default)]
pub struct TypeAliasMap<'a>(
    FxHashMap<
        &'a str,
        (
            (ast_step1::Type<'a>, ast_step1::Forall<'a>),
            AliasComputation<'a>,
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
    ) -> Option<(Type<'a>, Forall)> {
        debug_assert_ne!(search_type, SearchMode::Normal);
        let alias = self.0.get(name.0)?;
        Some(match (&alias, search_type) {
            (
                (_, AliasComputation::Unaliased(t, forall)),
                SearchMode::Alias,
            ) => {
                let mut t = t.clone();
                let mut new_forall = Vec::new();
                for v in &forall.0 {
                    let new_v = TypeVariable::new();
                    t = t.replace_num(*v, &TypeUnit::Variable(new_v).into());
                    new_forall.push(new_v);
                }
                token_map.insert(name.1, TokenMapEntry::TypeAlias);
                (t, Forall(new_forall))
            }
            ((t, _), _) => {
                let mut type_variable_names: FxHashMap<&'a str, TypeVariable> =
                    type_variable_names
                        .clone()
                        .into_iter()
                        .map(|(s, v)| (s, v.increment_recursive_index(1)))
                        .collect();
                type_variable_names
                    .insert(name.0, TypeVariable::RecursiveIndex(0));
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
                let new_t = type_to_type(
                    t.0.clone(),
                    data_decl_map,
                    &type_variable_names,
                    self,
                    search_type,
                    token_map,
                );
                let new_t = if new_t
                    .contains_variable(TypeVariable::RecursiveIndex(0))
                {
                    TypeUnit::RecursiveAlias { body: new_t }.into()
                } else {
                    new_t
                };
                if search_type == SearchMode::Alias {
                    self.0.get_mut(name.0).unwrap().1 =
                        AliasComputation::Unaliased(
                            new_t.clone(),
                            Forall(forall.clone()),
                        );
                }
                token_map.insert(name.1, TokenMapEntry::TypeAlias);
                (decrement_index_outside(new_t), Forall(forall))
            }
        })
    }
}

fn decrement_index_outside(t: Type) -> Type {
    t.into_iter()
        .map(|t| decrement_index_outside_unit(unwrap_or_clone(t)))
        .collect()
}

fn decrement_index_outside_unit(t: TypeUnit) -> TypeUnit {
    match t {
        TypeUnit::Fn(a, b) => {
            TypeUnit::Fn(decrement_index_outside(a), decrement_index_outside(b))
        }
        TypeUnit::Variable(v) => {
            TypeUnit::Variable(v.decrement_recursive_index_with_bound(1))
        }
        TypeUnit::RecursiveAlias { body } => TypeUnit::RecursiveAlias { body },
        TypeUnit::Const { name, id } => TypeUnit::Const { name, id },
        TypeUnit::Tuple(a, b) => TypeUnit::Tuple(
            decrement_index_outside(a),
            decrement_index_outside(b),
        ),
    }
}

impl<'a> IntoIterator for SubtypeRelations<'a> {
    type Item = (Type<'a>, Type<'a>);
    type IntoIter = std::collections::btree_set::IntoIter<(Type<'a>, Type<'a>)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, 'b> IntoIterator for &'b SubtypeRelations<'a> {
    type Item = &'b (Type<'a>, Type<'a>);
    type IntoIter = std::collections::btree_set::Iter<'b, (Type<'a>, Type<'a>)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> FromIterator<(Type<'a>, Type<'a>)> for SubtypeRelations<'a> {
    fn from_iter<T: IntoIterator<Item = (Type<'a>, Type<'a>)>>(
        iter: T,
    ) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<'a> SubtypeRelations<'a> {
    pub fn iter(
        &self,
    ) -> std::collections::btree_set::Iter<(Type<'a>, Type<'a>)> {
        self.0.iter()
    }

    pub fn insert(&mut self, value: (Type<'a>, Type<'a>)) -> bool {
        self.0.insert(value)
    }

    pub fn remove(&mut self, value: &(Type<'a>, Type<'a>)) -> bool {
        self.0.remove(value)
    }

    pub fn contains(&self, value: &(Type<'a>, Type<'a>)) -> bool {
        self.0.contains(value)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<'a> Extend<(Type<'a>, Type<'a>)> for SubtypeRelations<'a> {
    fn extend<T: IntoIterator<Item = (Type<'a>, Type<'a>)>>(
        &mut self,
        iter: T,
    ) {
        self.0.extend(iter)
    }
}

impl<'a> Display for PatternUnitForRestriction<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternUnitForRestriction::I64 => write!(f, "I64Lit"),
            PatternUnitForRestriction::Str => write!(f, "StrLit"),
            PatternUnitForRestriction::Binder(b, decl_id) => {
                write!(f, "Bind({b}, id = {decl_id})")
            }
            PatternUnitForRestriction::Const { name, .. } => {
                write!(f, ":{name}")
            }
            PatternUnitForRestriction::Tuple(a, b) => write!(f, "({a}, {b})"),
        }
    }
}

impl<'a> PatternUnitForRestriction<'a> {
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

    pub fn decl_type_map(&self) -> Vec<(DeclId, &Type<'a>)> {
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
        F: FnMut(Type<'a>) -> Type<'a>,
    {
        self.map_type_rec(f).0
    }

    fn map_type_rec<F>(self, mut f: F) -> (Self, F)
    where
        F: FnMut(Type<'a>) -> Type<'a>,
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
            fmt_type_with_env(&self.t.constructor, self.op_precedence_map).0
        )?;
        let vs = self.t.constructor.all_type_variables();
        if !vs.is_empty() {
            write!(
                f,
                " forall {{ {}{} }}",
                vs.iter().format(", "),
                &self.t.subtype_relations.iter().format_with(
                    "",
                    |(a, b), f| f(&format_args!(", {} <: {}", a, b))
                )
            )?;
        }
        Ok(())
    }
}

impl<'a> Display for PrintTypeOfLocalVariableForUser<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", fmt_type_with_env(self.t, self.op_precedence_map).0)?;
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
    t: &Type<'_>,
    op_precedence_map: &OpPrecedenceMap,
) -> (String, OperatorContext) {
    if t.is_empty() {
        ("∅".to_string(), OperatorContext::Single)
    } else if t.len() == 1 {
        fmt_type_unit_with_env(t.iter().next().unwrap(), op_precedence_map)
    } else {
        (
            t.iter()
                .format_with(" | ", |t, f| {
                    let (t, t_context) =
                        fmt_type_unit_with_env(t, op_precedence_map);
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
    t: &TypeUnit<'_>,
    op_precedence_map: &OpPrecedenceMap,
) -> (String, OperatorContext) {
    use OperatorContext::*;
    match t {
        TypeUnit::Fn(a, b) => {
            let (b, b_context) = fmt_type_with_env(b, op_precedence_map);
            let (a, a_context) = fmt_type_with_env(a, op_precedence_map);
            let s = match (a_context, b_context) {
                (Single, Single | Fn) => format!("{} -> {}", a, b),
                (Single, _) => format!("{} -> ({})", a, b),
                (_, Single | Fn) => format!("({}) -> {}", a, b),
                _ => format!("({}) -> ({})", a, b),
            };
            (s, Fn)
        }
        TypeUnit::Variable(v) => (format!("{}", v), Single),
        TypeUnit::RecursiveAlias { body } => (
            format!("rec[{}]", fmt_type_with_env(body, op_precedence_map).0),
            Single,
        ),
        TypeUnit::Const { name, .. } => (format!(":{}", name), Single),
        TypeUnit::Tuple(hs, ts) => {
            let ts = collect_tuple_rev(ts);
            let hts = hs
                .iter()
                .flat_map(|h| ts.iter().map(move |t| (h, t)))
                .collect_vec();
            if hts.len() == 1 {
                let (h, tuple_rev) = hts[0];
                if let TypeUnit::Const { name, .. } = &**h {
                    fmt_tuple(&**name, tuple_rev, op_precedence_map)
                } else {
                    panic!()
                }
            } else {
                let t = format!(
                    "{}",
                    hts.iter().format_with(" | ", |(h, t), f| {
                        if let TypeUnit::Const { name, .. } = &***h {
                            let (t, t_context) =
                                fmt_tuple(name, t, op_precedence_map);
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
    }
}

fn fmt_tuple(
    head: &str,
    tuple_rev: &[&Type],
    op_precedence_map: &OpPrecedenceMap,
) -> (String, OperatorContext) {
    use OperatorContext::*;
    if tuple_rev.is_empty() {
        (head.to_string(), Single)
    } else if tuple_rev.len() == 1 {
        (
            format!(
                "{}[{}]",
                head,
                fmt_type_with_env(tuple_rev[0], op_precedence_map).0
            ),
            Single,
        )
    } else if op_precedence_map.get(head).is_some() {
        assert_eq!(tuple_rev.len(), 2);
        (
            tuple_rev
                .iter()
                .map(|t| {
                    let (t, t_context) =
                        fmt_type_with_env(t, op_precedence_map);
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
                    let (t, t_context) =
                        fmt_type_with_env(t, op_precedence_map);
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

fn collect_tuple_rev<'a, 'b>(tuple: &'b Type<'a>) -> Vec<Vec<&'b Type<'a>>> {
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
