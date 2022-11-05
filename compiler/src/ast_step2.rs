pub mod decl_id;
pub mod ident_id;
pub mod name_id;
pub mod types;

use self::name_id::Name;
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

/// # Difference between `ast_step1::Ast` and `ast_step2::Ast`
/// - The names of types and constructors are resolved.
/// - Local variable declarations are converted into lambdas and function calls.
#[derive(Debug, PartialEq)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: Name,
    pub fields: Vec<TypeVariable>,
    pub type_variable_decls: Vec<(TypeVariable, Name)>,
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

pub type PatternForRestriction = Vec<PatternUnitForRestriction>;
pub type PatternRestrictions = Vec<(Type, Vec<PatternUnitForRestriction>)>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct TypeWithEnv<T = Type>
where
    T: TypeConstructor,
{
    pub constructor: T,
    pub variable_requirements: Vec<VariableRequirement>,
    pub subtype_relations: SubtypeRelations,
    pub already_considered_relations: SubtypeRelations,
    pub pattern_restrictions: PatternRestrictions,
}

pub struct PrintTypeOfGlobalVariableForUser<'a> {
    pub t: &'a GlobalVariableType,
    pub op_precedence_map: &'a OpPrecedenceMap<'a>,
}

pub struct PrintTypeOfLocalVariableForUser<'a> {
    pub t: &'a Type,
    pub op_precedence_map: &'a OpPrecedenceMap<'a>,
    pub type_variable_decls: &'a FxHashMap<TypeVariable, Name>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl {
    pub name: Name,
    pub type_annotation: Option<TypeWithEnv>,
    pub implicit_parameters: Vec<(Name, Type, DeclId)>,
    pub value: ExprWithType<TypeVariable>,
    pub decl_id: DeclId,
}

pub type ExprWithType<T> = (Expr<T>, T);

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<T> {
    Lambda(Vec<FnArm<T>>),
    Number(Name),
    StrLiteral(Name),
    Ident { name: Name, ident_id: IdentId },
    Call(Box<ExprWithType<T>>, Box<ExprWithType<T>>),
    Do(Vec<ExprWithType<T>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<T> {
    pub pattern: Vec<Pattern<T>>,
    pub expr: ExprWithType<T>,
}

/// Represents a multi-case pattern which matches if any of the `PatternUnit` in it matches.
/// It should have at least one `PatternUnit`.
pub type Pattern<T> = Vec<PatternUnit<T>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit<T> {
    I64(Name),
    Str(Name),
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

#[derive(Default, Debug, PartialEq, Eq)]
pub struct TokenMap(pub FxHashMap<TokenId, TokenMapEntry>);

impl TokenMap {
    fn insert(&mut self, id: Option<TokenId>, entry: TokenMapEntry) {
        if let Some(id) = id {
            self.0.insert(id, entry);
        }
    }
}

pub static TYPE_NAMES: Lazy<RwLock<FxHashMap<TypeId, Name>>> =
    Lazy::new(|| {
        RwLock::new(
            INTRINSIC_TYPES
                .iter()
                .map(|(name, id)| {
                    (TypeId::Intrinsic(*id), Name::from_str(name))
                })
                .collect(),
        )
    });

pub fn get_type_name(type_id: TypeId) -> Name {
    *TYPE_NAMES.read().unwrap().get(&type_id).unwrap()
}

impl Ast {
    pub fn from(ast: ast_step1::Ast) -> (Self, TokenMap) {
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
                    name: Name::from_str(d.name.0),
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
                        .map(|(n, v)| (v, Name::from_str(n)))
                        .collect(),
                }
            })
            .collect();
        let data_decl_map: FxHashMap<Name, DeclId> =
            data_decl.iter().map(|d| (d.name, d.decl_id)).collect();
        {
            TYPE_NAMES.write().unwrap().extend(
                data_decl
                    .iter()
                    .map(|d| (TypeId::DeclId(d.decl_id), d.name)),
            );
        }
        let mut type_alias_map = TypeAliasMap(
            ast.type_alias_decl
                .into_iter()
                .map(|a| {
                    token_map.insert(a.name.1, TokenMapEntry::TypeAlias);
                    (
                        Name::from_str(a.name.0),
                        (a.body, AliasComputation::NotUnaliased),
                    )
                })
                .collect(),
        );
        let interface_decl: FxHashMap<Name, Vec<_>> = ast
            .interface_decl
            .into_iter()
            .map(|i| {
                token_map.insert(i.name.1, TokenMapEntry::Interface);
                (
                    Name::from_str(i.name.0),
                    i.variables
                        .into_iter()
                        .map(|(name, t, forall)| {
                            let self_ = TypeVariable::new();
                            let (t, _) = type_to_type_with_forall(
                                t,
                                &data_decl_map,
                                std::iter::once((
                                    Name::from_str("Self"),
                                    self_,
                                ))
                                .collect(),
                                &mut type_alias_map,
                                forall,
                                &Default::default(),
                                &mut token_map,
                            );
                            token_map.insert(
                                name.1,
                                TokenMapEntry::VariableDeclInInterface(
                                    t.clone(),
                                ),
                            );
                            (Name::from_str(name.0), t, self_)
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
            .find(|d| d.name == Name::from_str("main"))
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
    data_decl_map: &FxHashMap<Name, DeclId>,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    type_alias_map: &mut TypeAliasMap,
    interfaces: &FxHashMap<Name, Vec<(Name, Type, TypeVariable)>>,
    token_map: &mut TokenMap,
) -> VariableDecl {
    let mut implicit_parameters = Vec::new();
    let decl_id = DeclId::new();
    token_map.insert(v.name.1, TokenMapEntry::Decl(decl_id));
    VariableDecl {
        name: Name::from_str(v.name.0),
        type_annotation: v.type_annotation.map(|(t, forall)| {
            let (t, ps) = type_to_type_with_forall(
                t,
                data_decl_map,
                type_variable_names.clone(),
                type_alias_map,
                forall,
                interfaces,
                token_map,
            );
            implicit_parameters = ps;
            t.into()
        }),
        value: expr(
            v.value,
            data_decl_map,
            type_variable_names,
            type_alias_map,
            interfaces,
            token_map,
        ),
        decl_id,
        implicit_parameters,
    }
}

fn expr(
    e: ast_step1::Expr,
    data_decl_map: &FxHashMap<Name, DeclId>,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    type_alias_map: &mut TypeAliasMap,
    interfaces: &FxHashMap<Name, Vec<(Name, Type, TypeVariable)>>,
    token_map: &mut TokenMap,
) -> ExprWithType<TypeVariable> {
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
        ast_step1::Expr::Number(n) => Number(Name::from_str(n)),
        ast_step1::Expr::StrLiteral(s) => StrLiteral(Name::from_str(s)),
        ast_step1::Expr::Ident(name) => {
            let ident_id = IdentId::new();
            token_map.insert(name.1, TokenMapEntry::Ident(ident_id));
            Ident {
                name: Name::from_str(name.0),
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

fn add_expr_in_do(
    e: ast_step1::Expr,
    mut es: Vec<ExprWithType<TypeVariable>>,
    data_decl_map: &FxHashMap<Name, DeclId>,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    type_alias_map: &mut TypeAliasMap,
    interfaces: &FxHashMap<Name, Vec<(Name, Type, TypeVariable)>>,
    token_map: &mut TokenMap,
) -> Vec<ExprWithType<TypeVariable>> {
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
                            name: Name::from_str("()"),
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

fn fn_arm(
    arm: ast_step1::FnArm,
    data_decl_map: &FxHashMap<Name, DeclId>,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    type_alias_map: &mut TypeAliasMap,
    interfaces: &FxHashMap<Name, Vec<(Name, Type, TypeVariable)>>,
    token_map: &mut TokenMap,
) -> FnArm<TypeVariable> {
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
    fn get(name: Name, data_decl_map: &FxHashMap<Name, DeclId>) -> TypeId {
        if let Some(id) = data_decl_map.get(&name) {
            TypeId::DeclId(*id)
        } else if let Some(i) = INTRINSIC_TYPES.get(&name.as_str().as_str()) {
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
            INTRINSIC_CONSTRUCTORS.get(name.as_str().as_str())
        {
            ConstructorId::Intrinsic(*i)
        } else {
            panic!("{:?} not fould", name)
        }
    }
}

fn pattern(
    p: ast_step1::Pattern,
    data_decl_map: &FxHashMap<Name, DeclId>,
    token_map: &mut TokenMap,
) -> Pattern<TypeVariable> {
    use PatternUnit::*;
    match p {
        ast_step1::Pattern::Number(n) => I64(Name::from_str(n)),
        ast_step1::Pattern::StrLiteral(s) => Str(Name::from_str(s)),
        ast_step1::Pattern::Constructor { name, args } => {
            let id = ConstructorId::get(Name::from_str(name.0), data_decl_map);
            token_map.insert(name.1, TokenMapEntry::Constructor(id));
            Constructor {
                name: Name::from_str(name.0),
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
            Binder(Name::from_str(name.0), decl_id, TypeVariable::new())
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

pub fn type_to_type(
    t: ast_step1::Type,
    data_decl_map: &FxHashMap<Name, DeclId>,
    type_variable_names: &FxHashMap<Name, TypeVariable>,
    type_alias_map: &mut TypeAliasMap,
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
            if let Some(n) = type_variable_names.get(&Name::from_str(t.name.0))
            {
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
                (Name::from_str(t.name.0), t.name.1),
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
                let id = TypeId::get(Name::from_str(t.name.0), data_decl_map);
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
) -> (Type, Vec<(Name, Type, DeclId)>) {
    let mut implicit_parameters = Vec::new();
    let mut type_variable_decls = FxHashMap::default();
    let mut type_parameters = Vec::new();
    for (s, interface_names) in forall.type_variables {
        token_map.insert(s.1, TokenMapEntry::TypeVariable);
        let v = TypeVariable::new();
        for name in interface_names {
            token_map.insert(name.1, TokenMapEntry::Interface);
            for (name, t, self_) in &interfaces[&Name::from_str(name.0)] {
                implicit_parameters.push((
                    *name,
                    t.clone()
                        .replace_num(*self_, &TypeUnit::Variable(v).into()),
                    DeclId::new(),
                ))
            }
        }
        type_parameters.push(v);
        type_variable_decls.insert(v, Name::from_str(s.0));
        type_variable_names.insert(Name::from_str(s.0), v);
    }
    let mut t = type_to_type(
        t,
        data_decl_map,
        &type_variable_names,
        type_alias_map,
        SearchMode::Normal,
        token_map,
    );
    if !implicit_parameters.is_empty() {
        t = TypeUnit::Restrictions {
            t,
            variable_requirements: implicit_parameters
                .iter()
                .map(|(name, required_type, _decl_id)| {
                    (*name, required_type.clone())
                })
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
    (t, implicit_parameters)
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
        Some(match (&alias, search_type) {
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
                            type_variable_names.insert(Name::from_str(s.0), v);
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
        let mut s = Self::default();
        for r in iter {
            s.insert(r);
        }
        s
    }
}

impl SubtypeRelations {
    pub fn iter(&self) -> std::collections::btree_set::Iter<(Type, Type)> {
        self.0.iter()
    }

    pub fn insert(&mut self, value: (Type, Type)) -> bool {
        debug_assert!(!value.0.contains_restriction());
        debug_assert!(!value.1.contains_restriction());
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

impl Display for PrintTypeOfGlobalVariableForUser<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            fmt_type_with_env(
                &self.t.type_with_env.constructor,
                self.op_precedence_map,
                &Default::default()
            )
            .0
        )?;
        let vs = self.t.type_with_env.constructor.all_type_variables();
        if !vs.is_empty() {
            write!(
                f,
                " forall {{ {}{} }}",
                vs.iter().format_with(", ", |v, f| { f(v) }),
                &self.t.type_with_env.subtype_relations.iter().format_with(
                    "",
                    |(a, b), f| f(&format_args!(
                        ", {} <: {}",
                        fmt_type_with_env(
                            a,
                            self.op_precedence_map,
                            &Default::default()
                        )
                        .0,
                        fmt_type_with_env(
                            b,
                            self.op_precedence_map,
                            &Default::default()
                        )
                        .0
                    ))
                )
            )?;
        }
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

enum OperatorContext {
    Single,
    Fn,
    Or,
    OtherOperator,
}

fn fmt_type_with_env(
    t: &Type,
    op_precedence_map: &OpPrecedenceMap,
    type_variable_decls: &FxHashMap<TypeVariable, Name>,
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
    type_variable_decls: &FxHashMap<TypeVariable, Name>,
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
                        *id,
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
                            panic!()
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
    type_variable_decls: &FxHashMap<TypeVariable, Name>,
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
