pub mod decl_id;
pub mod ident_id;
pub mod types;

use self::types::TypeVariable;
use self::{
    decl_id::{new_decl_id, DeclId},
    ident_id::{new_ident_id, IdentId},
    types::{Type, TypeUnit},
};
use crate::{
    ast_step1,
    intrinsics::{
        IntrinsicConstructor, IntrinsicType, INTRINSIC_CONSTRUCTORS,
        INTRINSIC_TYPES,
    },
};
use fxhash::FxHashMap;
use std::collections::BTreeSet;
pub use types::TypeConstructor;

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
pub enum ConstructorId<'a> {
    DeclId(DeclId, &'a str),
    Intrinsic(IntrinsicConstructor),
}

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
pub enum TypeId {
    DeclId(DeclId),
    Intrinsic(IntrinsicType),
}

/// # Difference between `ast_step1::Ast` and `ast_step2::Ast`
/// - The names of types and constructors are resolved.
#[derive(Debug, PartialEq, Clone)]
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IncompleteType<'a, T = Type<'a>>
where
    T: TypeConstructor<'a>,
{
    pub constructor: T,
    pub variable_requirements: Vec<(&'a str, Type<'a>, IdentId)>,
    pub subtype_relation: BTreeSet<(Type<'a>, Type<'a>)>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub type_annotation: Option<IncompleteType<'a>>,
    pub value: ExprWithType<'a>,
    pub decl_id: DeclId,
}

pub type ExprWithType<'a> = (Expr<'a>, TypeVariable);

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident { name: &'a str, ident_id: IdentId },
    Decl(Box<VariableDecl<'a>>),
    Call(Box<ExprWithType<'a>>, Box<ExprWithType<'a>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub pattern_type: Vec<Option<Type<'a>>>,
    pub exprs: Vec<ExprWithType<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern<'a> {
    Number(&'a str),
    StrLiteral(&'a str),
    Constructor {
        id: ConstructorId<'a>,
        args: Vec<Pattern<'a>>,
    },
    Binder(&'a str, DeclId),
    Underscore,
}

impl<'a> From<ast_step1::Ast<'a>> for Ast<'a> {
    fn from(ast: ast_step1::Ast<'a>) -> Self {
        let data_decl: Vec<_> = ast
            .data_decl
            .into_iter()
            .map(|d| DataDecl {
                name: d.name,
                fields: (0..d.field_len)
                    .map(|_| TypeVariable::new())
                    .collect(),
                decl_id: new_decl_id(),
            })
            .collect();
        let data_decl_map: FxHashMap<&str, DeclId> =
            data_decl.iter().map(|d| (d.name, d.decl_id)).collect();
        let variable_decl: Vec<_> = ast
            .variable_decl
            .into_iter()
            .map(|d| {
                variable_decl(d, &data_decl_map, &Default::default())
            })
            .collect();
        let entry_point = variable_decl
            .iter()
            .find(|d| d.name == "main")
            .unwrap_or_else(|| panic!("entry point not found"))
            .decl_id;
        Self {
            variable_decl,
            data_decl,
            entry_point,
        }
    }
}

impl<'a> ConstructorId<'a> {
    pub fn name(&self) -> &'a str {
        match self {
            ConstructorId::DeclId(_, name) => name,
            ConstructorId::Intrinsic(c) => c.to_str(),
        }
    }
}

impl<'a> From<ConstructorId<'a>> for TypeId {
    fn from(c: ConstructorId<'a>) -> Self {
        match c {
            ConstructorId::DeclId(ident, _) => Self::DeclId(ident),
            ConstructorId::Intrinsic(i) => Self::Intrinsic(i.into()),
        }
    }
}

impl<'a> From<Type<'a>> for IncompleteType<'a> {
    fn from(t: Type<'a>) -> Self {
        Self {
            constructor: t,
            variable_requirements: Default::default(),
            subtype_relation: Default::default(),
        }
    }
}

fn variable_decl<'a>(
    v: ast_step1::VariableDecl<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
) -> VariableDecl<'a> {
    let mut type_variable_names = type_variable_names.clone();
    VariableDecl {
        name: v.name,
        type_annotation: v.type_annotation.map(|(t, forall)| {
            type_variable_names.extend(
                forall
                    .type_variable_names
                    .into_iter()
                    .map(|s| (s, TypeVariable::new())),
            );
            type_to_type(t, data_decl_map, &type_variable_names)
                .into()
        }),
        value: expr(v.value, data_decl_map, &type_variable_names),
        decl_id: new_decl_id(),
    }
}

fn expr<'a>(
    e: ast_step1::Expr<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
) -> ExprWithType<'a> {
    use Expr::*;
    let e = match e {
        ast_step1::Expr::Lambda(arms) => Lambda(
            arms.into_iter()
                .map(move |arm| {
                    fn_arm(arm, data_decl_map, type_variable_names)
                })
                .collect(),
        ),
        ast_step1::Expr::Number(n) => Number(n),
        ast_step1::Expr::StrLiteral(s) => StrLiteral(s),
        ast_step1::Expr::Ident(name) => Ident {
            name,
            ident_id: new_ident_id(),
        },
        ast_step1::Expr::Decl(d) => Decl(Box::new(variable_decl(
            *d,
            data_decl_map,
            type_variable_names,
        ))),
        ast_step1::Expr::Call(f, a) => Call(
            Box::new(expr(*f, data_decl_map, type_variable_names)),
            Box::new(expr(*a, data_decl_map, type_variable_names)),
        ),
    };
    (e, TypeVariable::new())
}

fn fn_arm<'a>(
    arm: ast_step1::FnArm<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
) -> FnArm<'a> {
    FnArm {
        pattern: arm
            .pattern
            .into_iter()
            .map(|p| pattern(p, data_decl_map))
            .collect(),
        pattern_type: arm
            .pattern_type
            .into_iter()
            .map(|o| {
                o.map(|t| {
                    type_to_type(
                        t,
                        data_decl_map,
                        type_variable_names,
                    )
                })
            })
            .collect(),
        exprs: arm
            .exprs
            .into_iter()
            .map(|e| expr(e, data_decl_map, type_variable_names))
            .collect(),
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

impl ConstructorId<'_> {
    fn get<'a>(
        name: &'a str,
        data_decl_map: &FxHashMap<&str, DeclId>,
    ) -> ConstructorId<'a> {
        if let Some(id) = data_decl_map.get(name) {
            ConstructorId::DeclId(*id, name)
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
) -> Pattern<'a> {
    use Pattern::*;
    match p {
        ast_step1::Pattern::Number(n) => Number(n),
        ast_step1::Pattern::StrLiteral(s) => StrLiteral(s),
        ast_step1::Pattern::Constructor { name, args } => {
            Constructor {
                id: ConstructorId::get(name, data_decl_map),
                args: args
                    .into_iter()
                    .map(|arg| pattern(arg, data_decl_map))
                    .collect(),
            }
        }
        ast_step1::Pattern::Binder(name) => {
            Binder(name, new_decl_id())
        }
        ast_step1::Pattern::Underscore => Pattern::Underscore,
    }
}

pub fn type_to_type<'a>(
    t: ast_step1::Type<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
) -> Type<'a> {
    match t.name {
        "|" => t
            .args
            .into_iter()
            .flat_map(|a| {
                type_to_type(a, data_decl_map, type_variable_names)
            })
            .collect(),
        "->" => TypeUnit::Fn(
            type_to_type(
                t.args[0].clone(),
                data_decl_map,
                type_variable_names,
            ),
            type_to_type(
                t.args[1].clone(),
                data_decl_map,
                type_variable_names,
            ),
        )
        .into(),
        _ => {
            if let Some(n) = type_variable_names.get(t.name) {
                TypeUnit::Variable(*n).into()
            } else if let Some(i) = INTRINSIC_TYPES.get(&t.name) {
                TypeUnit::Normal {
                    name: t.name,
                    args: t
                        .args
                        .into_iter()
                        .map(|a| {
                            type_to_type(
                                a,
                                data_decl_map,
                                type_variable_names,
                            )
                        })
                        .collect(),
                    id: TypeId::Intrinsic(*i),
                }
                .into()
            } else {
                TypeUnit::Normal {
                    name: t.name,
                    args: t
                        .args
                        .into_iter()
                        .map(|a| {
                            type_to_type(
                                a,
                                data_decl_map,
                                type_variable_names,
                            )
                        })
                        .collect(),
                    id: TypeId::get(t.name, data_decl_map),
                }
                .into()
            }
        }
    }
}

impl std::fmt::Display for ConstructorId<'_> {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            ConstructorId::Intrinsic(a) => std::fmt::Debug::fmt(a, f),
            ConstructorId::DeclId(a, _) => a.fmt(f),
        }
    }
}
