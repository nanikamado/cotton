pub mod decl_id;
pub mod ident_id;
pub mod types;

use self::decl_id::{new_decl_id, DeclId};
use self::ident_id::{new_ident_id, IdentId};
use self::types::{Type, TypeUnit};
use crate::type_check::intrinsics::INTRINSIC_TYPES_NAMES;
use crate::{
    ast1,
    type_check::intrinsics::{
        IntrinsicConstructor, IntrinsicType, INTRINSIC_CONSTRUCTORS,
        INTRINSIC_TYPES,
    },
};
use fxhash::FxHashMap;
use std::collections::BTreeSet;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstructorIdent<'a> {
    DeclId(DeclId, &'a str),
    Intrinsic(IntrinsicConstructor),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeIdent<'a> {
    DeclId(DeclId, &'a str),
    Intrinsic(IntrinsicType),
}

#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl<'a> {
    pub name: &'a str,
    pub field_len: usize,
    pub decl_id: DeclId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IncompleteType<'a> {
    pub constructor: Type<'a>,
    pub requirements: Requirements<'a>,
}

#[derive(
    Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash,
)]
pub struct Requirements<'a> {
    pub variable_requirements: Vec<(&'a str, Type<'a>, IdentId)>,
    pub subtype_relation: BTreeSet<(Type<'a>, Type<'a>)>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub ident: &'a str,
    pub type_annotation: Option<IncompleteType<'a>>,
    pub value: Expr<'a>,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident { name: &'a str, ident_id: IdentId },
    Decl(Box<VariableDecl<'a>>),
    Call(Box<Expr<'a>>, Box<Expr<'a>>),
    Unit,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub pattern_type: Vec<Option<Type<'a>>>,
    pub exprs: Vec<Expr<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern<'a> {
    Number(&'a str),
    StrLiteral(&'a str),
    Constructor {
        id: ConstructorIdent<'a>,
        args: Vec<Pattern<'a>>,
    },
    Binder(&'a str, DeclId),
    Underscore,
}

impl<'a> From<ast1::Ast<'a>> for Ast<'a> {
    fn from(ast: ast1::Ast<'a>) -> Self {
        let data_decl: Vec<_> = ast
            .data_decl
            .into_iter()
            .map(|d| DataDecl {
                name: &d.name,
                field_len: d.field_len,
                decl_id: new_decl_id(),
            })
            .collect();
        let data_decl_map: FxHashMap<&str, DeclId> = data_decl
            .iter()
            .map(|d| (&d.name[..], d.decl_id))
            .collect();
        let variable_decl: Vec<_> = ast
            .variable_decl
            .into_iter()
            .map(|d| {
                variable_decl(d, &data_decl_map, &Default::default())
            })
            .collect();
        let entry_point = variable_decl
            .iter()
            .find(|d| d.ident == "main")
            .unwrap_or_else(|| panic!("entry point not found"))
            .decl_id;
        Self {
            variable_decl,
            data_decl,
            entry_point,
        }
    }
}

impl ConstructorIdent<'_> {
    pub fn name(&self) -> &str {
        match self {
            ConstructorIdent::DeclId(_, name) => name,
            ConstructorIdent::Intrinsic(c) => c.to_str(),
        }
    }
}

impl TypeIdent<'_> {
    #[allow(unused)]
    pub fn name(&self) -> &str {
        match self {
            TypeIdent::DeclId(_, name) => name,
            TypeIdent::Intrinsic(c) => &INTRINSIC_TYPES_NAMES[c][..],
        }
    }
}

impl<'a> From<ConstructorIdent<'a>> for TypeIdent<'a> {
    fn from(c: ConstructorIdent<'a>) -> Self {
        match c {
            ConstructorIdent::DeclId(ident, name) => {
                Self::DeclId(ident, name)
            }
            ConstructorIdent::Intrinsic(i) => {
                Self::Intrinsic(i.into())
            }
        }
    }
}

impl<'a> From<Type<'a>> for IncompleteType<'a> {
    fn from(t: Type<'a>) -> Self {
        Self {
            constructor: t,
            requirements: Requirements::default(),
        }
    }
}

fn variable_decl<'a>(
    v: ast1::VariableDecl<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, usize>,
) -> VariableDecl<'a> {
    let mut type_variable_names = type_variable_names.clone();
    VariableDecl {
        ident: v.identifier,
        type_annotation: v.type_annotation.map(|(t, forall)| {
            type_variable_names.extend(
                forall
                    .type_variable_names
                    .into_iter()
                    .map(|s| (s, TypeUnit::new_variable_num())),
            );
            type_to_type(t, data_decl_map, &type_variable_names)
                .into()
        }),
        value: expr(v.value, data_decl_map, &type_variable_names),
        decl_id: new_decl_id(),
    }
}

fn expr<'a>(
    e: ast1::Expr<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, usize>,
) -> Expr<'a> {
    use Expr::*;
    match e {
        ast1::Expr::Lambda(arms) => Lambda(
            arms.into_iter()
                .map(move |arm| {
                    fn_arm(arm, data_decl_map, type_variable_names)
                })
                .collect(),
        ),
        ast1::Expr::Number(n) => Number(n),
        ast1::Expr::StrLiteral(s) => StrLiteral(s),
        ast1::Expr::Ident(name) => Ident {
            name,
            ident_id: new_ident_id(),
        },
        ast1::Expr::Decl(d) => Decl(Box::new(variable_decl(
            *d,
            data_decl_map,
            type_variable_names,
        ))),
        ast1::Expr::Call(f, a) => Call(
            Box::new(expr(*f, data_decl_map, type_variable_names)),
            Box::new(expr(*a, data_decl_map, type_variable_names)),
        ),
        ast1::Expr::Unit => Unit,
    }
}

fn fn_arm<'a>(
    arm: ast1::FnArm<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, usize>,
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

impl TypeIdent<'_> {
    fn get<'a>(
        name: &'a str,
        data_decl_map: &FxHashMap<&str, DeclId>,
    ) -> TypeIdent<'a> {
        if let Some(id) = data_decl_map.get(name) {
            TypeIdent::DeclId(*id, name)
        } else if let Some(i) = INTRINSIC_TYPES.get(name) {
            TypeIdent::Intrinsic(*i)
        } else {
            panic!("{:?} not fould", name)
        }
    }
}

impl ConstructorIdent<'_> {
    fn get<'a>(
        name: &'a str,
        data_decl_map: &FxHashMap<&str, DeclId>,
    ) -> ConstructorIdent<'a> {
        if let Some(id) = data_decl_map.get(name) {
            ConstructorIdent::DeclId(*id, name)
        } else if let Some(i) = INTRINSIC_CONSTRUCTORS.get(name) {
            ConstructorIdent::Intrinsic(*i)
        } else {
            panic!("{:?} not fould", name)
        }
    }
}

fn pattern<'a>(
    p: ast1::Pattern<'a>,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> Pattern<'a> {
    use Pattern::*;
    match p {
        ast1::Pattern::Number(n) => Number(n),
        ast1::Pattern::StrLiteral(s) => StrLiteral(s),
        ast1::Pattern::Constructor { name, args } => Constructor {
            id: ConstructorIdent::get(&name, data_decl_map),
            args: args
                .into_iter()
                .map(|arg| pattern(arg, data_decl_map))
                .collect(),
        },
        ast1::Pattern::Binder(name) => Binder(name, new_decl_id()),
        ast1::Pattern::Underscore => Pattern::Underscore,
    }
}

pub fn type_to_type<'a>(
    t: ast1::Type<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, usize>,
) -> Type<'a> {
    match &t.name[..] {
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
            if let Some(n) = type_variable_names.get(&t.name[..]) {
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
                    id: TypeIdent::Intrinsic(*i),
                }
                .into()
            } else {
                TypeUnit::Normal {
                    name: t.name.clone(),
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
                    id: TypeIdent::get(&t.name, data_decl_map),
                }
                .into()
            }
        }
    }
}
