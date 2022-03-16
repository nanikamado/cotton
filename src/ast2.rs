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
pub enum ConstructorIdent {
    DeclId(DeclId, String),
    Intrinsic(IntrinsicConstructor),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeIdent {
    DeclId(DeclId, String),
    Intrinsic(IntrinsicType),
}

#[derive(Debug, PartialEq)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: String,
    pub field_len: usize,
    pub decl_id: DeclId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IncompleteType {
    pub constructor: Type,
    pub requirements: Requirements,
}

#[derive(
    Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash,
)]
pub struct Requirements {
    pub variable_requirements: Vec<(String, Type, IdentId)>,
    pub subtype_relation: BTreeSet<(Type, Type)>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl {
    pub ident: String,
    pub type_annotation: Option<IncompleteType>,
    pub value: Expr,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Ident { name: String, ident_id: IdentId },
    Decl(Box<VariableDecl>),
    Call(Box<Expr>, Box<Expr>),
    Unit,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm {
    pub pattern: Vec<Pattern>,
    pub pattern_type: Vec<Option<Type>>,
    pub exprs: Vec<Expr>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern {
    Number(String),
    StrLiteral(String),
    Constructor {
        id: ConstructorIdent,
        args: Vec<Pattern>,
    },
    Binder(String, DeclId),
    Underscore,
}

impl From<ast1::Ast> for Ast {
    fn from(ast: ast1::Ast) -> Self {
        let data_decl: Vec<_> = ast
            .data_decl
            .into_iter()
            .map(|d| DataDecl {
                name: d.name,
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

impl ConstructorIdent {
    pub fn name(&self) -> &str {
        match self {
            ConstructorIdent::DeclId(_, name) => name,
            ConstructorIdent::Intrinsic(c) => c.to_str(),
        }
    }
}

impl TypeIdent {
    #[allow(unused)]
    pub fn name(&self) -> &str {
        match self {
            TypeIdent::DeclId(_, name) => name,
            TypeIdent::Intrinsic(c) => &INTRINSIC_TYPES_NAMES[c][..],
        }
    }
}

impl From<ConstructorIdent> for TypeIdent {
    fn from(c: ConstructorIdent) -> Self {
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

impl From<Type> for IncompleteType {
    fn from(t: Type) -> Self {
        Self {
            constructor: t,
            requirements: Requirements::default(),
        }
    }
}

fn variable_decl(
    v: ast1::VariableDecl,
    data_decl_map: &FxHashMap<&str, DeclId>,
    type_variable_names: &FxHashMap<String, usize>,
) -> VariableDecl {
    VariableDecl {
        ident: v.identifier,
        type_annotation: v.type_annotation.map(|(t, forall)| {
            let mut type_variable_names = type_variable_names.clone();
            type_variable_names.extend(
                forall
                    .type_variable_names
                    .into_iter()
                    .map(|s| (s, TypeUnit::new_variable_num())),
            );
            type_to_type(t, data_decl_map, &type_variable_names)
                .into()
        }),
        value: expr(v.value, data_decl_map, type_variable_names),
        decl_id: new_decl_id(),
    }
}

fn expr(
    e: ast1::Expr,
    data_decl_map: &FxHashMap<&str, DeclId>,
    type_variable_names: &FxHashMap<String, usize>,
) -> Expr {
    use Expr::*;
    match e {
        ast1::Expr::Lambda(arms) => Lambda(
            arms.into_iter()
                .map(|arm| {
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

fn fn_arm(
    arm: ast1::FnArm,
    data_decl_map: &FxHashMap<&str, DeclId>,
    type_variable_names: &FxHashMap<String, usize>,
) -> FnArm {
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

impl TypeIdent {
    fn get(
        name: &str,
        data_decl_map: &FxHashMap<&str, DeclId>,
    ) -> TypeIdent {
        if let Some(id) = data_decl_map.get(name) {
            TypeIdent::DeclId(*id, name.to_string())
        } else if let Some(i) = INTRINSIC_TYPES.get(name) {
            TypeIdent::Intrinsic(*i)
        } else {
            panic!("{:?} not fould", name)
        }
    }
}

impl ConstructorIdent {
    fn get(
        name: &str,
        data_decl_map: &FxHashMap<&str, DeclId>,
    ) -> ConstructorIdent {
        if let Some(id) = data_decl_map.get(name) {
            ConstructorIdent::DeclId(*id, name.to_string())
        } else if let Some(i) = INTRINSIC_CONSTRUCTORS.get(name) {
            ConstructorIdent::Intrinsic(*i)
        } else {
            panic!("{:?} not fould", name)
        }
    }
}

fn pattern(
    p: ast1::Pattern,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> Pattern {
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

pub fn type_to_type(
    t: ast1::Type,
    data_decl_map: &FxHashMap<&str, DeclId>,
    type_variable_names: &FxHashMap<String, usize>,
) -> Type {
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
