use crate::{
    ast0,
    ast1::{
        decl_id::{new_decl_id, DeclId},
        types::TypeUnit,
    },
    type_check::intrinsics::{
        IntrinsicConstructor, IntrinsicType, INTRINSIC_CONSTRUCTORS,
        INTRINSIC_TYPES, INTRINSIC_TYPES_NAMES,
    },
};
use fxhash::FxHashMap;
use itertools::Itertools;

#[derive(Debug, PartialEq, Eq)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub identifier: String,
    pub type_annotation: Option<InfixTypeSequence>,
    pub value: OpSequence,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeIdent {
    DeclId(DeclId, String),
    Intrinsic(IntrinsicType),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstructorIdent {
    DeclId(DeclId, String),
    Intrinsic(IntrinsicConstructor),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type {
    Identifier(TypeIdent),
    Variable(usize),
    Paren(InfixTypeSequence),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InfixTypeSequence {
    pub operators: Vec<TypeIdent>,
    pub operands: Vec<Type>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: String,
    pub field_len: usize,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Identifier(String),
    Declaration(Box<VariableDecl>),
    Unit,
    Paren(OpSequence),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OpSequence {
    pub operators: Vec<String>,
    pub operands: Vec<Expr>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm {
    pub pattern: Vec<InfixConstructorSequence>,
    pub pattern_type: Vec<Option<InfixTypeSequence>>,
    pub exprs: Vec<OpSequence>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InfixConstructorSequence {
    pub operators: Vec<ConstructorIdent>,
    pub operands: Vec<Pattern>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern {
    Number(String),
    StrLiteral(String),
    Constructor {
        id: ConstructorIdent,
        name: String,
        args: Vec<Pattern>,
    },
    Binder(String),
    Underscore,
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

impl From<ast0::Ast> for Ast {
    fn from(ast: ast0::Ast) -> Self {
        let (vs, ds): (Vec<_>, Vec<_>) = ast
            .declarations
            .into_iter()
            .map(|d| match d {
                ast0::Decl::Variable(a) => Ok(a),
                ast0::Decl::Data(a) => Err(DataDecl {
                    name: a.name,
                    field_len: a.field_len,
                    decl_id: new_decl_id(),
                }),
            })
            .partition_result();
        let data_decl_map: FxHashMap<&str, DeclId> =
            ds.iter().map(|d| (&d.name[..], d.decl_id)).collect();
        Ast {
            variable_decl: vs
                .into_iter()
                .map(|v| variable_decl(v, &data_decl_map))
                .collect(),
            data_decl: ds,
        }
    }
}

fn variable_decl(
    v: ast0::VariableDecl,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> VariableDecl {
    VariableDecl {
        identifier: v.identifier,
        type_annotation: v.type_annotation.map(|(s, forall)| {
            let type_variables: FxHashMap<String, usize> = forall
                .type_variable_names
                .into_iter()
                .map(|name| (name, TypeUnit::new_variable_num()))
                .collect();
            infix_type_sequence(s, &type_variables, data_decl_map)
        }),
        value: op_sequence(v.value, data_decl_map),
    }
}

fn get_type_id(
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

pub fn infix_type_sequence(
    s: ast0::InfixTypeSequence,
    type_variables: &FxHashMap<String, usize>,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> InfixTypeSequence {
    InfixTypeSequence {
        operators: s
            .operators
            .into_iter()
            .map(|o| get_type_id(&o, data_decl_map))
            .collect(),
        operands: s
            .operands
            .into_iter()
            .map(|t| type_to_type(t, data_decl_map, type_variables))
            .collect(),
    }
}

fn type_to_type(
    t: ast0::Type,
    data_decl_map: &FxHashMap<&str, DeclId>,
    type_variables: &FxHashMap<String, usize>,
) -> Type {
    match t {
        ast0::Type::Identifier(name) => {
            if let Some(id) = data_decl_map.get(&name[..]) {
                Type::Identifier(TypeIdent::DeclId(*id, name))
            } else if let Some(i) = INTRINSIC_TYPES.get(&name[..]) {
                Type::Identifier(TypeIdent::Intrinsic(*i))
            } else if let Some(n) = type_variables.get(&name) {
                Type::Variable(*n)
            } else {
                panic!()
            }
        }
        ast0::Type::Paren(s) => Type::Paren(infix_type_sequence(
            s,
            type_variables,
            data_decl_map,
        )),
    }
}

fn op_sequence(
    s: ast0::OpSequence,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> OpSequence {
    OpSequence {
        operators: s.operators,
        operands: s
            .operands
            .into_iter()
            .map(|e| expr(e, data_decl_map))
            .collect(),
    }
}

fn expr(
    e: ast0::Expr,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> Expr {
    use Expr::*;
    match e {
        ast0::Expr::Lambda(arms) => Lambda(
            arms.into_iter()
                .map(|a| fn_arm(a, data_decl_map))
                .collect(),
        ),
        ast0::Expr::Number(a) => Number(a),
        ast0::Expr::StrLiteral(a) => StrLiteral(a),
        ast0::Expr::Identifier(a) => Identifier(a),
        ast0::Expr::Declaration(a) => {
            Declaration(Box::new(variable_decl(*a, data_decl_map)))
        }
        ast0::Expr::Unit => Unit,
        ast0::Expr::Paren(a) => Paren(op_sequence(a, data_decl_map)),
    }
}

fn fn_arm(
    a: ast0::FnArm,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> FnArm {
    FnArm {
        pattern: a
            .pattern
            .into_iter()
            .map(|s| infix_constructor_sequence(s, data_decl_map))
            .collect(),
        pattern_type: a
            .pattern_type
            .into_iter()
            .map(|t| {
                t.map(|t| {
                    infix_type_sequence(
                        t,
                        &Default::default(),
                        data_decl_map,
                    )
                })
            })
            .collect(),
        exprs: a
            .exprs
            .into_iter()
            .map(|e| op_sequence(e, data_decl_map))
            .collect(),
    }
}

fn get_constructor_id(
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

fn pattern_to_pattern(
    pattern: ast0::Pattern,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> Pattern {
    match pattern {
        ast0::Pattern::Number(a) => Pattern::Number(a),
        ast0::Pattern::StrLiteral(a) => Pattern::StrLiteral(a),
        ast0::Pattern::Constructor(name, ps) => {
            Pattern::Constructor {
                id: get_constructor_id(&name, data_decl_map),
                name,
                args: ps
                    .into_iter()
                    .map(|p| pattern_to_pattern(p, data_decl_map))
                    .collect(),
            }
        }
        ast0::Pattern::Binder(a) => Pattern::Binder(a),
        ast0::Pattern::Underscore => Pattern::Underscore,
    }
}

fn infix_constructor_sequence(
    s: ast0::InfixConstructorSequence,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> InfixConstructorSequence {
    InfixConstructorSequence {
        operators: s
            .operators
            .into_iter()
            .map(|o| get_constructor_id(&o, data_decl_map))
            .collect(),
        operands: s
            .operands
            .into_iter()
            .map(|t| pattern_to_pattern(t, data_decl_map))
            .collect(),
    }
}
