use crate::ast0;
use itertools::Itertools;
use once_cell::sync::Lazy;
use std::collections::{BTreeSet, HashMap};

#[derive(Debug, PartialEq)]
pub struct Ast {
    pub declarations: Vec<Declaration>,
    pub data_declarations: Vec<ast0::DataDeclaration>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Declaration {
    pub identifier: String,
    pub datatype: Option<Type>,
    pub value: Expr,
}

impl From<ast0::Declaration> for Declaration {
    fn from(d: ast0::Declaration) -> Self {
        Self {
            identifier: d.identifier,
            datatype: d.datatype.map(|t| t.into()),
            value: d.value.into(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Identifier(String),
    Declaration(Box<Declaration>),
    Call(Box<Expr>, Box<Expr>),
    Unit,
}

impl From<ast0::Expr> for Expr {
    fn from(ast_expr: ast0::Expr) -> Self {
        use Expr::*;
        match ast_expr {
            ast0::Expr::Lambda(a) => {
                Lambda(a.into_iter().map(|f| f.into()).collect())
            }
            ast0::Expr::Number(a) => Number(a),
            ast0::Expr::StrLiteral(a) => StrLiteral(a),
            ast0::Expr::Identifier(a) => Identifier(a),
            ast0::Expr::Declaration(a) => {
                Declaration(Box::new((*a).into()))
            }
            ast0::Expr::Unit => Unit,
            ast0::Expr::Paren(a) => a.into(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm {
    pub pattern: Vec<ast0::Pattern>,
    pub pattern_type: Vec<Option<Type>>,
    pub exprs: Vec<Expr>,
}

fn infix_constructor_sequence_to_pattern(
    s: ast0::InfixConstructorSequence,
) -> ast0::Pattern {
    let op_list: BTreeSet<_> =
        s.operators.iter().map(|s| OP_PRECEDENCE[&s[..]]).collect();
    let mut operators = s.operators;
    let mut operands: Vec<ast0::Pattern> = s.operands;
    for a in op_list.into_iter().rev() {
        let mut operand_head = 0;
        for i in 0..operators.len() {
            let op = operators[i].clone();
            if a == OP_PRECEDENCE[&op[..]] {
                operands[operand_head] = ast0::Pattern::Constructor(
                    op,
                    vec![
                        operands[operand_head].clone(),
                        operands[i + 1].clone(),
                    ],
                );
            } else {
                operand_head += 1;
                operands[operand_head] = operands[i + 1].clone();
            }
        }
        operators.retain(|o| OP_PRECEDENCE[&o[..]] != a);
    }
    operands[0].clone()
}

impl From<ast0::FnArm> for FnArm {
    fn from(ast_fn_arm: ast0::FnArm) -> Self {
        Self {
            pattern: ast_fn_arm
                .pattern
                .into_iter()
                .map(infix_constructor_sequence_to_pattern)
                .collect(),
            pattern_type: ast_fn_arm
                .pattern_type
                .into_iter()
                .map(|a| a.map(|a| a.into()))
                .collect(),
            exprs: ast_fn_arm
                .exprs
                .into_iter()
                .map(Expr::from)
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Operator(String);

static OP_PRECEDENCE: Lazy<HashMap<&str, i32>> = Lazy::new(|| {
    [
        ("fn_call", 10),
        ("type_call", 10),
        (".", 10),
        ("%", 7),
        ("+", 6),
        ("-", 6),
        ("<", 5),
        ("!=", 5),
        ("..", 4),
        ("/\\", 3),
        ("|", 2),
        ("->", 1),
        ("$", 0),
    ]
    .iter()
    .cloned()
    .collect()
});

impl Ord for Operator {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        OP_PRECEDENCE[&self.0[..]].cmp(&OP_PRECEDENCE[&other.0[..]])
    }
}

impl PartialOrd for Operator {
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl From<ast0::Ast> for Ast {
    fn from(ast: ast0::Ast) -> Self {
        let (vs, ds) = ast
            .declarations
            .into_iter()
            .map(|d| match d {
                ast0::Dec::Variable(a) => Ok(declaration(a)),
                ast0::Dec::Data(a) => Err(a),
            })
            .partition_result();
        Ast {
            declarations: vs,
            data_declarations: ds,
        }
    }
}

fn declaration(d: ast0::Declaration) -> Declaration {
    Declaration {
        identifier: d.identifier,
        datatype: d.datatype.map(|t| t.into()),
        value: d.value.into(),
    }
}

impl From<ast0::OpSequence> for Expr {
    fn from(s: ast0::OpSequence) -> Self {
        let op_list: BTreeSet<_> = s
            .operators
            .clone()
            .into_iter()
            .map(|s| {
                *OP_PRECEDENCE.get(&s[..]).unwrap_or_else(|| {
                    panic!("no entry found for key: {}", s)
                })
            })
            .collect();
        let mut operators = s.operators;
        let mut operands: Vec<Expr> =
            s.operands.into_iter().map(|o| o.into()).collect();
        for a in op_list.into_iter().rev() {
            let mut operand_head = 0;
            for i in 0..operators.len() {
                let op = operators[i].clone();
                if a == OP_PRECEDENCE[&op[..]] {
                    operands[operand_head] = Expr::Call(
                        Box::new(if op == *"fn_call" {
                            operands[operand_head].clone()
                        } else {
                            Expr::Call(
                                Box::new(Expr::Identifier(op)),
                                Box::new(
                                    operands[operand_head].clone(),
                                ),
                            )
                        }),
                        Box::new(operands[i + 1].clone()),
                    );
                } else {
                    operand_head += 1;
                    operands[operand_head] = operands[i + 1].clone();
                }
            }
            operators.retain(|o| OP_PRECEDENCE[&o[..]] != a);
        }
        operands[0].clone()
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Normal(String, Vec<Type>),
    Fn(Vec<FnArmType>),
    Union(Box<Type>, Box<Type>),
    Anonymous(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FnArmType(pub Type, pub Type);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct IncompleteType {
    pub constructor: Type,
    pub requirements: Requirements,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Requirements {
    pub variable_requirements: Vec<(String, Type)>,
    pub subtype_relationship: Vec<(Type, Type)>,
}

impl From<Type> for IncompleteType {
    fn from(t: Type) -> Self {
        Self {
            constructor: t,
            requirements: Requirements::default(),
        }
    }
}

impl From<ast0::Datatype> for Type {
    fn from(t: ast0::Datatype) -> Self {
        match t {
            ast0::Datatype::Identifier(s) => {
                Type::Normal(s, Vec::new())
            }
            ast0::Datatype::Paren(s) => s.into(),
        }
    }
}

impl From<ast0::InfixTypeSequence> for Type {
    fn from(s: ast0::InfixTypeSequence) -> Self {
        let op_list: BTreeSet<_> = s
            .operators
            .clone()
            .into_iter()
            .map(|s| {
                *OP_PRECEDENCE.get(&s[..]).unwrap_or_else(|| {
                    panic!("no entry found for key: {}", s)
                })
            })
            .collect();
        let mut operators = s.operators;
        let mut operands: Vec<Type> =
            s.operands.into_iter().map(|o| o.into()).collect();
        for a in op_list.into_iter().rev() {
            let mut operand_head = 0;
            for i in 0..operators.len() {
                let op = operators[i].clone();
                if a == OP_PRECEDENCE[&op[..]] {
                    operands[operand_head] = if op == *"type_call" {
                        unimplemented!()
                    } else if op == *"->" {
                        Type::Fn(vec![FnArmType(
                            operands[operand_head].clone(),
                            operands[i + 1].clone(),
                        )])
                    } else {
                        Type::Normal(
                            op,
                            vec![
                                operands[operand_head].clone(),
                                operands[i + 1].clone(),
                            ],
                        )
                    }
                } else {
                    operand_head += 1;
                    operands[operand_head] = operands[i + 1].clone();
                }
            }
            operators.retain(|o| OP_PRECEDENCE[&o[..]] != a);
        }
        operands[0].clone()
    }
}
