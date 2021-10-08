use crate::ast0;
use itertools::Itertools;
use once_cell::sync::Lazy;
use std::{
    collections::{BTreeSet, HashMap, HashSet, VecDeque},
    iter::FromIterator,
};

#[derive(Debug, PartialEq)]
pub struct Ast {
    pub declarations: Vec<Declaration>,
    pub data_declarations: Vec<ast0::DataDeclaration>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    Normal(String, Vec<Type>),
    Fn(Box<Type>, Box<Type>),
    Union(Union),
    Variable(usize),
    Empty,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Union(BTreeSet<Type>);

impl IntoIterator for Union {
    type Item = Type;

    type IntoIter = std::collections::btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Union {
    pub fn iter(
        &self,
    ) -> std::collections::btree_set::Iter<'_, Type> {
        self.0.iter()
    }

    pub fn contains(&self, value: &Type) -> bool {
        self.0.contains(value)
    }
}

impl FromIterator<Type> for Type {
    fn from_iter<T: IntoIterator<Item = Type>>(iter: T) -> Self {
        let mut u = BTreeSet::new();
        for t in iter {
            match t {
                Type::Union(Union(a)) => u.extend(a),
                Type::Empty => (),
                other => {
                    u.insert(other);
                }
            }
        }
        match u.len() {
            0 => Type::Empty,
            1 => u.into_iter().next().unwrap(),
            _ => Type::Union(Union(u)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct IncompleteType {
    pub constructor: Type,
    pub requirements: Requirements,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Requirements {
    pub variable_requirements: Vec<(String, Type)>,
    pub subtype_relation: BTreeSet<(Type, Type)>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Declaration {
    pub identifier: String,
    pub type_annotation: Option<IncompleteType>,
    pub value: Expr,
}

impl From<ast0::Declaration> for Declaration {
    fn from(d: ast0::Declaration) -> Self {
        Self {
            identifier: d.identifier,
            type_annotation: d.type_annotation.map(|t| t.into()),
            value: d.value.into(),
        }
    }
}

impl From<(ast0::InfixTypeSequence, ast0::Forall)>
    for IncompleteType
{
    fn from(
        (t, forall): (ast0::InfixTypeSequence, ast0::Forall),
    ) -> Self {
        let mut t: Type = t.into();
        for v in forall.type_variable_names {
            t = t.replace_type(
                &Type::Normal(v, Vec::new()),
                &Type::new_variable(),
            );
        }
        t.into()
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
    .copied()
    .collect()
});

static RIGHT_ASSOCIATIVE: Lazy<HashSet<i32>> =
    Lazy::new(|| [1].iter().copied().collect());

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
        type_annotation: d.type_annotation.map(|t| t.into()),
        value: d.value.into(),
    }
}

impl From<ast0::OpSequence> for Expr {
    fn from(s: ast0::OpSequence) -> Self {
        let op_list: BTreeSet<_> = s
            .operators
            .iter()
            .map(|s| {
                *OP_PRECEDENCE.get(&s[..]).unwrap_or_else(|| {
                    panic!("no entry found for key: {}", s)
                })
            })
            .collect();
        let mut operators = s.operators.into_iter().collect();
        let mut operands: VecDeque<Expr> =
            s.operands.into_iter().map(|o| o.into()).collect();
        for a in op_list.into_iter().rev() {
            if RIGHT_ASSOCIATIVE.contains(&a) {
                unimplemented!()
            } else {
                let os = value_op_apply_left(operators, operands, a);
                operators = os.0;
                operands = os.1;
            }
        }
        operands[0].clone()
    }
}

fn value_op_apply_left(
    mut operators: VecDeque<String>,
    mut operands: VecDeque<Expr>,
    precedence: i32,
) -> (VecDeque<String>, VecDeque<Expr>) {
    if let Some(op) = operators.pop_front() {
        let head = operands.pop_front().unwrap();
        if OP_PRECEDENCE[&op[..]] == precedence {
            let head_ = operands.pop_front().unwrap();
            let new_elm = if op == "fn_call" {
                Expr::Call(head.into(), head_.into())
            } else {
                Expr::Call(
                    Expr::Call(
                        Expr::Identifier(op).into(),
                        head.into(),
                    )
                    .into(),
                    head_.into(),
                )
            };
            operands.push_front(new_elm);
            value_op_apply_left(operators, operands, precedence)
        } else {
            let (mut operators, mut operands) =
                value_op_apply_left(operators, operands, precedence);
            operators.push_front(op);
            operands.push_front(head);
            (operators, operands)
        }
    } else {
        (operators, operands)
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
            .iter()
            .map(|s| {
                *OP_PRECEDENCE.get(&s[..]).unwrap_or_else(|| {
                    panic!("no entry found for key: {}", s)
                })
            })
            .collect();
        let mut operators = s.operators.into_iter().collect();
        let mut operands: VecDeque<Type> =
            s.operands.into_iter().map(|o| o.into()).collect();
        for a in op_list.into_iter().rev() {
            if RIGHT_ASSOCIATIVE.contains(&a) {
                let os = type_op_apply_right(operators, operands, a);
                operators = os.0;
                operands = os.1;
            } else {
                let os = type_op_apply_left(operators, operands, a);
                operators = os.0;
                operands = os.1;
            }
        }
        operands[0].clone()
    }
}

fn type_op_apply_right(
    mut operators: VecDeque<String>,
    mut operands: VecDeque<Type>,
    precedence: i32,
) -> (VecDeque<String>, VecDeque<Type>) {
    if let Some(op) = operators.pop_back() {
        let last = operands.pop_back().unwrap();
        if OP_PRECEDENCE[&op[..]] == precedence {
            let last_ = operands.pop_back().unwrap();
            let new_elm = if op == "type_call" {
                unimplemented!()
            } else if op == "->" {
                Type::Fn(Box::new(last_), Box::new(last))
            } else {
                Type::Normal(op, vec![last_, last])
            };
            operands.push_back(new_elm);
            type_op_apply_right(operators, operands, precedence)
        } else {
            let (mut operators, mut operands) =
                type_op_apply_right(operators, operands, precedence);
            operators.push_back(op);
            operands.push_back(last);
            (operators, operands)
        }
    } else {
        (operators, operands)
    }
}

fn type_op_apply_left(
    mut operators: VecDeque<String>,
    mut operands: VecDeque<Type>,
    precedence: i32,
) -> (VecDeque<String>, VecDeque<Type>) {
    if let Some(op) = operators.pop_front() {
        let head = operands.pop_front().unwrap();
        if OP_PRECEDENCE[&op[..]] == precedence {
            let head_ = operands.pop_front().unwrap();
            let new_elm = if op == "type_call" {
                if let Type::Normal(n, mut args) = head {
                    args.push(head_);
                    Type::Normal(n, args)
                } else {
                    unimplemented!()
                }
            } else if op == "->" {
                Type::Fn(Box::new(head), Box::new(head_))
            } else if op == "|" {
                head.union_with(head_)
            } else {
                Type::Normal(op, vec![head, head_])
            };
            operands.push_front(new_elm);
            type_op_apply_left(operators, operands, precedence)
        } else {
            let (mut operators, mut operands) =
                type_op_apply_left(operators, operands, precedence);
            operators.push_front(op);
            operands.push_front(head);
            (operators, operands)
        }
    } else {
        (operators, operands)
    }
}
