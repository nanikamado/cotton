use crate::{
    ast0::{self, Associativity, Forall, OperatorPrecedence},
    type_check::intrinsics::OP_PRECEDENCE,
};
use fxhash::FxHashMap;
use index_list::{Index, IndexList};
use std::{
    collections::BTreeMap,
    fmt::{self, Debug},
};

#[derive(Debug, PartialEq, Eq)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub identifier: String,
    pub type_annotation: Option<(Type, Forall)>,
    pub value: Expr,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type {
    pub name: String,
    pub args: Vec<Type>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: String,
    pub field_len: usize,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Ident(String),
    Decl(Box<VariableDecl>),
    Call(Box<Expr>, Box<Expr>),
    Unit,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm {
    pub pattern: Vec<Pattern>,
    pub pattern_type: Vec<Option<Type>>,
    pub exprs: Vec<Expr>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern {
    Number(String),
    StrLiteral(String),
    Constructor { name: String, args: Vec<Pattern> },
    Binder(String),
    Underscore,
}

pub type TypeOperatorSequence = Vec<OpSequenceUnit<Type>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OpSequenceUnit<T> {
    Operand(T),
    Operator(String, Associativity, i32),
    Apply(T),
}

#[derive(Debug, Clone, Default)]
pub struct OpPrecedenceMap(FxHashMap<String, (Associativity, i32)>);

impl OpPrecedenceMap {
    pub fn new(m: FxHashMap<String, (Associativity, i32)>) -> Self {
        OpPrecedenceMap(m)
    }

    fn get(&self, name: &str) -> (Associativity, i32) {
        *self.0.get(name).unwrap_or_else(|| {
            panic!("key {:?} not found in {:?}", name, self.0)
        })
    }
}

pub trait InfixOpCall {
    fn infix_op_call(op_name: String, e1: Self, e2: Self) -> Self;
}

pub trait IdentFromString {
    fn ident_from_string(s: String) -> Self;
}

pub trait AddArgument {
    fn add_argument(self, arg: Self) -> Self;
}

impl IdentFromString for Type {
    fn ident_from_string(s: String) -> Self {
        Self {
            name: s,
            args: Vec::new(),
        }
    }
}

impl AddArgument for Type {
    fn add_argument(mut self, arg: Self) -> Self {
        self.args.push(arg);
        self
    }
}

impl IdentFromString for Expr {
    fn ident_from_string(s: String) -> Self {
        Self::Ident(s)
    }
}

impl AddArgument for Expr {
    fn add_argument(self, arg: Self) -> Self {
        Self::Call(self.into(), arg.into())
    }
}

impl IdentFromString for Pattern {
    fn ident_from_string(name: String) -> Self {
        Self::Constructor {
            name,
            args: Vec::new(),
        }
    }
}

impl AddArgument for Pattern {
    fn add_argument(self, arg: Self) -> Self {
        if let Pattern::Constructor { name, mut args } = self {
            args.push(arg);
            Pattern::Constructor { name, args }
        } else {
            panic!()
        }
    }
}

impl<T> OpSequenceUnit<T> {
    pub fn operator_precedence(&self) -> Option<i32> {
        match self {
            OpSequenceUnit::Operand(_) => None,
            OpSequenceUnit::Operator(_, _, p) => Some(*p),
            OpSequenceUnit::Apply(_) => Some(10),
        }
    }
}

impl From<ast0::Ast> for Ast {
    fn from(ast: ast0::Ast) -> Self {
        let mut vs = Vec::new();
        let mut ds = Vec::new();
        let mut precedence_map = OP_PRECEDENCE.clone();
        for d in ast.decls {
            match d {
                ast0::Decl::Variable(a) => vs.push(a),
                ast0::Decl::Data(a) => ds.push(DataDecl {
                    name: a.name,
                    field_len: a.field_len,
                }),
                ast0::Decl::Precedence(OperatorPrecedence {
                    name,
                    associativity,
                    precedence,
                }) => {
                    precedence_map
                        .insert(name, (associativity, precedence));
                }
            }
        }
        let op_precedence_map = OpPrecedenceMap::new(precedence_map);
        Ast {
            variable_decl: vs
                .into_iter()
                .map(|v| variable_decl(v, &op_precedence_map))
                .collect(),
            data_decl: ds,
        }
    }
}

fn variable_decl(
    v: ast0::VariableDecl,
    op_precedence_map: &OpPrecedenceMap,
) -> VariableDecl {
    VariableDecl {
        identifier: v.identifier,
        type_annotation: v.type_annotation.map(|(s, forall)| {
            (
                infix_op_sequence(op_sequence(s, op_precedence_map)),
                forall,
            )
        }),
        value: infix_op_sequence(op_sequence(
            v.value,
            op_precedence_map,
        )),
    }
}

fn apply_type_op<T: AddArgument + IdentFromString + Clone + Debug>(
    mut sequence: IndexList<OpSequenceUnit<T>>,
    i: Index,
) -> IndexList<OpSequenceUnit<T>> {
    let i_prev = sequence.prev_index(i);
    let i_next = sequence.next_index(i);
    let s_i = sequence.get(i).cloned();
    let s_i_next = sequence.get(i_next).cloned();
    match s_i {
        Some(OpSequenceUnit::Operator(name, _, _)) => {
            match sequence.get_mut(i_prev).unwrap() {
                OpSequenceUnit::Operand(e1) => {
                    if let OpSequenceUnit::Operand(e2) =
                        s_i_next.unwrap()
                    {
                        *e1 = T::ident_from_string(name)
                            .add_argument(e1.clone())
                            .add_argument(e2);
                    } else {
                        panic!()
                    }
                    sequence.remove(i);
                    sequence.remove(i_next);
                }
                OpSequenceUnit::Apply(_) => {
                    sequence = apply_type_op(sequence, i_prev);
                    sequence = apply_type_op(sequence, i);
                }
                _ => panic!(),
            }
        }
        Some(OpSequenceUnit::Apply(a)) => {
            match sequence.get_mut(i_prev).unwrap() {
                OpSequenceUnit::Operand(e) => {
                    *e = e.clone().add_argument(a);
                    sequence.remove(i);
                }
                OpSequenceUnit::Apply(_) => {
                    sequence = apply_type_op(sequence, i_prev);
                    sequence = apply_type_op(sequence, i);
                }
                _ => panic!(),
            }
        }
        None => panic!("specified index is not varid."),
        Some(OpSequenceUnit::Operand(a)) => {
            panic!("specified position is a operand {:?}", a)
        }
    }
    sequence
}

fn op_apply_left<T: AddArgument + IdentFromString + Clone + Debug>(
    mut sequence: Vec<OpSequenceUnit<T>>,
    precedence: i32,
) -> Vec<OpSequenceUnit<T>> {
    let mut sequence = IndexList::from(&mut sequence);
    let mut i = sequence.first_index();
    loop {
        let next_i = sequence.next_index(i);
        if let Some(u) = sequence.get(next_i) {
            match u.operator_precedence() {
                Some(p) if p == precedence => {
                    sequence = apply_type_op(sequence, next_i)
                }
                _ => {
                    i = sequence.next_index(i);
                }
            }
        } else {
            break;
        }
    }
    sequence.drain_iter().collect()
}

fn op_apply_right<
    T: AddArgument + IdentFromString + Clone + Debug,
>(
    mut sequence: Vec<OpSequenceUnit<T>>,
    precedence: i32,
) -> Vec<OpSequenceUnit<T>> {
    let mut sequence = IndexList::from(&mut sequence);
    let mut i = sequence.prev_index(sequence.last_index());
    loop {
        let i_next = sequence.next_index(i);
        if let Some(u) = sequence.get(i_next) {
            match u.operator_precedence() {
                Some(p) if p == precedence => {
                    sequence = apply_type_op(sequence, i_next)
                }
                _ => (),
            }
            i = sequence.prev_index(i);
        } else {
            break;
        }
    }
    sequence.drain_iter().collect()
}

pub fn infix_op_sequence<
    T: AddArgument + IdentFromString + Clone + fmt::Debug,
>(
    mut s: Vec<OpSequenceUnit<T>>,
) -> T {
    let mut precedence_list = BTreeMap::new();
    for op in s.clone() {
        match op {
            OpSequenceUnit::Operand(_) => (),
            OpSequenceUnit::Operator(_, Associativity::Left, p) => {
                if let Some(Associativity::Right) =
                    precedence_list.insert(p, Associativity::Left)
                {
                    panic!(
                        "cannot mix infixl {} and infixr {}",
                        p, p
                    );
                }
            }
            OpSequenceUnit::Operator(_, Associativity::Right, p) => {
                if let Some(Associativity::Left) =
                    precedence_list.insert(p, Associativity::Right)
                {
                    panic!(
                        "cannot mix infixl {} and infixr {}",
                        p, p
                    );
                }
            }
            OpSequenceUnit::Operator(
                _,
                Associativity::UnaryLeft,
                p,
            ) => {
                precedence_list.insert(p, Associativity::Right);
            }
            OpSequenceUnit::Apply(_) => {
                precedence_list.insert(10, Associativity::UnaryLeft);
            }
        }
    }
    for (p, kind) in precedence_list.into_iter().rev() {
        match kind {
            Associativity::Left | Associativity::UnaryLeft => {
                s = op_apply_left(s, p)
            }
            Associativity::Right => s = op_apply_right(s, p),
        }
    }
    debug_assert_eq!(s.len(), 1);
    if let OpSequenceUnit::Operand(t) = &s[0] {
        t.clone()
    } else {
        panic!()
    }
}

impl ConvertWithOpPrecedenceMap for ast0::Type {
    type T = Type;

    fn convert(self, op_precedence_map: &OpPrecedenceMap) -> Self::T {
        match self {
            ast0::Type::Identifier(name) => Type {
                name,
                args: Vec::new(),
            },
            ast0::Type::Paren(s) => {
                infix_op_sequence(op_sequence(s, op_precedence_map))
            }
        }
    }
}

pub fn op_sequence<U: ConvertWithOpPrecedenceMap>(
    s: Vec<ast0::OpSequenceUnit<U>>,
    op_precedence_map: &OpPrecedenceMap,
) -> Vec<OpSequenceUnit<<U as ConvertWithOpPrecedenceMap>::T>> {
    use OpSequenceUnit::*;
    s.into_iter()
        .map(|u| match u {
            ast0::OpSequenceUnit::Operand(e) => {
                Operand(e.convert(op_precedence_map))
            }
            ast0::OpSequenceUnit::Operator(a) => {
                let (ass, p) = op_precedence_map.get(&a);
                Operator(a, ass, p)
            }
            ast0::OpSequenceUnit::Apply(a) => {
                Apply(a.convert(op_precedence_map))
            }
        })
        .collect()
}

pub trait ConvertWithOpPrecedenceMap {
    type T;
    fn convert(self, op_precedence_map: &OpPrecedenceMap) -> Self::T;
}

impl ConvertWithOpPrecedenceMap for ast0::Expr {
    type T = Expr;

    fn convert(self, op_precedence_map: &OpPrecedenceMap) -> Self::T {
        use Expr::*;
        match self {
            ast0::Expr::Lambda(arms) => Lambda(
                arms.into_iter()
                    .map(|a| fn_arm(a, op_precedence_map))
                    .collect(),
            ),
            ast0::Expr::Number(a) => Number(a),
            ast0::Expr::StrLiteral(a) => StrLiteral(a),
            ast0::Expr::Identifier(a) => Ident(a),
            ast0::Expr::Decl(a) => {
                Decl(Box::new(variable_decl(*a, op_precedence_map)))
            }
            ast0::Expr::Unit => Unit,
            ast0::Expr::Paren(a) => {
                infix_op_sequence(op_sequence(a, op_precedence_map))
            }
        }
    }
}

fn fn_arm(
    a: ast0::FnArm,
    op_precedence_map: &OpPrecedenceMap,
) -> FnArm {
    FnArm {
        pattern: a
            .pattern
            .into_iter()
            .map(|s| {
                infix_op_sequence(op_sequence(s, op_precedence_map))
            })
            .collect(),
        pattern_type: a
            .pattern_type
            .into_iter()
            .map(|t| {
                t.map(|t| {
                    infix_op_sequence(op_sequence(
                        t,
                        op_precedence_map,
                    ))
                })
            })
            .collect(),
        exprs: a
            .exprs
            .into_iter()
            .map(|e| {
                infix_op_sequence(op_sequence(e, op_precedence_map))
            })
            .collect(),
    }
}

impl ConvertWithOpPrecedenceMap for ast0::Pattern {
    type T = Pattern;

    fn convert(self, op_precedence_map: &OpPrecedenceMap) -> Self::T {
        match self {
            ast0::Pattern::Number(a) => Pattern::Number(a),
            ast0::Pattern::StrLiteral(a) => Pattern::StrLiteral(a),
            ast0::Pattern::Constructor(name, ps) => {
                Pattern::Constructor {
                    name,
                    args: ps
                        .into_iter()
                        .map(|p| p.convert(op_precedence_map))
                        .collect(),
                }
            }
            ast0::Pattern::Binder(a) => Pattern::Binder(a),
            ast0::Pattern::Underscore => Pattern::Underscore,
        }
    }
}
