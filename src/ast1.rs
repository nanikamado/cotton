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
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl<'a> {
    pub identifier: &'a str,
    pub type_annotation: Option<(Type<'a>, Forall<'a>)>,
    pub value: Expr<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type<'a> {
    pub name: &'a str,
    pub args: Vec<Type<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl<'a> {
    pub name: &'a str,
    pub field_len: usize,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident(&'a str),
    Decl(Box<VariableDecl<'a>>),
    Call(Box<Expr<'a>>, Box<Expr<'a>>),
    Unit,
}

#[derive(Debug, PartialEq, Eq, Clone)]
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
        name: &'a str,
        args: Vec<Pattern<'a>>,
    },
    Binder(&'a str),
    Underscore,
}

pub type TypeOperatorSequence<'a> = Vec<OpSequenceUnit<'a, Type<'a>>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OpSequenceUnit<'a, T> {
    Operand(T),
    Operator(&'a str, Associativity, i32),
    Apply(T),
}

#[derive(Debug, Clone, Default)]
pub struct OpPrecedenceMap<'a>(
    FxHashMap<&'a str, (Associativity, i32)>,
);

impl<'a> OpPrecedenceMap<'a> {
    pub fn new(m: FxHashMap<&'a str, (Associativity, i32)>) -> Self {
        OpPrecedenceMap(m)
    }

    fn get(&self, name: &str) -> (Associativity, i32) {
        *self.0.get(name).unwrap_or_else(|| {
            panic!("key {:?} not found in {:?}", name, self.0)
        })
    }
}

pub trait InfixOpCall {
    fn infix_op_call(op_name: &str, e1: Self, e2: Self) -> Self;
}

pub trait IdentFromStr<'a> {
    fn ident_from_str(s: &'a str) -> Self;
}

pub trait AddArgument {
    fn add_argument(self, arg: Self) -> Self;
}

impl<'a> IdentFromStr<'a> for Type<'a> {
    fn ident_from_str(s: &'a str) -> Self {
        Self {
            name: s,
            args: Vec::new(),
        }
    }
}

impl<'a> AddArgument for Type<'a> {
    fn add_argument(mut self, arg: Self) -> Self {
        self.args.push(arg);
        self
    }
}

impl<'a> IdentFromStr<'a> for Expr<'a> {
    fn ident_from_str(s: &'a str) -> Self {
        Self::Ident(&s)
    }
}

impl<'a> AddArgument for Expr<'a> {
    fn add_argument(self, arg: Self) -> Self {
        Self::Call(self.into(), arg.into())
    }
}

impl<'a> IdentFromStr<'a> for Pattern<'a> {
    fn ident_from_str(name: &'a str) -> Self {
        Self::Constructor {
            name,
            args: Vec::new(),
        }
    }
}

impl AddArgument for Pattern<'_> {
    fn add_argument(self, arg: Self) -> Self {
        if let Pattern::Constructor { name, mut args } = self {
            args.push(arg);
            Pattern::Constructor { name, args }
        } else {
            panic!()
        }
    }
}

impl<T> OpSequenceUnit<'_, T> {
    pub fn operator_precedence(&self) -> Option<i32> {
        match self {
            OpSequenceUnit::Operand(_) => None,
            OpSequenceUnit::Operator(_, _, p) => Some(*p),
            OpSequenceUnit::Apply(_) => Some(10),
        }
    }
}

impl<'a> From<ast0::Ast<'a>> for Ast<'a> {
    fn from(ast: ast0::Ast<'a>) -> Self {
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

fn variable_decl<'a>(
    v: ast0::VariableDecl<'a>,
    op_precedence_map: &OpPrecedenceMap,
) -> VariableDecl<'a> {
    VariableDecl {
        identifier: &v.identifier,
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

fn apply_type_op<
    'a,
    T: AddArgument + IdentFromStr<'a> + Clone + Debug,
>(
    mut sequence: IndexList<OpSequenceUnit<'a, T>>,
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
                        *e1 = T::ident_from_str(name)
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

fn op_apply_left<
    'a,
    T: AddArgument + IdentFromStr<'a> + Clone + Debug,
>(
    mut sequence: Vec<OpSequenceUnit<'a, T>>,
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
    'a,
    T: AddArgument + IdentFromStr<'a> + Clone + Debug,
>(
    mut sequence: Vec<OpSequenceUnit<'a, T>>,
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
    'a,
    T: AddArgument + IdentFromStr<'a> + Clone + fmt::Debug,
>(
    mut s: Vec<OpSequenceUnit<'a, T>>,
) -> T {
    let mut precedence_list = BTreeMap::new();
    for op in &s {
        match op {
            OpSequenceUnit::Operand(_) => (),
            OpSequenceUnit::Operator(_, Associativity::Left, p) => {
                if let Some(Associativity::Right) =
                    precedence_list.insert(*p, Associativity::Left)
                {
                    panic!(
                        "cannot mix infixl {} and infixr {}",
                        p, p
                    );
                }
            }
            OpSequenceUnit::Operator(_, Associativity::Right, p) => {
                if let Some(Associativity::Left) =
                    precedence_list.insert(*p, Associativity::Right)
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
                precedence_list.insert(*p, Associativity::Right);
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

impl<'a> ConvertWithOpPrecedenceMap for ast0::Type<'a> {
    type T = Type<'a>;

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

pub fn op_sequence<'a, U: ConvertWithOpPrecedenceMap>(
    s: Vec<ast0::OpSequenceUnit<'a, U>>,
    op_precedence_map: &OpPrecedenceMap,
) -> Vec<OpSequenceUnit<'a, <U as ConvertWithOpPrecedenceMap>::T>> {
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

impl<'a> ConvertWithOpPrecedenceMap for ast0::Expr<'a> {
    type T = Expr<'a>;

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

fn fn_arm<'a>(
    a: ast0::FnArm<'a>,
    op_precedence_map: &OpPrecedenceMap,
) -> FnArm<'a> {
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

impl<'a> ConvertWithOpPrecedenceMap for ast0::Pattern<'a> {
    type T = Pattern<'a>;

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
