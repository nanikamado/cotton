use crate::intrinsics::OP_PRECEDENCE;
use fxhash::FxHashMap;
use index_list::{Index, IndexList};
use parse::{self, Associativity, OpPrecedenceDecl};
use std::{collections::BTreeMap, fmt, fmt::Debug};

/// # Difference between `parse::Ast` and `ast_step1::Ast`
/// - `OpSequence`s and `TypeOpSequence`s are converted to syntex trees
/// based on `OperatorPrecedenceDecl`s.
#[derive(Debug, PartialEq, Eq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub type_alias_decl: Vec<TypeAliasDecl<'a>>,
    pub interface_decl: Vec<InterfaceDecl<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Forall<'a> {
    pub type_variables: Vec<(&'a str, Vec<&'a str>)>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
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
pub struct TypeAliasDecl<'a> {
    pub name: &'a str,
    pub body: (Type<'a>, Forall<'a>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InterfaceDecl<'a> {
    pub name: &'a str,
    pub variables: Vec<(&'a str, Type<'a>, Forall<'a>)>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident(&'a str),
    Decl(Box<VariableDecl<'a>>),
    Call(Box<Expr<'a>>, Box<Expr<'a>>),
    Do(Vec<Expr<'a>>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub expr: Expr<'a>,
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OpSequenceUnit<'a, T> {
    Operand(T),
    Operator(&'a str, Associativity, i32),
    Apply(Vec<OpSequenceUnit<'a, T>>),
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
        Self::Ident(s)
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

impl<'a> From<&'a parse::Ast> for Ast<'a> {
    fn from(ast: &'a parse::Ast) -> Self {
        let mut vs = Vec::new();
        let mut ds = Vec::new();
        let mut aliases = Vec::new();
        let mut precedence_map = OP_PRECEDENCE.clone();
        let mut interfaces = Vec::new();
        for d in &ast.decls {
            match d {
                parse::Decl::Variable(a) => vs.push(a),
                parse::Decl::Data(a) => ds.push(DataDecl {
                    name: &a.name,
                    field_len: a.field_len,
                }),
                parse::Decl::OpPrecedence(OpPrecedenceDecl {
                    name,
                    associativity,
                    precedence,
                }) => {
                    precedence_map
                        .insert(name, (*associativity, *precedence));
                }
                parse::Decl::TypeAlias(a) => aliases.push(a),
                parse::Decl::Interface(a) => interfaces.push(a),
            }
        }
        let op_precedence_map = OpPrecedenceMap::new(precedence_map);
        Ast {
            variable_decl: vs
                .into_iter()
                .map(|v| variable_decl(v, &op_precedence_map))
                .collect(),
            data_decl: ds,
            type_alias_decl: aliases
                .into_iter()
                .map(|a| TypeAliasDecl {
                    name: &a.name,
                    body: (
                        infix_op_sequence(op_sequence(
                            &a.body.0,
                            &op_precedence_map,
                        )),
                        (&a.body.1).into(),
                    ),
                })
                .collect(),
            interface_decl: interfaces
                .into_iter()
                .map(|a| InterfaceDecl {
                    name: &a.name,
                    variables: a
                        .variables
                        .iter()
                        .map(|(name, t, forall)| {
                            (
                                name.as_str(),
                                infix_op_sequence(op_sequence(
                                    t,
                                    &op_precedence_map,
                                )),
                                forall.into(),
                            )
                        })
                        .collect(),
                })
                .collect(),
        }
    }
}

impl<'a> From<&'a parse::Forall> for Forall<'a> {
    fn from(
        parse::Forall { type_variables }: &'a parse::Forall,
    ) -> Self {
        Forall {
            type_variables: type_variables
                .iter()
                .map(|(name, ts)| {
                    (
                        name.as_str(),
                        ts.iter().map(String::as_str).collect(),
                    )
                })
                .collect(),
        }
    }
}

fn variable_decl<'a>(
    v: &'a parse::VariableDecl,
    op_precedence_map: &OpPrecedenceMap,
) -> VariableDecl<'a> {
    VariableDecl {
        name: &v.name,
        type_annotation: v.type_annotation.as_ref().map(
            |(s, forall)| {
                (
                    infix_op_sequence(op_sequence(
                        s,
                        op_precedence_map,
                    )),
                    forall.into(),
                )
            },
        ),
        value: infix_op_sequence(op_sequence(
            &v.expr,
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
                    *e = e.clone().add_argument(infix_op_sequence(a));
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

impl<'a> ConvertWithOpPrecedenceMap for &'a parse::TypeUnit {
    type T = Type<'a>;

    fn convert(self, op_precedence_map: &OpPrecedenceMap) -> Self::T {
        match self {
            parse::TypeUnit::Ident(name) => Type {
                name,
                args: Vec::new(),
            },
            parse::TypeUnit::Paren(s) => {
                infix_op_sequence(op_sequence(s, op_precedence_map))
            }
        }
    }
}

pub fn op_sequence<'a, U>(
    s: &'a [parse::OpSequenceUnit<U>],
    op_precedence_map: &OpPrecedenceMap,
) -> Vec<OpSequenceUnit<'a, <&'a U as ConvertWithOpPrecedenceMap>::T>>
where
    &'a U: ConvertWithOpPrecedenceMap,
{
    use OpSequenceUnit::*;
    s.iter()
        .map(|u| match u {
            parse::OpSequenceUnit::Operand(e) => {
                Operand(e.convert(op_precedence_map))
            }
            parse::OpSequenceUnit::Op(a) => {
                let (ass, p) = op_precedence_map.get(a);
                Operator(a, ass, p)
            }
            parse::OpSequenceUnit::Apply(a) => {
                Apply(op_sequence(a, op_precedence_map))
            }
        })
        .collect()
}

pub trait ConvertWithOpPrecedenceMap {
    type T;
    fn convert(self, op_precedence_map: &OpPrecedenceMap) -> Self::T;
}

impl<'a> ConvertWithOpPrecedenceMap for &'a parse::ExprUnit {
    type T = Expr<'a>;

    fn convert(self, op_precedence_map: &OpPrecedenceMap) -> Self::T {
        use Expr::*;
        match self {
            parse::ExprUnit::Case(arms) => Lambda(
                arms.iter()
                    .map(|a| fn_arm(a, op_precedence_map))
                    .collect(),
            ),
            parse::ExprUnit::Int(a) => Number(a),
            parse::ExprUnit::Str(a) => StrLiteral(a),
            parse::ExprUnit::Ident(a) => Ident(a),
            parse::ExprUnit::VariableDecl(a) => {
                Decl(Box::new(variable_decl(a, op_precedence_map)))
            }
            parse::ExprUnit::Paren(a) => {
                infix_op_sequence(op_sequence(a, op_precedence_map))
            }
            parse::ExprUnit::Do(es) => Do(es
                .iter()
                .map(|e| {
                    infix_op_sequence(op_sequence(
                        e,
                        op_precedence_map,
                    ))
                })
                .collect()),
        }
    }
}

fn fn_arm<'a>(
    a: &'a parse::FnArm,
    op_precedence_map: &OpPrecedenceMap,
) -> FnArm<'a> {
    FnArm {
        pattern: a
            .pattern
            .iter()
            .map(|s| {
                infix_op_sequence(op_sequence(s, op_precedence_map))
            })
            .collect(),
        expr: infix_op_sequence(op_sequence(
            &a.expr,
            op_precedence_map,
        )),
    }
}

impl<'a> ConvertWithOpPrecedenceMap for &'a parse::PatternUnit {
    type T = Pattern<'a>;

    fn convert(self, op_precedence_map: &OpPrecedenceMap) -> Self::T {
        match self {
            parse::PatternUnit::Int(a) => Pattern::Number(a),
            parse::PatternUnit::Str(a) => Pattern::StrLiteral(a),
            parse::PatternUnit::Constructor(name, ps) => {
                Pattern::Constructor {
                    name,
                    args: ps
                        .iter()
                        .map(|p| {
                            infix_op_sequence(op_sequence(
                                p,
                                op_precedence_map,
                            ))
                        })
                        .collect(),
                }
            }
            parse::PatternUnit::Bind(a) => Pattern::Binder(a),
            parse::PatternUnit::Underscore => Pattern::Underscore,
        }
    }
}
