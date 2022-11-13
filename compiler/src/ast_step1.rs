use crate::intrinsics::{INTRINSIC_CONSTRUCTORS, OP_PRECEDENCE};
use fxhash::{FxHashMap, FxHashSet};
use index_list::{Index, IndexList};
use parser::{self, token_id::TokenId, Associativity, OpPrecedenceDecl, Span};
use std::{collections::BTreeMap, fmt, fmt::Debug};

/// # Difference between `parser::Ast` and `ast_step1::Ast`
/// - `OpSequence`s and `TypeOpSequence`s are converted to syntex trees
/// based on `OperatorPrecedenceDecl`s.
#[derive(Debug, PartialEq, Eq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub type_alias_decl: Vec<TypeAliasDecl<'a>>,
    pub interface_decl: Vec<InterfaceDecl<'a>>,
}

type StrWithId<'a> = (&'a str, Option<TokenId>);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Forall<'a> {
    pub type_variables: Vec<(StrWithId<'a>, Vec<StrWithId<'a>>)>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl<'a> {
    pub name: StrWithId<'a>,
    pub type_annotation: Option<(Type<'a>, Forall<'a>, Span)>,
    pub value: ExprWithSpan<'a>,
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type<'a> {
    pub name: StrWithId<'a>,
    pub args: Vec<Type<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl<'a> {
    pub name: StrWithId<'a>,
    pub fields: Vec<StrWithId<'a>>,
    pub type_variables: Forall<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeAliasDecl<'a> {
    pub name: StrWithId<'a>,
    pub body: (Type<'a>, Forall<'a>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InterfaceDecl<'a> {
    pub name: StrWithId<'a>,
    pub variables: Vec<(StrWithId<'a>, Type<'a>, Forall<'a>)>,
}

pub type ExprWithSpan<'a> = (Expr<'a>, Span);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident(StrWithId<'a>),
    Decl(Box<VariableDecl<'a>>),
    Call(Box<ExprWithSpan<'a>>, Box<ExprWithSpan<'a>>),
    Do(Vec<ExprWithSpan<'a>>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<(Pattern<'a>, Span)>,
    pub expr: ExprWithSpan<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern<'a> {
    Number(&'a str),
    StrLiteral(&'a str),
    Constructor {
        name: StrWithId<'a>,
        args: Vec<Pattern<'a>>,
    },
    Binder(StrWithId<'a>),
    Underscore,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OpSequenceUnit<'a, T> {
    Operand(T),
    Operator(StrWithId<'a>, Associativity, i32, Span),
    Apply(Vec<OpSequenceUnit<'a, T>>),
}

#[derive(Debug, Clone, Default)]
pub struct OpPrecedenceMap<'a>(FxHashMap<&'a str, (Associativity, i32)>);

impl<'a> OpPrecedenceMap<'a> {
    pub fn new(m: FxHashMap<&'a str, (Associativity, i32)>) -> Self {
        OpPrecedenceMap(m)
    }

    fn get_unwrap(&self, name: &str) -> (Associativity, i32) {
        *self.0.get(name).unwrap_or_else(|| {
            panic!("key {:?} not found in {:?}", name, self.0)
        })
    }

    pub fn get(&self, name: &str) -> Option<(Associativity, i32)> {
        self.0.get(name).copied()
    }
}

pub trait InfixOpCall {
    fn infix_op_call(op_name: &str, e1: Self, e2: Self) -> Self;
}

pub trait IdentFromStr<'a> {
    fn ident_from_str(s: StrWithId<'a>) -> Self;
}

pub trait AddArgument {
    fn add_argument(self, arg: Self) -> Self;
}

impl<'a> IdentFromStr<'a> for Type<'a> {
    fn ident_from_str(s: StrWithId<'a>) -> Self {
        Self {
            name: s,
            args: Vec::new(),
        }
    }
}

impl<'a> AddArgument for (Type<'a>, Span) {
    fn add_argument(mut self, arg: Self) -> Self {
        self.0.args.push(arg.0);
        self
    }
}

impl<'a> IdentFromStr<'a> for Expr<'a> {
    fn ident_from_str(s: StrWithId<'a>) -> Self {
        Self::Ident(s)
    }
}

pub fn merge_span(a: &Span, b: &Span) -> Span {
    a.start.min(b.start)..a.end.max(b.end)
}

impl<'a> AddArgument for ExprWithSpan<'a> {
    fn add_argument(self, arg: Self) -> Self {
        let span = merge_span(&self.1, &arg.1);
        (Expr::Call(self.into(), arg.into()), span)
    }
}

impl<'a> IdentFromStr<'a> for Pattern<'a> {
    fn ident_from_str(name: StrWithId<'a>) -> Self {
        Self::Constructor {
            name,
            args: Vec::new(),
        }
    }
}

impl AddArgument for (Pattern<'_>, Span) {
    fn add_argument(self, arg: Self) -> Self {
        if let Pattern::Constructor { name, mut args } = self.0 {
            args.push(arg.0);
            (
                Pattern::Constructor { name, args },
                merge_span(&self.1, &arg.1),
            )
        } else {
            panic!()
        }
    }
}

impl<T> OpSequenceUnit<'_, T> {
    pub fn operator_precedence(&self) -> Option<i32> {
        match self {
            OpSequenceUnit::Operand(_) => None,
            OpSequenceUnit::Operator(_, _, p, _) => Some(*p),
            OpSequenceUnit::Apply(_) => Some(10),
        }
    }
}

impl<'a> Ast<'a> {
    pub fn from(ast: &'a parser::Ast) -> (Self, OpPrecedenceMap) {
        let mut vs = Vec::new();
        let mut ds = Vec::new();
        let mut aliases = Vec::new();
        let mut precedence_map = OP_PRECEDENCE.clone();
        let mut interfaces = Vec::new();
        let mut constructors: FxHashSet<&str> =
            INTRINSIC_CONSTRUCTORS.keys().map(|s| s.as_str()).collect();
        for d in &ast.decls {
            match d {
                parser::Decl::Variable(a) => vs.push(a),
                parser::Decl::Data(a) => {
                    ds.push(DataDecl {
                        name: (&a.name.0, a.name.1),
                        fields: a
                            .fields
                            .iter()
                            .map(|(name, id)| (name.as_str(), *id))
                            .collect(),
                        type_variables: (&a.type_variables).into(),
                    });
                    constructors.insert(&a.name.0);
                }
                parser::Decl::OpPrecedence(OpPrecedenceDecl {
                    name,
                    associativity,
                    precedence,
                }) => {
                    precedence_map.insert(name, (*associativity, *precedence));
                }
                parser::Decl::TypeAlias(a) => aliases.push(a),
                parser::Decl::Interface(a) => interfaces.push(a),
            }
        }
        let op_precedence_map = OpPrecedenceMap::new(precedence_map);
        let ast = Ast {
            variable_decl: vs
                .into_iter()
                .map(|v| variable_decl(v, &op_precedence_map, &constructors))
                .collect(),
            data_decl: ds,
            type_alias_decl: aliases
                .into_iter()
                .map(|a| TypeAliasDecl {
                    name: (&a.name.0, a.name.1),
                    body: (
                        infix_op_sequence(op_sequence(
                            &a.body.0,
                            &op_precedence_map,
                            &constructors,
                        ))
                        .0,
                        (&a.body.1).into(),
                    ),
                })
                .collect(),
            interface_decl: interfaces
                .into_iter()
                .map(|a| InterfaceDecl {
                    name: (&a.name.0, a.name.1),
                    variables: a
                        .variables
                        .iter()
                        .map(|((name, id), t, forall)| {
                            (
                                (name.as_str(), *id),
                                infix_op_sequence(op_sequence(
                                    t,
                                    &op_precedence_map,
                                    &constructors,
                                ))
                                .0,
                                forall.into(),
                            )
                        })
                        .collect(),
                })
                .collect(),
        };
        (ast, op_precedence_map)
    }
}

impl<'a> From<&'a parser::Forall> for Forall<'a> {
    fn from(parser::Forall { type_variables }: &'a parser::Forall) -> Self {
        Forall {
            type_variables: type_variables
                .iter()
                .map(|((name, id), ts)| {
                    (
                        (name.as_str(), *id),
                        ts.iter().map(|(n, id)| (n.as_str(), *id)).collect(),
                    )
                })
                .collect(),
        }
    }
}

fn variable_decl<'a>(
    v: &'a parser::VariableDecl,
    op_precedence_map: &OpPrecedenceMap,
    constructors: &FxHashSet<&str>,
) -> VariableDecl<'a> {
    VariableDecl {
        name: (&v.name.0, v.name.1),
        type_annotation: v.type_annotation.as_ref().map(|(s, forall)| {
            let (t, span) = infix_op_sequence(op_sequence(
                s,
                op_precedence_map,
                constructors,
            ));
            (t, forall.into(), span)
        }),
        value: infix_op_sequence(op_sequence(
            &v.expr,
            op_precedence_map,
            constructors,
        )),
        span: v.span.clone(),
    }
}

fn apply_type_op<'a, T: IdentFromStr<'a> + Clone + Debug>(
    mut sequence: IndexList<OpSequenceUnit<'a, (T, Span)>>,
    i: Index,
) -> IndexList<OpSequenceUnit<(T, Span)>>
where
    (T, Span): AddArgument,
{
    let i_prev = sequence.prev_index(i);
    let i_next = sequence.next_index(i);
    let s_i = sequence.get(i).cloned();
    let s_i_next = sequence.get(i_next).cloned();
    match s_i {
        Some(OpSequenceUnit::Operator(name, _, _, name_span)) => {
            match sequence.get_mut(i_prev).unwrap() {
                OpSequenceUnit::Operand(e1) => {
                    if let OpSequenceUnit::Operand(e2) = s_i_next.unwrap() {
                        *e1 = (T::ident_from_str(name), name_span)
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

fn op_apply_left<'a, T: IdentFromStr<'a> + Clone + Debug>(
    mut sequence: Vec<OpSequenceUnit<'a, (T, Span)>>,
    precedence: i32,
) -> Vec<OpSequenceUnit<(T, Span)>>
where
    (T, Span): AddArgument,
{
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

fn op_apply_right<'a, T: IdentFromStr<'a> + Clone + Debug>(
    mut sequence: Vec<OpSequenceUnit<'a, (T, Span)>>,
    precedence: i32,
) -> Vec<OpSequenceUnit<(T, Span)>>
where
    (T, Span): AddArgument,
{
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

pub fn infix_op_sequence<'a, T: IdentFromStr<'a> + Clone + fmt::Debug>(
    mut s: Vec<OpSequenceUnit<'a, (T, Span)>>,
) -> (T, Span)
where
    (T, Span): AddArgument,
{
    let mut precedence_list = BTreeMap::new();
    for op in &s {
        match op {
            OpSequenceUnit::Operand(_) => (),
            OpSequenceUnit::Operator(_, Associativity::Left, p, _) => {
                if let Some(Associativity::Right) =
                    precedence_list.insert(*p, Associativity::Left)
                {
                    panic!("cannot mix infixl {} and infixr {}", p, p);
                }
            }
            OpSequenceUnit::Operator(_, Associativity::Right, p, _) => {
                if let Some(Associativity::Left) =
                    precedence_list.insert(*p, Associativity::Right)
                {
                    panic!("cannot mix infixl {} and infixr {}", p, p);
                }
            }
            OpSequenceUnit::Operator(_, Associativity::UnaryLeft, p, _) => {
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

impl<'a> ConvertWithOpPrecedenceMap for (&'a parser::TypeUnit, &'a Span) {
    type T = (Type<'a>, Span);

    fn convert(
        self,
        op_precedence_map: &OpPrecedenceMap,
        constructors: &FxHashSet<&str>,
    ) -> Self::T {
        match self.0 {
            parser::TypeUnit::Ident((name, id)) => (
                Type {
                    name: (name, *id),
                    args: Vec::new(),
                },
                self.1.clone(),
            ),
            parser::TypeUnit::Paren(s) => infix_op_sequence(op_sequence(
                s,
                op_precedence_map,
                constructors,
            )),
        }
    }
}

pub fn op_sequence<'a, U>(
    s: &'a [parser::OpSequenceUnit<(U, Span)>],
    op_precedence_map: &OpPrecedenceMap,
    constructors: &FxHashSet<&str>,
) -> Vec<OpSequenceUnit<'a, <(&'a U, &'a Span) as ConvertWithOpPrecedenceMap>::T>>
where
    (&'a U, &'a Span): ConvertWithOpPrecedenceMap,
{
    use OpSequenceUnit::*;
    s.iter()
        .map(|u| match u {
            parser::OpSequenceUnit::Operand((e, e_span)) => {
                Operand((e, e_span).convert(op_precedence_map, constructors))
            }
            parser::OpSequenceUnit::Op(a, span) => {
                let (ass, p) = op_precedence_map.get_unwrap(&a.0);
                Operator((&a.0, a.1), ass, p, span.clone())
            }
            parser::OpSequenceUnit::Apply(a) => {
                Apply(op_sequence(a, op_precedence_map, constructors))
            }
        })
        .collect()
}

pub trait ConvertWithOpPrecedenceMap {
    type T;
    fn convert(
        self,
        op_precedence_map: &OpPrecedenceMap,
        constructors: &FxHashSet<&str>,
    ) -> Self::T;
}

impl<'a> ConvertWithOpPrecedenceMap for (&'a parser::ExprUnit, &'a Span) {
    type T = ExprWithSpan<'a>;

    fn convert(
        self,
        op_precedence_map: &OpPrecedenceMap,
        constructors: &FxHashSet<&str>,
    ) -> Self::T {
        use Expr::*;
        let e =
            match &self.0 {
                parser::ExprUnit::Case(arms) => Lambda(
                    arms.iter()
                        .map(|a| fn_arm(a, op_precedence_map, constructors))
                        .collect(),
                ),
                parser::ExprUnit::Int(a) => Number(a),
                parser::ExprUnit::Str(a) => StrLiteral(a),
                parser::ExprUnit::Ident((n, id)) => Ident((n, *id)),
                parser::ExprUnit::VariableDecl(a) => Decl(Box::new(
                    variable_decl(a, op_precedence_map, constructors),
                )),
                parser::ExprUnit::Paren(a) => {
                    infix_op_sequence(op_sequence(
                        a,
                        op_precedence_map,
                        constructors,
                    ))
                    .0
                }
                parser::ExprUnit::Do(es) => Do(es
                    .iter()
                    .map(|e| {
                        infix_op_sequence(op_sequence(
                            e,
                            op_precedence_map,
                            constructors,
                        ))
                    })
                    .collect()),
            };
        (e, self.1.clone())
    }
}

fn fn_arm<'a>(
    a: &'a parser::FnArm,
    op_precedence_map: &OpPrecedenceMap,
    constructors: &FxHashSet<&str>,
) -> FnArm<'a> {
    FnArm {
        pattern: a
            .pattern
            .iter()
            .map(|s| {
                infix_op_sequence(op_sequence(
                    s,
                    op_precedence_map,
                    constructors,
                ))
            })
            .collect(),
        expr: infix_op_sequence(op_sequence(
            &a.expr,
            op_precedence_map,
            constructors,
        )),
    }
}

impl<'a> ConvertWithOpPrecedenceMap for (&'a parser::PatternUnit, &'a Span) {
    type T = (Pattern<'a>, Span);

    fn convert(
        self,
        op_precedence_map: &OpPrecedenceMap,
        constructors: &FxHashSet<&str>,
    ) -> Self::T {
        let a = match &self.0 {
            parser::PatternUnit::Int(a) => Pattern::Number(a),
            parser::PatternUnit::Str(a) => Pattern::StrLiteral(a),
            parser::PatternUnit::Ident((name, id), ps) => {
                if constructors.contains(name.as_str()) {
                    Pattern::Constructor {
                        name: (name, *id),
                        args: ps
                            .iter()
                            .map(|p| {
                                infix_op_sequence(op_sequence(
                                    p,
                                    op_precedence_map,
                                    constructors,
                                ))
                                .0
                            })
                            .collect(),
                    }
                } else {
                    assert!(ps.is_empty());
                    Pattern::Binder((name, *id))
                }
            }
            parser::PatternUnit::Underscore => Pattern::Underscore,
        };
        (a, self.1.clone())
    }
}
