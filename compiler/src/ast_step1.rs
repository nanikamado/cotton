pub mod decl_id;
pub mod ident_id;
pub mod name_id;
pub mod token_map;

use self::{
    decl_id::DeclId,
    name_id::Name,
    token_map::{TokenMap, TokenMapEntry},
};
use crate::intrinsics::{INTRINSIC_CONSTRUCTORS, OP_PRECEDENCE};
use fxhash::{FxHashMap, FxHashSet};
use index_list::{Index, IndexList};
use itertools::Itertools;
use parser::{
    self, token_id::TokenId, Associativity, ExprSuffixOp, OpPrecedenceDecl,
    PatternApply, Span, TypeApply,
};
use std::{collections::BTreeMap, fmt::Debug};

/// Difference between `parser::Ast` and `ast_step1::Ast`:
/// - `OpSequence`s and `TypeOpSequence`s are converted to syntex trees
/// based on `OperatorPrecedenceDecl`s.
#[derive(Debug, PartialEq, Eq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub type_alias_decl: Vec<TypeAliasDecl<'a>>,
    pub interface_decl: Vec<InterfaceDecl<'a>>,
    pub modules: Vec<Module<'a>>,
}

type StrWithId<'a> = (&'a str, Option<TokenId>);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Forall<'a> {
    pub type_variables: Vec<(StrWithId<'a>, Vec<StrWithId<'a>>)>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl<'a> {
    pub name: Name,
    pub type_annotation: Option<(Type<'a>, Forall<'a>, Span)>,
    pub value: ExprWithSpan<'a>,
    pub span: Span,
    pub is_public: bool,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type<'a> {
    pub name: StrWithId<'a>,
    pub path: Vec<StrWithId<'a>>,
    pub span: Span,
    pub args: Vec<Type<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl<'a> {
    pub name: Name,
    pub fields: Vec<StrWithId<'a>>,
    pub type_variables: Forall<'a>,
    pub decl_id: DeclId,
    pub is_public: bool,
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
    Ident {
        name: StrWithId<'a>,
        path: Vec<StrWithId<'a>>,
    },
    Decl(Box<VariableDecl<'a>>),
    Call(Box<ExprWithSpan<'a>>, Box<ExprWithSpan<'a>>),
    Do(Vec<ExprWithSpan<'a>>),
    Question(Box<ExprWithSpan<'a>>, Span),
    TypeAnnotation(Box<ExprWithSpan<'a>>, Type<'a>, Forall<'a>),
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
    TypeRestriction(Box<Pattern<'a>>, Type<'a>, Forall<'a>),
}

#[derive(Debug, Clone)]
enum OpSequenceUnit<'a, T>
where
    <T as ApplySuffixOp<'a>>::Op: Debug,
    T: ApplySuffixOp<'a>,
{
    Operand(T),
    Operator(StrWithId<'a>, Associativity, i32, Span),
    Apply(&'a <T as ApplySuffixOp<'a>>::Op),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Module<'a> {
    pub name: Name,
    pub ast: Ast<'a>,
    pub is_public: bool,
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
            path: Vec::new(),
            span: 0..0, // TODO: not correct
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
    fn ident_from_str(name: StrWithId<'a>) -> Self {
        Self::Ident {
            name,
            path: Vec::new(),
        }
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

struct Env<'a> {
    op_precedence_map: &'a OpPrecedenceMap<'a>,
    constructors: &'a FxHashSet<&'a str>,
    module_path: Name,
    token_map: &'a mut TokenMap,
}

trait ApplySuffixOp<'a> {
    type Op;
    fn apply_suffix_op(self, arg: &'a Self::Op, env: &mut Env) -> Self;
}

impl<'a> ApplySuffixOp<'a> for ExprWithSpan<'a> {
    type Op = ExprSuffixOp;

    fn apply_suffix_op(self, arg: &'a Self::Op, env: &mut Env) -> Self {
        match arg {
            ExprSuffixOp::Apply(s) => self.add_argument(expr(s, env)),
            ExprSuffixOp::Question(question_span) => {
                let span = self.1.clone();
                (Expr::Question(Box::new(self), question_span.clone()), span)
            }
        }
    }
}

impl<'a> ApplySuffixOp<'a> for (Pattern<'a>, Span) {
    type Op = PatternApply;

    fn apply_suffix_op(self, arg: &'a Self::Op, env: &mut Env) -> Self {
        self.add_argument(fold_op_sequence(&arg.0, env))
    }
}

impl<'a> ApplySuffixOp<'a> for (Type<'a>, Span) {
    type Op = TypeApply;

    fn apply_suffix_op(self, arg: &'a Self::Op, env: &mut Env) -> Self {
        self.add_argument(fold_op_sequence(&arg.0, env))
    }
}

impl<'a, T> OpSequenceUnit<'a, T>
where
    T: ApplySuffixOp<'a>,
    <T as ApplySuffixOp<'a>>::Op: std::fmt::Debug,
{
    pub fn operator_precedence(&self) -> Option<i32> {
        match self {
            OpSequenceUnit::Operand(_) => None,
            OpSequenceUnit::Operator(_, _, p, _) => Some(*p),
            OpSequenceUnit::Apply(_) => Some(10),
        }
    }
}

impl<'a> Ast<'a> {
    fn from_rec(
        ast: &'a parser::Ast,
        module_path: Name,
        token_map: &mut TokenMap,
    ) -> (Self, OpPrecedenceMap<'a>) {
        let mut vs = Vec::new();
        let mut ds = Vec::new();
        let mut aliases = Vec::new();
        let mut precedence_map = OP_PRECEDENCE.clone();
        let mut interfaces = Vec::new();
        let mut constructors: FxHashSet<&str> =
            INTRINSIC_CONSTRUCTORS.keys().map(|s| s.as_str()).collect();
        let mut modules = Vec::new();
        for d in &ast.decls {
            match d {
                parser::Decl::Variable(a) => vs.push(a),
                parser::Decl::Data(a) => {
                    let decl_id = DeclId::new();
                    token_map
                        .insert(a.name.1, TokenMapEntry::DataDecl(decl_id));
                    ds.push(DataDecl {
                        name: Name::from_str(module_path, &a.name.0),
                        fields: a
                            .fields
                            .iter()
                            .map(|(name, id)| (name.as_str(), *id))
                            .collect(),
                        type_variables: (&a.type_variables).into(),
                        decl_id,
                        is_public: a.is_public,
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
                parser::Decl::Module {
                    name,
                    ast,
                    is_public,
                } => {
                    let name = Name::from_str(module_path, &name.0);
                    modules.push(Module {
                        name,
                        ast: Ast::from_rec(ast, name, token_map).0,
                        is_public: *is_public,
                    });
                }
            }
        }
        let op_precedence_map = OpPrecedenceMap::new(precedence_map);
        let ast = Ast {
            variable_decl: vs
                .into_iter()
                .map(|v| {
                    variable_decl(
                        v,
                        &mut Env {
                            op_precedence_map: &op_precedence_map,
                            constructors: &constructors,
                            module_path,
                            token_map,
                        },
                    )
                })
                .collect(),
            data_decl: ds,
            type_alias_decl: aliases
                .into_iter()
                .map(|a| TypeAliasDecl {
                    name: (&a.name.0, a.name.1),
                    body: (
                        fold_op_sequence(
                            &a.body.0,
                            &mut Env {
                                op_precedence_map: &op_precedence_map,
                                constructors: &constructors,
                                module_path,
                                token_map,
                            },
                        )
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
                                fold_op_sequence(
                                    t,
                                    &mut Env {
                                        op_precedence_map: &op_precedence_map,
                                        constructors: &constructors,
                                        module_path,
                                        token_map,
                                    },
                                )
                                .0,
                                forall.into(),
                            )
                        })
                        .collect(),
                })
                .collect(),
            modules,
        };
        (ast, op_precedence_map)
    }

    pub fn from(ast: &'a parser::Ast) -> (Self, OpPrecedenceMap<'a>, TokenMap) {
        let mut token_map = TokenMap::default();
        let (a, b) = Self::from_rec(ast, Name::root_module(), &mut token_map);
        (a, b, token_map)
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

fn expr<'a>(e: &'a parser::Expr, env: &mut Env) -> ExprWithSpan<'a> {
    let value = fold_op_sequence(&e.0, env);
    if let Some((annotation, forall)) = &e.1 {
        let (t, _span) = fold_op_sequence(annotation, env);
        let span = value.1.clone();
        (
            Expr::TypeAnnotation(Box::new(value), t, forall.into()),
            span,
        )
    } else {
        value
    }
}

fn variable_decl<'a>(
    v: &'a parser::VariableDecl,
    env: &mut Env,
) -> VariableDecl<'a> {
    let decl_id = DeclId::new();
    env.token_map.insert(v.name.1, TokenMapEntry::Decl(decl_id));
    VariableDecl {
        name: Name::from_str(env.module_path, &v.name.0),
        type_annotation: v.type_annotation.as_ref().map(|(s, forall)| {
            let (t, span) = fold_op_sequence(s, env);
            (t, forall.into(), span)
        }),
        value: expr(&v.expr, env),
        span: v.span.clone(),
        is_public: v.is_public,
        decl_id,
    }
}

fn apply_type_op<'a, T: IdentFromStr<'a> + Clone + Debug>(
    mut sequence: IndexList<OpSequenceUnit<'a, (T, Span)>>,
    i: Index,
    env: &mut Env,
) -> IndexList<OpSequenceUnit<'a, (T, Span)>>
where
    (T, Span): AddArgument + ApplySuffixOp<'a>,
    <(T, Span) as ApplySuffixOp<'a>>::Op: Clone + Debug,
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
                    sequence = apply_type_op(sequence, i_prev, env);
                    sequence = apply_type_op(sequence, i, env);
                }
                _ => panic!(),
            }
        }
        Some(OpSequenceUnit::Apply(a)) => {
            match sequence.get_mut(i_prev).unwrap() {
                OpSequenceUnit::Operand(e) => {
                    *e = e.clone().apply_suffix_op(a, env);
                    sequence.remove(i);
                }
                OpSequenceUnit::Apply(_) => {
                    sequence = apply_type_op(sequence, i_prev, env);
                    sequence = apply_type_op(sequence, i, env);
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
    env: &mut Env,
) -> Vec<OpSequenceUnit<'a, (T, Span)>>
where
    (T, Span): AddArgument + ApplySuffixOp<'a>,
    <(T, Span) as ApplySuffixOp<'a>>::Op: Clone + Debug,
{
    let mut sequence = IndexList::from(&mut sequence);
    let mut i = sequence.first_index();
    loop {
        let next_i = sequence.next_index(i);
        if let Some(u) = sequence.get(next_i) {
            match u.operator_precedence() {
                Some(p) if p == precedence => {
                    sequence = apply_type_op(sequence, next_i, env)
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
    env: &mut Env,
) -> Vec<OpSequenceUnit<'a, (T, Span)>>
where
    (T, Span): AddArgument + ApplySuffixOp<'a>,
    <(T, Span) as ApplySuffixOp<'a>>::Op: Clone + Debug,
{
    let mut sequence = IndexList::from(&mut sequence);
    let mut i = sequence.prev_index(sequence.last_index());
    loop {
        let i_next = sequence.next_index(i);
        if let Some(u) = sequence.get(i_next) {
            match u.operator_precedence() {
                Some(p) if p == precedence => {
                    sequence = apply_type_op(sequence, i_next, env)
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

impl<'a> ConvertWithOpPrecedenceMap for (&'a parser::TypeUnit, &'a Span) {
    type T = (Type<'a>, Span);

    fn convert(self, env: &mut Env) -> Self::T {
        match self.0 {
            parser::TypeUnit::Ident {
                path,
                name: (name, id),
            } => (
                Type {
                    name: (name, *id),
                    args: Vec::new(),
                    path: path
                        .iter()
                        .map(|(name, id)| (name.as_str(), *id))
                        .collect(),
                    span: self.1.clone(),
                },
                self.1.clone(),
            ),
            parser::TypeUnit::Paren(s) => fold_op_sequence(s, env),
        }
    }
}

#[allow(clippy::type_complexity)]
fn fold_op_sequence<'a, T, U: 'a>(
    s: &'a [parser::OpSequenceUnit<
        (T, Span),
        <(U, Span) as ApplySuffixOp<'a>>::Op,
    >],
    env: &mut Env,
) -> (U, Span)
where
    (U, Span): AddArgument + ApplySuffixOp<'a>,
    (&'a T, &'a Span): ConvertWithOpPrecedenceMap<T = (U, Span)>,
    <(U, Span) as ApplySuffixOp<'a>>::Op: Clone + Debug,
    U: IdentFromStr<'a> + Clone + Debug,
{
    use OpSequenceUnit::*;
    let mut s = s
        .iter()
        .map(|u| match u {
            parser::OpSequenceUnit::Operand((e, e_span)) => {
                Operand((e, e_span).convert(env))
            }
            parser::OpSequenceUnit::Op(a, span) => {
                let (ass, p) = env.op_precedence_map.get_unwrap(&a.0);
                Operator((&a.0, a.1), ass, p, span.clone())
            }
            parser::OpSequenceUnit::Apply(a) => Apply(a),
        })
        .collect_vec();
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
                s = op_apply_left(s, p, env)
            }
            Associativity::Right => s = op_apply_right(s, p, env),
        }
    }
    debug_assert_eq!(s.len(), 1);
    if let OpSequenceUnit::Operand(t) = &s[0] {
        t.clone()
    } else {
        panic!()
    }
}

trait ConvertWithOpPrecedenceMap {
    type T;
    fn convert(self, env: &mut Env) -> Self::T;
}

impl<'a> ConvertWithOpPrecedenceMap for (&'a parser::ExprUnit, &'a Span) {
    type T = ExprWithSpan<'a>;

    fn convert(self, env: &mut Env) -> Self::T {
        use Expr::*;
        let e = match &self.0 {
            parser::ExprUnit::Case(arms) => {
                Lambda(arms.iter().map(|a| fn_arm(a, env)).collect())
            }
            parser::ExprUnit::Int(a) => Number(a),
            parser::ExprUnit::Str(a) => StrLiteral(a),
            parser::ExprUnit::Ident {
                name: (n, id),
                path,
            } => Ident {
                name: (n, *id),
                path: path
                    .iter()
                    .map(|(name, t)| (name.as_str(), *t))
                    .collect(),
            },
            parser::ExprUnit::VariableDecl(a) => {
                Decl(Box::new(variable_decl(a, env)))
            }
            parser::ExprUnit::Paren(a) => expr(a, env).0,
            parser::ExprUnit::Do(es) => {
                Do(es.iter().map(|e| expr(e, env)).collect())
            }
        };
        (e, self.1.clone())
    }
}

fn fn_arm<'a>(a: &'a parser::FnArm, env: &mut Env) -> FnArm<'a> {
    FnArm {
        pattern: a.pattern.iter().map(|s| fold_op_sequence(s, env)).collect(),
        expr: expr(&a.expr, env),
    }
}

impl<'a> ConvertWithOpPrecedenceMap for (&'a parser::PatternUnit, &'a Span) {
    type T = (Pattern<'a>, Span);

    fn convert(self, env: &mut Env) -> Self::T {
        let a = match &self.0 {
            parser::PatternUnit::Int(a) => Pattern::Number(a),
            parser::PatternUnit::Str(a) => Pattern::StrLiteral(a),
            parser::PatternUnit::Ident((name, id), ps) => {
                if env.constructors.contains(name.as_str()) {
                    Pattern::Constructor {
                        name: (name, *id),
                        args: ps
                            .iter()
                            .map(|p| fold_op_sequence(p, env).0)
                            .collect(),
                    }
                } else {
                    assert!(ps.is_empty());
                    Pattern::Binder((name, *id))
                }
            }
            parser::PatternUnit::Underscore => Pattern::Underscore,
            parser::PatternUnit::TypeRestriction(p, t, forall) => {
                Pattern::TypeRestriction(
                    Box::new(fold_op_sequence(p, env).0),
                    fold_op_sequence(t, env).0,
                    forall.into(),
                )
            }
        };
        (a, self.1.clone())
    }
}
