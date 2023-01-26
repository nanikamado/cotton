pub mod decl_id;
pub mod ident_id;
pub mod name_id;
pub mod token_map;

use self::decl_id::DeclId;
use self::name_id::Path;
use self::token_map::{TokenMap, TokenMapEntry};
use crate::ast_step2::imports::Imports;
use crate::errors::CompileError;
use crate::intrinsics::INTRINSIC_CONSTRUCTORS;
use fxhash::FxHashSet;
use index_list::{Index, IndexList};
use itertools::Itertools;
use parser::token_id::TokenId;
use parser::{
    self, Associativity, ExprSuffixOp, Forall, OpPrecedenceDecl, PatternApply,
    Span, TypeApply,
};
use std::collections::BTreeMap;
use std::fmt::Debug;

/// Difference between `parser::Ast` and `ast_step1::Ast`:
/// - `OpSequence`s and `TypeOpSequence`s are converted to syntax trees
/// based on `OperatorPrecedenceDecl`s.
#[derive(Debug, PartialEq, Eq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub type_alias_decl: Vec<TypeAliasDecl<'a>>,
    pub interface_decl: Vec<InterfaceDecl<'a>>,
    pub modules: Vec<Module<'a>>,
}

type StrWithId<'a> = (&'a str, Option<Span>, Option<TokenId>);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl<'a> {
    pub name: Path,
    pub type_annotation: Option<(Type<'a>, &'a Forall, Span)>,
    pub value: ExprWithSpan<'a>,
    pub span: Span,
    pub is_public: bool,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type<'a> {
    pub path: &'a parser::Path,
    pub args: Vec<Type<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl<'a> {
    pub name: Path,
    pub fields: Vec<Field<'a>>,
    pub type_variables: &'a Forall,
    pub decl_id: DeclId,
    pub is_public: bool,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Field<'a> {
    pub type_: Type<'a>,
    pub name: Path,
    pub is_public: bool,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeAliasDecl<'a> {
    pub name: StrWithId<'a>,
    pub body: (Type<'a>, &'a Forall),
    pub is_public: bool,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InterfaceDecl<'a> {
    pub name: StrWithId<'a>,
    pub variables: Vec<(StrWithId<'a>, Type<'a>, &'a Forall)>,
    pub is_public: bool,
}

pub type ExprWithSpan<'a> = (Expr<'a>, Span);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident {
        path: &'a parser::Path,
    },
    Record {
        path: &'a parser::Path,
        fields: Vec<(StrWithId<'a>, Expr<'a>)>,
    },
    Decl(Box<VariableDecl<'a>>),
    Call(Box<ExprWithSpan<'a>>, Box<ExprWithSpan<'a>>),
    Do(Vec<ExprWithSpan<'a>>),
    Question(Box<ExprWithSpan<'a>>, Span),
    TypeAnnotation(Box<ExprWithSpan<'a>>, Type<'a>, &'a Forall),
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
        path: &'a parser::Path,
        args: Vec<(Pattern<'a>, Span)>,
    },
    Binder(StrWithId<'a>),
    Underscore,
    TypeRestriction(Box<Pattern<'a>>, Type<'a>, &'a Forall),
    Apply(Box<Pattern<'a>>, Vec<ApplyPattern<'a>>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ApplyPattern<'a> {
    pub function: ExprWithSpan<'a>,
    pub post_pattern: (Pattern<'a>, Span),
}

#[derive(Debug, Clone)]
enum OpSequenceUnit<'a, T>
where
    <T as ApplySuffixOp<'a>>::Op: Debug,
    T: ApplySuffixOp<'a>,
{
    Operand(T),
    Operator(&'a parser::Path, Associativity, i32, Span),
    Apply(&'a <T as ApplySuffixOp<'a>>::Op),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Module<'a> {
    pub name: Path,
    pub ast: Ast<'a>,
    pub is_public: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct UseDecl<'a> {
    pub is_public: bool,
    pub name: StrWithId<'a>,
    pub path: &'a parser::Path,
    pub span: Span,
}

pub trait InfixOpCall {
    fn infix_op_call(op_name: &str, e1: Self, e2: Self) -> Self;
}

pub trait IdentFromStr<'a> {
    fn ident_from_str(s: &'a parser::Path) -> Self;
}

pub trait AddArgument {
    fn add_argument(self, arg: Self) -> Self;
}

impl<'a> IdentFromStr<'a> for Type<'a> {
    fn ident_from_str(s: &'a parser::Path) -> Self {
        Self {
            args: Vec::new(),
            path: s,
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
    fn ident_from_str(name: &'a parser::Path) -> Self {
        Self::Ident { path: name }
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
    fn ident_from_str(name: &'a parser::Path) -> Self {
        Self::Constructor {
            path: name,
            args: Vec::new(),
        }
    }
}

impl AddArgument for (Pattern<'_>, Span) {
    fn add_argument(self, arg: Self) -> Self {
        if let Pattern::Constructor {
            path: name,
            mut args,
        } = self.0
        {
            let span = arg.1.clone();
            args.push(arg);
            (
                Pattern::Constructor { path: name, args },
                merge_span(&self.1, &span),
            )
        } else {
            panic!()
        }
    }
}

struct Env<'a> {
    imports: &'a mut Imports,
    constructors: &'a FxHashSet<&'a str>,
    module_path: Path,
    token_map: &'a mut TokenMap,
}

trait ApplySuffixOp<'a>: Sized {
    type Op;
    fn apply_suffix_op(
        self,
        arg: &'a Self::Op,
        env: &mut Env,
        module_path: Path,
    ) -> Result<Self, CompileError>;
}

impl<'a> ApplySuffixOp<'a> for ExprWithSpan<'a> {
    type Op = ExprSuffixOp;

    fn apply_suffix_op(
        self,
        arg: &'a Self::Op,
        env: &mut Env,
        module_path: Path,
    ) -> Result<Self, CompileError> {
        match arg {
            ExprSuffixOp::Apply(s) => {
                Ok(self.add_argument(expr(s, env, module_path)?))
            }
            ExprSuffixOp::Question(question_span) => {
                let span = self.1.clone();
                Ok((
                    Expr::Question(Box::new(self), question_span.clone()),
                    span,
                ))
            }
        }
    }
}

impl<'a> ApplySuffixOp<'a> for (Pattern<'a>, Span) {
    type Op = PatternApply;

    fn apply_suffix_op(
        self,
        arg: &'a Self::Op,
        env: &mut Env,
        module_path: Path,
    ) -> Result<Self, CompileError> {
        Ok(self.add_argument(fold_op_sequence(&arg.0, env, module_path)?))
    }
}

impl<'a> ApplySuffixOp<'a> for (Type<'a>, Span) {
    type Op = TypeApply;

    fn apply_suffix_op(
        self,
        arg: &'a Self::Op,
        env: &mut Env,
        module_path: Path,
    ) -> Result<Self, CompileError> {
        Ok(self.add_argument(fold_op_sequence(&arg.0, env, module_path)?))
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
        module_path: Path,
        token_map: &mut TokenMap,
        constructors: &mut FxHashSet<&'a str>,
        imports: &mut Imports,
    ) -> Result<Self, CompileError> {
        let mut vs = Vec::new();
        let mut ds = Vec::new();
        let mut aliases = Vec::new();
        let mut interfaces = Vec::new();
        let mut modules = Vec::new();
        for d in &ast.decls {
            match d {
                parser::Decl::Variable(a) => vs.push(a),
                parser::Decl::Data(a) => {
                    let decl_id = DeclId::new();
                    token_map
                        .insert(a.name.2, TokenMapEntry::DataDecl(decl_id));
                    ds.push(DataDecl {
                        name: Path::from_str(module_path, &a.name.0),
                        fields: a
                            .fields
                            .iter()
                            .map(|parser::Field { type_: t, name }| {
                                let (t, _span) = fold_op_sequence(
                                    t,
                                    &mut Env {
                                        constructors,
                                        module_path,
                                        token_map,
                                        imports,
                                    },
                                    module_path,
                                )?;
                                Ok(Field {
                                    type_: t,
                                    name: Path::from_str(module_path, &name.0),
                                    is_public: true,
                                })
                            })
                            .try_collect()?,
                        type_variables: &a.type_variables,
                        decl_id,
                        is_public: a.is_public,
                    });
                }
                parser::Decl::OpPrecedence(OpPrecedenceDecl { .. }) => (),
                parser::Decl::TypeAlias(a) => aliases.push(a),
                parser::Decl::Interface(a) => interfaces.push(a),
                parser::Decl::Module {
                    name,
                    ast,
                    is_public,
                } => {
                    modules.push((
                        Path::from_str(module_path, &name.0),
                        ast,
                        is_public,
                    ));
                }
                parser::Decl::Use { .. } => {}
            }
        }
        let modules = modules
            .into_iter()
            .map(|(name, ast, is_public)| {
                Ok(Module {
                    name,
                    ast: Ast::from_rec(
                        ast,
                        name,
                        token_map,
                        constructors,
                        imports,
                    )?,
                    is_public: *is_public,
                })
            })
            .try_collect()?;
        Ok(Ast {
            variable_decl: vs
                .into_iter()
                .map(|v| {
                    variable_decl(
                        v,
                        &mut Env {
                            constructors,
                            module_path,
                            token_map,
                            imports,
                        },
                        module_path,
                    )
                })
                .try_collect()?,
            data_decl: ds,
            type_alias_decl: aliases
                .into_iter()
                .map(|a| {
                    Ok(TypeAliasDecl {
                        name: (&a.name.0, a.name.1.clone(), a.name.2),
                        body: (
                            fold_op_sequence(
                                &a.body.0,
                                &mut Env {
                                    constructors,
                                    module_path,
                                    token_map,
                                    imports,
                                },
                                module_path,
                            )?
                            .0,
                            &a.body.1,
                        ),
                        is_public: a.is_public,
                    })
                })
                .try_collect()?,
            interface_decl: interfaces
                .into_iter()
                .map(|a| {
                    Ok(InterfaceDecl {
                        name: (&a.name.0, a.name.1.clone(), a.name.2),
                        variables: a
                            .variables
                            .iter()
                            .map(|((name, span, id), t, forall)| {
                                Ok((
                                    (name.as_str(), span.clone(), *id),
                                    fold_op_sequence(
                                        t,
                                        &mut Env {
                                            constructors,
                                            module_path,
                                            token_map,
                                            imports,
                                        },
                                        module_path,
                                    )?
                                    .0,
                                    forall,
                                ))
                            })
                            .try_collect()?,
                        is_public: a.is_public,
                    })
                })
                .try_collect()?,
            modules,
        })
    }

    fn collect_constructors_and_public_names(
        ast: &'a parser::Ast,
        constructors: &mut FxHashSet<&'a str>,
        module_path: Path,
        imports: &mut Imports,
    ) {
        for d in &ast.decls {
            match d {
                parser::Decl::Data(d) => {
                    constructors.insert(&d.name.0);
                }
                parser::Decl::Module {
                    ast,
                    name,
                    is_public: _,
                } => Self::collect_constructors_and_public_names(
                    ast,
                    constructors,
                    Path::from_str(module_path, &name.0),
                    imports,
                ),
                parser::Decl::Variable(_) => (),
                parser::Decl::OpPrecedence(op) => imports.add_op_precedence(
                    Path::from_str(module_path, &op.name),
                    op.associativity,
                    op.precedence,
                    op.is_public,
                ),
                parser::Decl::TypeAlias(_) => (),
                parser::Decl::Interface(_) => (),
                parser::Decl::Use { path, is_public } => {
                    imports.insert_name_alias(
                        Path::from_str(
                            module_path,
                            &path.path.last().unwrap().0,
                        ),
                        if path.from_root {
                            Path::pkg_root()
                        } else {
                            module_path
                        },
                        path.path.clone(),
                        *is_public,
                    );
                }
            }
        }
        if module_path != Path::prelude() {
            imports.insert_wild_card_import(
                module_path,
                Path::prelude(),
                Vec::new(),
                false,
            );
        }
    }

    pub fn from(
        ast: &'a parser::Ast,
        imports: &mut Imports,
    ) -> Result<(Self, TokenMap), CompileError> {
        let mut token_map = TokenMap::default();
        let mut constructors =
            INTRINSIC_CONSTRUCTORS.keys().map(|s| s.as_str()).collect();
        Self::collect_constructors_and_public_names(
            ast,
            &mut constructors,
            Path::root(),
            imports,
        );
        let a = Self::from_rec(
            ast,
            Path::root(),
            &mut token_map,
            &mut constructors,
            imports,
        )?;
        Ok((a, token_map))
    }
}

fn expr<'a>(
    e: &'a parser::Expr,
    env: &mut Env,
    module_path: Path,
) -> Result<ExprWithSpan<'a>, CompileError> {
    let value = fold_op_sequence(&e.0, env, module_path)?;
    if let Some((annotation, forall)) = &e.1 {
        let (t, _span) = fold_op_sequence(annotation, env, module_path)?;
        let span = value.1.clone();
        Ok((Expr::TypeAnnotation(Box::new(value), t, forall), span))
    } else {
        Ok(value)
    }
}

fn variable_decl<'a>(
    v: &'a parser::VariableDecl,
    env: &mut Env,
    module_path: Path,
) -> Result<VariableDecl<'a>, CompileError> {
    let decl_id = DeclId::new();
    env.token_map.insert(v.name.2, TokenMapEntry::Decl(decl_id));
    Ok(VariableDecl {
        name: Path::from_str(env.module_path, &v.name.0),
        type_annotation: v
            .type_annotation
            .as_ref()
            .map(|(s, forall)| {
                let (t, span) = fold_op_sequence(s, env, module_path)?;
                Ok((t, forall, span))
            })
            .transpose()?,
        value: expr(&v.expr, env, module_path)?,
        span: v.span.clone(),
        is_public: v.is_public,
        decl_id,
    })
}

fn apply_type_op<'a, T: IdentFromStr<'a> + Clone + Debug>(
    mut sequence: IndexList<OpSequenceUnit<'a, (T, Span)>>,
    i: Index,
    env: &mut Env,
    module_path: Path,
) -> Result<IndexList<OpSequenceUnit<'a, (T, Span)>>, CompileError>
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
                    sequence =
                        apply_type_op(sequence, i_prev, env, module_path)?;
                    sequence = apply_type_op(sequence, i, env, module_path)?;
                }
                _ => panic!(),
            }
        }
        Some(OpSequenceUnit::Apply(a)) => {
            match sequence.get_mut(i_prev).unwrap() {
                OpSequenceUnit::Operand(e) => {
                    *e = e.clone().apply_suffix_op(a, env, module_path)?;
                    sequence.remove(i);
                }
                OpSequenceUnit::Apply(_) => {
                    sequence =
                        apply_type_op(sequence, i_prev, env, module_path)?;
                    sequence = apply_type_op(sequence, i, env, module_path)?;
                }
                _ => panic!(),
            }
        }
        None => panic!("specified index is not valid."),
        Some(OpSequenceUnit::Operand(a)) => {
            panic!("specified position is a operand {a:?}")
        }
    }
    Ok(sequence)
}

fn op_apply_left<'a, T: IdentFromStr<'a> + Clone + Debug>(
    mut sequence: Vec<OpSequenceUnit<'a, (T, Span)>>,
    precedence: i32,
    env: &mut Env,
    module_path: Path,
) -> Result<Vec<OpSequenceUnit<'a, (T, Span)>>, CompileError>
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
                    sequence =
                        apply_type_op(sequence, next_i, env, module_path)?
                }
                _ => {
                    i = sequence.next_index(i);
                }
            }
        } else {
            break;
        }
    }
    Ok(sequence.drain_iter().collect())
}

fn op_apply_right<'a, T: IdentFromStr<'a> + Clone + Debug>(
    mut sequence: Vec<OpSequenceUnit<'a, (T, Span)>>,
    precedence: i32,
    env: &mut Env,
    module_path: Path,
) -> Result<Vec<OpSequenceUnit<'a, (T, Span)>>, CompileError>
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
                    sequence =
                        apply_type_op(sequence, i_next, env, module_path)?
                }
                _ => (),
            }
            i = sequence.prev_index(i);
        } else {
            break;
        }
    }
    Ok(sequence.drain_iter().collect())
}

impl<'a> ConvertWithOpPrecedenceMap for (&'a parser::TypeUnit, &'a Span) {
    type T = (Type<'a>, Span);

    fn convert(
        self,
        env: &mut Env,
        module_path: Path,
    ) -> Result<Self::T, CompileError> {
        match self.0 {
            parser::TypeUnit::Ident { path } => Ok((
                Type {
                    args: Vec::new(),
                    path,
                },
                self.1.clone(),
            )),
            parser::TypeUnit::Paren(s) => fold_op_sequence(s, env, module_path),
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
    module_path: Path,
) -> Result<(U, Span), CompileError>
where
    (U, Span): AddArgument + ApplySuffixOp<'a>,
    (&'a T, &'a Span): ConvertWithOpPrecedenceMap<T = (U, Span)>,
    <(U, Span) as ApplySuffixOp<'a>>::Op: Clone + Debug,
    U: IdentFromStr<'a> + Clone + Debug,
{
    use OpSequenceUnit::*;
    let mut s: Vec<_> = s
        .iter()
        .map(|u| match u {
            parser::OpSequenceUnit::Operand((e, e_span)) => {
                Ok(Operand((e, e_span).convert(env, module_path)?))
            }
            parser::OpSequenceUnit::Op(a, span) => {
                let (ass, p) = env.imports.get_op_precedence(
                    module_path,
                    module_path,
                    &a.path.last().unwrap().0,
                    Some(span.clone()),
                    env.token_map,
                )?;
                Ok(Operator(a, ass, p, span.clone()))
            }
            parser::OpSequenceUnit::Apply(a) => Ok(Apply(a)),
        })
        .try_collect()?;
    let mut precedence_list = BTreeMap::new();
    for op in &s {
        match op {
            OpSequenceUnit::Operand(_) => (),
            OpSequenceUnit::Operator(_, Associativity::Left, p, _) => {
                if let Some(Associativity::Right) =
                    precedence_list.insert(*p, Associativity::Left)
                {
                    panic!("cannot mix infixl {p} and infixr {p}");
                }
            }
            OpSequenceUnit::Operator(_, Associativity::Right, p, _) => {
                if let Some(Associativity::Left) =
                    precedence_list.insert(*p, Associativity::Right)
                {
                    panic!("cannot mix infixl {p} and infixr {p}");
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
                s = op_apply_left(s, p, env, module_path)?
            }
            Associativity::Right => s = op_apply_right(s, p, env, module_path)?,
        }
    }
    debug_assert_eq!(s.len(), 1);
    if let OpSequenceUnit::Operand(t) = &s[0] {
        Ok(t.clone())
    } else {
        panic!()
    }
}

trait ConvertWithOpPrecedenceMap {
    type T;
    fn convert(
        self,
        env: &mut Env,
        module_path: Path,
    ) -> Result<Self::T, CompileError>;
}

impl<'a> ConvertWithOpPrecedenceMap for (&'a parser::ExprUnit, &'a Span) {
    type T = ExprWithSpan<'a>;

    fn convert(
        self,
        env: &mut Env,
        module_path: Path,
    ) -> Result<Self::T, CompileError> {
        use Expr::*;
        let e = match &self.0 {
            parser::ExprUnit::Case(arms) => Lambda(
                arms.iter()
                    .map(|a| fn_arm(a, env, module_path))
                    .try_collect()?,
            ),
            parser::ExprUnit::Int(a) => Number(a),
            parser::ExprUnit::Str(a) => StrLiteral(a),
            parser::ExprUnit::Ident { path } => Ident { path },
            parser::ExprUnit::VariableDecl(a) => {
                Decl(Box::new(variable_decl(a, env, module_path)?))
            }
            parser::ExprUnit::Paren(a) => expr(a, env, module_path)?.0,
            parser::ExprUnit::Do(es) => Do(es
                .iter()
                .map(|e| expr(e, env, module_path))
                .try_collect()?),
            parser::ExprUnit::Record { path, fields } => Record {
                path,
                fields: fields
                    .iter()
                    .map(|(f, e)| {
                        Ok((
                            (f.0.as_str(), f.1.clone(), f.2),
                            expr(e, env, module_path)?.0,
                        ))
                    })
                    .try_collect()?,
            },
        };
        Ok((e, self.1.clone()))
    }
}

fn fn_arm<'a>(
    a: &'a parser::FnArm,
    env: &mut Env,
    module_path: Path,
) -> Result<FnArm<'a>, CompileError> {
    Ok(FnArm {
        pattern: a
            .pattern
            .iter()
            .map(|s| fold_op_sequence(s, env, module_path))
            .try_collect()?,
        expr: expr(&a.expr, env, module_path)?,
    })
}

impl<'a> ConvertWithOpPrecedenceMap for (&'a parser::PatternUnit, &'a Span) {
    type T = (Pattern<'a>, Span);

    fn convert(
        self,
        env: &mut Env,
        module_path: Path,
    ) -> Result<Self::T, CompileError> {
        let a = match &self.0 {
            parser::PatternUnit::Int(a) => Pattern::Number(a),
            parser::PatternUnit::Str(a) => Pattern::StrLiteral(a),
            parser::PatternUnit::Ident(path, ps) => {
                if env
                    .constructors
                    .contains(path.path.last().unwrap().0.as_str())
                {
                    Pattern::Constructor {
                        path,
                        args: ps
                            .iter()
                            .map(|p| fold_op_sequence(p, env, module_path))
                            .try_collect()?,
                    }
                } else {
                    assert!(ps.is_empty());
                    debug_assert!(!path.from_root);
                    debug_assert_eq!(path.path.len(), 1);
                    let name = &path.path[0];
                    Pattern::Binder((&name.0, name.1.clone(), name.2))
                }
            }
            parser::PatternUnit::Underscore => Pattern::Underscore,
            parser::PatternUnit::TypeRestriction(p, t, forall) => {
                Pattern::TypeRestriction(
                    Box::new(fold_op_sequence(p, env, module_path)?.0),
                    fold_op_sequence(t, env, module_path)?.0,
                    forall,
                )
            }
            parser::PatternUnit::Apply(pre_pattern, applications) => {
                Pattern::Apply(
                    Box::new(
                        (&pre_pattern.0, &pre_pattern.1)
                            .convert(env, module_path)?
                            .0,
                    ),
                    applications
                        .iter()
                        .map(|a| {
                            Ok(ApplyPattern {
                                function: expr(&a.function, env, module_path)?,
                                post_pattern: fold_op_sequence(
                                    &a.post_pattern,
                                    env,
                                    module_path,
                                )?,
                            })
                        })
                        .try_collect()?,
                )
            }
        };
        Ok((a, self.1.clone()))
    }
}
