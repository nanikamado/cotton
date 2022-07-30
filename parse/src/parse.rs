use crate::lex::{Span, Token};
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::{prelude::*, Error, Stream};

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Forall {
    pub type_variables: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub name: String,
    pub type_annotation: Option<(Type, Forall)>,
    pub expr: Expr,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OpSequenceUnit<T> {
    Operand(T),
    Op(String),
    Apply(Vec<OpSequenceUnit<T>>),
}

pub type Expr = Vec<OpSequenceUnit<ExprUnit>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExprUnit {
    Int(String),
    Str(String),
    Ident(String),
    Case(Vec<FnArm>),
    Paren(Expr),
    Do(Vec<Expr>),
    VariableDecl(VariableDecl),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeUnit {
    Ident(String),
    Paren(Type),
}

pub type Type = Vec<OpSequenceUnit<TypeUnit>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit {
    Int(String),
    Str(String),
    Constructor(String, Vec<Pattern>),
    Underscore,
    Bind(String),
}

pub type Pattern = Vec<OpSequenceUnit<PatternUnit>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm {
    pub pattern: Vec<Pattern>,
    pub pattern_type: Vec<Option<Type>>,
    pub expr: Expr,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OpPrecedenceDecl {
    pub name: String,
    pub associativity: Associativity,
    pub precedence: i32,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Associativity {
    Left,
    Right,
    UnaryLeft,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: String,
    pub field_len: usize,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Decl {
    Variable(VariableDecl),
    OpPrecedence(OpPrecedenceDecl),
    Data(DataDecl),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Ast {
    pub decls: Vec<Decl>,
}

fn indented<'a, O: 'a + Clone, E: 'a + Error<Token> + Clone>(
    p: impl 'a + Parser<Token, O, Error = E> + Clone,
) -> Recursive<'a, Token, O, E> {
    recursive(|indented| {
        let indented = indented.or(p);
        indented
            .clone()
            .delimited_by(just(Token::Indent), just(Token::Dedent))
            .or(indented.delimited_by(
                just(Token::Paren('{')),
                just(Token::Paren('}')),
            ))
    })
}

fn parser() -> impl Parser<Token, Vec<Decl>, Error = Simple<Token>> {
    let int = select! { Token::Int(i) => i };
    let str = select! { Token::Str(s) => s };
    let op = select! { Token::Op(s) => s };
    let ident = select! { Token::Ident(ident) => ident };
    let capital_head_ident =
        select! { Token::CapitalHeadIdent(ident) => ident };
    let ident = ident.or(capital_head_ident);
    let open_paren =
        just(Token::Paren('(')).or(just(Token::OpenParenWithoutPad));
    let ident_or_op = ident.or(
        op.delimited_by(open_paren.clone(), just(Token::Paren(')')))
    );
    let pattern = recursive(|pattern| {
        let constructor_pattern = capital_head_ident
            .then(
                pattern
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(
                        open_paren.clone(),
                        just(Token::Paren(')')),
                    )
                    .or_not(),
            )
            .map(|(name, args)| {
                PatternUnit::Constructor(
                    name,
                    args.unwrap_or_default(),
                )
            });
        let pattern_unit = constructor_pattern
            .or(just(Token::Op("_".to_string()))
                .map(|_| PatternUnit::Underscore))
            .or(ident.map(PatternUnit::Bind))
            .or(int.map(PatternUnit::Int))
            .or(str.map(PatternUnit::Str));
        pattern_unit
            .clone()
            .then(
                op.then(pattern_unit.clone())
                    .map(|(o, e)| {
                        vec![
                            OpSequenceUnit::Op(o),
                            OpSequenceUnit::Operand(e),
                        ]
                    })
                    .repeated()
                    .flatten(),
            )
            .map(|(e, oes)| {
                [vec![OpSequenceUnit::Operand(e)], oes].concat()
            })
    });
    let patterns = pattern
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .at_least(1);
    let forall = just(Token::Forall)
        .ignore_then(indented(
            ident.separated_by(just(Token::Comma)).allow_trailing(),
        ))
        .map(|type_variable_names| Forall {
            type_variables: type_variable_names,
        });
    let type_ = recursive(|type_| {
        let type_unit = ident.map(TypeUnit::Ident).or(type_
            .clone()
            .delimited_by(open_paren.clone(), just(Token::Paren(')')))
            .map(TypeUnit::Paren));
        let apply = type_
            .separated_by(just(Token::Comma))
            .at_least(1)
            .allow_trailing()
            .delimited_by(
                just(Token::Paren('[')),
                just(Token::Paren(']')),
            )
            .map(|es| {
                es.into_iter().map(OpSequenceUnit::Apply).collect()
            });
        type_unit
            .clone()
            .then(
                op.or(just(Token::Bar).map(|_| "|".to_string()))
                    .then(type_unit.clone())
                    .map(|(o, e)| {
                        vec![
                            OpSequenceUnit::Op(o),
                            OpSequenceUnit::Operand(e),
                        ]
                    })
                    .or(apply)
                    .repeated()
                    .flatten(),
            )
            .map(|(e, oes)| {
                [vec![OpSequenceUnit::Operand(e)], oes].concat()
            })
    });
    let type_ = type_.then(forall.or_not()).map(|(t, forall)| {
        (
            t,
            forall.unwrap_or_else(|| Forall {
                type_variables: Vec::new(),
            }),
        )
    });
    let variable_decl = recursive(|variable_decl| {
        let expr = recursive(|expr| {
            let lambda = just(Token::Bar)
                .ignore_then(patterns)
                .then_ignore(just(Token::BArrow))
                .then(expr.clone())
                .map(|(pattern, expr)| {
                    let l = pattern.len();
                    FnArm {
                        pattern,
                        expr,
                        pattern_type: vec![None; l],
                    }
                });
            let case = just(Token::Case)
                .or_not()
                .ignore_then(indented(
                    lambda.clone().repeated().at_least(1),
                ))
                .map(ExprUnit::Case);
            let do_ = just(Token::Do)
                .ignore_then(indented(expr.clone().repeated()))
                .map(ExprUnit::Do);
            let expr_unit = do_
                .or(case)
                .or(int.map(ExprUnit::Int))
                .or(str.map(ExprUnit::Str))
                .or(variable_decl.map(ExprUnit::VariableDecl))
                .or(ident_or_op.clone().map(ExprUnit::Ident))
                .or(lambda.map(|a| ExprUnit::Case(vec![a])))
                .or(expr
                    .clone()
                    .delimited_by(open_paren, just(Token::Paren(')')))
                    .map(ExprUnit::Paren));
            let apply = expr
                .separated_by(just(Token::Comma))
                .at_least(1)
                .allow_trailing()
                .delimited_by(
                    just(Token::OpenParenWithoutPad),
                    just(Token::Paren(')')),
                )
                .map(|es| {
                    es.into_iter()
                        .map(OpSequenceUnit::Apply)
                        .collect()
                });
            expr_unit
                .clone()
                .then(
                    op.then(expr_unit.clone())
                        .map(|(o, e)| {
                            vec![
                                OpSequenceUnit::Op(o),
                                OpSequenceUnit::Operand(e),
                            ]
                        })
                        .or(apply)
                        .repeated()
                        .flatten(),
                )
                .map(|(e, oes)| {
                    [vec![OpSequenceUnit::Operand(e)], oes].concat()
                })
        });
        ident_or_op
            .clone()
            .then(
                just(Token::Colon)
                    .ignore_then(type_.clone())
                    .or_not(),
            )
            .then_ignore(just(Token::Assign))
            .then(expr)
            .map(|((name, type_annotation), expr)| VariableDecl {
                name,
                type_annotation,
                expr,
            })
    });
    let op_precedence_decl = just(Token::Infixl)
        .map(|_| Associativity::Left)
        .or(just(Token::Infixr).map(|_| Associativity::Right))
        .then(int)
        .then(op)
        .map(|((associativity, i), name)| OpPrecedenceDecl {
            name,
            associativity,
            precedence: i.parse().unwrap(),
        });
    let data_decl_normal = capital_head_ident
        .then(
            ident_or_op
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .delimited_by(
                    just(Token::OpenParenWithoutPad),
                    just(Token::Paren(')')),
                )
                .or_not(),
        )
        .map(|(name, args)| DataDecl {
            name,
            field_len: args.unwrap_or_default().len(),
        });
    let data_decl_infix = ident
        .ignore_then(op)
        .then_ignore(ident)
        .map(|name| DataDecl { name, field_len: 2 });
    let data_decl = just(Token::Data)
        .ignore_then(data_decl_normal.or(data_decl_infix));
    variable_decl
        .map(Decl::Variable)
        .or(op_precedence_decl.map(Decl::OpPrecedence))
        .or(data_decl.map(Decl::Data))
        .repeated()
        .at_least(1)
        .then_ignore(end())
}

pub(crate) fn parse(
    ts: Vec<(Token, Span)>,
    src: &str,
    src_len: usize,
) -> Ast {
    let r = parser().parse(Stream::from_iter(
        src_len..src_len + 1,
        ts.into_iter(),
    ));
    match r {
        Ok(decls) => Ast { decls },
        Err(es) => {
            for e in es {
                let e = e.map(|c| format!("{:?}", c));
                let report = Report::build(
                    ReportKind::Error,
                    (),
                    e.span().start,
                );
                let report = match e.reason() {
                    chumsky::error::SimpleReason::Unclosed {
                        span,
                        delimiter,
                    } => report
                        .with_message(format!(
                            "Unclosed delimiter {}",
                            delimiter.fg(Color::Yellow)
                        ))
                        .with_label(
                            Label::new(span.clone())
                                .with_message(format!(
                                    "Unclosed delimiter {}",
                                    delimiter.fg(Color::Yellow)
                                ))
                                .with_color(Color::Yellow),
                        )
                        .with_label(
                            Label::new(e.span())
                                .with_message(format!(
                                    "Must be closed before this {}",
                                    e.found()
                                        .unwrap_or(
                                            &"end of file"
                                                .to_string()
                                        )
                                        .fg(Color::Red)
                                ))
                                .with_color(Color::Red),
                        ),
                    chumsky::error::SimpleReason::Unexpected => {
                        report
                            .with_message(format!(
                                "{}, expected {}",
                                if e.found().is_some() {
                                    "Unexpected token in input"
                                } else {
                                    "Unexpected end of input"
                                },
                                if e.expected().len() == 0 {
                                    "something else".to_string()
                                } else {
                                    e.expected()
                                        .map(
                                            |expected| match expected
                                            {
                                                Some(expected) => {
                                                    expected
                                                        .to_string()
                                                }
                                                None => {
                                                    "end of input"
                                                        .to_string()
                                                }
                                            },
                                        )
                                        .collect::<Vec<_>>()
                                        .join(", ")
                                }
                            ))
                            .with_label(
                                Label::new(e.span())
                                    .with_message(format!(
                                        "Unexpected token {}",
                                        e.found()
                                            .unwrap_or(
                                                &"end of file"
                                                    .to_string()
                                            )
                                            .fg(Color::Red)
                                    ))
                                    .with_color(Color::Red),
                            )
                    }
                    chumsky::error::SimpleReason::Custom(msg) => {
                        report.with_message(msg).with_label(
                            Label::new(e.span())
                                .with_message(format!(
                                    "{}",
                                    msg.fg(Color::Red)
                                ))
                                .with_color(Color::Red),
                        )
                    }
                };
                report.finish().eprint(Source::from(&src)).unwrap();
            }
            std::process::exit(1)
        }
    }
}
