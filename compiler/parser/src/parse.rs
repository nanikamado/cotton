use crate::{
    lex::{Span, Token},
    token_id::TokenId,
};
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::{prelude::*, Error, Stream};

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Forall {
    pub type_variables: Vec<(StringWithId, Vec<StringWithId>)>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub name: StringWithId,
    pub type_annotation: Option<(Type, Forall)>,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OpSequenceUnit<T, U> {
    Operand(T),
    Op(StringWithId, Span),
    Apply(U),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExprSuffixOp {
    Apply(Expr),
    Question(Span),
}

pub type Expr = Vec<OpSequenceUnit<(ExprUnit, Span), ExprSuffixOp>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExprUnit {
    Int(String),
    Str(String),
    Ident(StringWithId),
    Case(Vec<FnArm>),
    Paren(Expr),
    Do(Vec<Expr>),
    VariableDecl(VariableDecl),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeUnit {
    Ident(StringWithId),
    Paren(Type),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeApply(pub Type);

pub type StringWithId = (String, Option<TokenId>);
pub type Type = Vec<OpSequenceUnit<(TypeUnit, Span), TypeApply>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit {
    Int(String),
    Str(String),
    Ident(StringWithId, Vec<Pattern>),
    Underscore,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PatternApply(pub Pattern);
pub type Pattern = Vec<OpSequenceUnit<(PatternUnit, Span), PatternApply>>;

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
    pub name: StringWithId,
    pub fields: Vec<StringWithId>,
    pub type_variables: Forall,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeAliasDecl {
    pub name: StringWithId,
    pub body: (Type, Forall),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InterfaceDecl {
    pub name: StringWithId,
    pub variables: Vec<(StringWithId, Type, Forall)>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Decl {
    Variable(VariableDecl),
    OpPrecedence(OpPrecedenceDecl),
    Data(DataDecl),
    TypeAlias(TypeAliasDecl),
    Interface(InterfaceDecl),
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
            .or(indented
                .delimited_by(just(Token::Paren('{')), just(Token::Paren('}'))))
    })
}

fn parser() -> impl Parser<Token, Vec<Decl>, Error = Simple<Token>> {
    let int = select! { Token::Int(i) => i };
    let str = select! { Token::Str(s) => s };
    let op = select! { Token::Op(s, id) => (s, id) };
    let ident = select! { Token::Ident(ident, id) => (ident, id) };
    let underscore =
        select! { Token::Ident(ident, id) if ident == "_" => (ident, id) };
    let and = select! { Token::Op(ident, id) if ident == "&" => (ident, id) };
    // let capital_head_ident =
    //     select! { Token::CapitalHeadIdent(ident) => ident };
    // let ident = ident.or(capital_head_ident);
    let open_paren =
        just(Token::Paren('(')).or(just(Token::OpenParenWithoutPad));
    let ident_or_op =
        ident.or(op.delimited_by(open_paren.clone(), just(Token::Paren(')'))));
    let pattern = recursive(|pattern| {
        let constructor_pattern = ident
            .then(
                pattern
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(open_paren.clone(), just(Token::Paren(')')))
                    .or_not(),
            )
            .map(|((name, id), args)| {
                PatternUnit::Ident((name, Some(id)), args.unwrap_or_default())
            });
        let pattern_unit = constructor_pattern
            .or(underscore.map(|_| PatternUnit::Underscore))
            .or(int.map(PatternUnit::Int))
            .or(str.map(PatternUnit::Str));
        pattern_unit
            .clone()
            .map_with_span(|p, s: Span| (p, s))
            .then(
                op.map_with_span(|op, span: Span| (op, span))
                    .then(
                        pattern_unit.clone().map_with_span(|p, s: Span| (p, s)),
                    )
                    .map(|(((s, id), s_span), (e, e_span))| {
                        vec![
                            OpSequenceUnit::Op((s, Some(id)), s_span),
                            OpSequenceUnit::Operand((e, e_span)),
                        ]
                    })
                    .repeated()
                    .flatten(),
            )
            .map(|((e, e_span), oes)| {
                [vec![OpSequenceUnit::Operand((e, e_span))], oes].concat()
            })
    });
    let patterns = pattern
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .at_least(1);
    let forall = just(Token::Forall)
        .ignore_then(indented(
            ident
                .then(
                    just(Token::Colon)
                        .ignore_then(ident.separated_by(and))
                        .or_not(),
                )
                .separated_by(just(Token::Comma))
                .allow_trailing(),
        ))
        .map(|type_variable_names| Forall {
            type_variables: type_variable_names
                .into_iter()
                .map(|((n, id), t)| {
                    (
                        (n, Some(id)),
                        t.into_iter()
                            .flatten()
                            .map(|(n, id)| (n, Some(id)))
                            .collect(),
                    )
                })
                .collect(),
        });
    let type_ = recursive(|type_| {
        let type_unit =
            ident.map(|(s, id)| TypeUnit::Ident((s, Some(id)))).or(type_
                .clone()
                .delimited_by(open_paren.clone(), just(Token::Paren(')')))
                .map(TypeUnit::Paren));
        let apply = type_
            .separated_by(just(Token::Comma))
            .at_least(1)
            .allow_trailing()
            .delimited_by(just(Token::Paren('[')), just(Token::Paren(']')))
            .map(|es| {
                es.into_iter()
                    .map(|e| OpSequenceUnit::Apply(TypeApply(e)))
                    .collect()
            });
        type_unit
            .clone()
            .map_with_span(|t, s: Span| (t, s))
            .then(
                op.map_with_span(|(s, id), span: Span| (s, Some(id), span))
                    .or(just(Token::Bar)
                        .map_with_span(|_, span| ("|".to_string(), None, span)))
                    .then(type_unit.clone())
                    .map_with_span(|((o, o_token, o_span), e), span: Span| {
                        vec![
                            OpSequenceUnit::Op((o, o_token), o_span),
                            OpSequenceUnit::Operand((e, span)),
                        ]
                    })
                    .or(apply)
                    .repeated()
                    .flatten(),
            )
            .map(|((e, e_span), oes)| {
                [vec![OpSequenceUnit::Operand((e, e_span))], oes].concat()
            })
    });
    let type_ = type_.then(forall.clone().or_not()).map(|(t, forall)| {
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
                .ignore_then(indented(lambda.clone().repeated().at_least(1)))
                .map(ExprUnit::Case);
            let do_ = just(Token::Do)
                .ignore_then(indented(expr.clone().repeated()))
                .map(ExprUnit::Do);
            let expr_unit = do_
                .or(case)
                .or(int.map(ExprUnit::Int))
                .or(str.map(ExprUnit::Str))
                .or(variable_decl.map(ExprUnit::VariableDecl))
                .or(ident_or_op
                    .clone()
                    .map(|(s, id)| ExprUnit::Ident((s, Some(id)))))
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
                        .map(|e| OpSequenceUnit::Apply(ExprSuffixOp::Apply(e)))
                        .collect()
                });
            expr_unit
                .clone()
                .map_with_span(|e, s| (e, s))
                .then(
                    op.map_with_span(|op, span: Span| (op, span))
                        .then(
                            expr_unit
                                .clone()
                                .map_with_span(|e, span| (e, span)),
                        )
                        .map(|(((s, id), s_span), (e, e_span))| {
                            vec![
                                OpSequenceUnit::Op((s, Some(id)), s_span),
                                OpSequenceUnit::Operand((e, e_span)),
                            ]
                        })
                        .or(apply)
                        .or(just(Token::Question).map_with_span(|_, span| {
                            vec![OpSequenceUnit::Apply(ExprSuffixOp::Question(
                                span,
                            ))]
                        }))
                        .repeated()
                        .flatten(),
                )
                .map(|(e, oes)| {
                    [vec![OpSequenceUnit::Operand(e)], oes].concat()
                })
        });
        ident_or_op
            .clone()
            .then(just(Token::Colon).ignore_then(type_.clone()).or_not())
            .then_ignore(just(Token::Assign))
            .then(expr)
            .map_with_span(|(((name, id), type_annotation), expr), span| {
                VariableDecl {
                    name: (name, Some(id)),
                    type_annotation,
                    expr,
                    span,
                }
            })
    });
    let op_precedence_decl = just(Token::Infixl)
        .map(|_| Associativity::Left)
        .or(just(Token::Infixr).map(|_| Associativity::Right))
        .then(int)
        .then(op)
        .map(|((associativity, i), (name, _token_id))| OpPrecedenceDecl {
            name,
            associativity,
            precedence: i.parse().unwrap(),
        });
    let data_decl_normal = ident
        .then(
            ident_or_op
                .clone()
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .delimited_by(
                    just(Token::OpenParenWithoutPad),
                    just(Token::Paren(')')),
                )
                .or_not(),
        )
        .then(forall.clone().or_not())
        .map(|(((name, id), args), forall)| DataDecl {
            name: (name, Some(id)),
            fields: args
                .unwrap_or_default()
                .into_iter()
                .map(|(name, id)| (name, Some(id)))
                .collect(),
            type_variables: forall.unwrap_or_default(),
        });
    let data_decl_infix = ident.then(op).then(ident).then(forall.or_not()).map(
        |(
            (((ident1, ident1_id), (op, op_id)), (ident2, ident2_id)),
            forall,
        )| DataDecl {
            name: (op, Some(op_id)),
            fields: vec![(ident1, Some(ident1_id)), (ident2, Some(ident2_id))],
            type_variables: forall.unwrap_or_default(),
        },
    );
    let data_decl =
        just(Token::Data).ignore_then(data_decl_infix.or(data_decl_normal));
    let type_alias_decl = just(Token::Type)
        .ignore_then(ident)
        .then_ignore(just(Token::Assign))
        .then(type_.clone())
        .map(|((name, id), body)| {
            Decl::TypeAlias(TypeAliasDecl {
                name: (name, Some(id)),
                body,
            })
        });
    let interface_decl = ident
        .delimited_by(just(Token::Interface), just(Token::Where))
        .then(indented(
            ident_or_op
                .then_ignore(just(Token::Colon))
                .then(type_)
                .repeated(),
        ))
        .map(|((name, id), vs)| {
            Decl::Interface(InterfaceDecl {
                name: (name, Some(id)),
                variables: vs
                    .into_iter()
                    .map(|((n, id), (t, forall))| ((n, Some(id)), t, forall))
                    .collect(),
            })
        });
    variable_decl
        .map(Decl::Variable)
        .or(op_precedence_decl.map(Decl::OpPrecedence))
        .or(data_decl.map(Decl::Data))
        .or(type_alias_decl)
        .or(interface_decl)
        .repeated()
        .at_least(1)
        .then_ignore(end())
}

pub fn parse_result(
    ts: Vec<(Token, Span)>,
    src_len: usize,
) -> Result<Ast, Vec<Simple<Token>>> {
    parser()
        .parse(Stream::from_iter(src_len..src_len + 1, ts.into_iter()))
        .map(|decls| Ast { decls })
}

pub fn parse(ts: Vec<(Token, Span)>, src: &str, src_len: usize) -> Ast {
    let r = parse_result(ts, src_len);
    match r {
        Ok(ast) => ast,
        Err(es) => {
            for e in es {
                let e = e.map(|c| format!("{:?}", c));
                let report =
                    Report::build(ReportKind::Error, (), e.span().start);
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
                                        .unwrap_or(&"end of file".to_string())
                                        .fg(Color::Red)
                                ))
                                .with_color(Color::Red),
                        ),
                    chumsky::error::SimpleReason::Unexpected => report
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
                                    .map(|expected| match expected {
                                        Some(expected) => expected.to_string(),
                                        None => "end of input".to_string(),
                                    })
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            }
                        ))
                        .with_label(
                            Label::new(e.span())
                                .with_message(format!(
                                    "Unexpected token {}",
                                    e.found()
                                        .unwrap_or(&"end of file".to_string())
                                        .fg(Color::Red)
                                ))
                                .with_color(Color::Red),
                        ),
                    chumsky::error::SimpleReason::Custom(msg) => {
                        report.with_message(msg).with_label(
                            Label::new(e.span())
                                .with_message(format!("{}", msg.fg(Color::Red)))
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
