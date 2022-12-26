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
    pub is_public: bool,
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

pub type Expr = (
    Vec<OpSequenceUnit<(ExprUnit, Span), ExprSuffixOp>>,
    Option<(Type, Forall)>,
);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExprUnit {
    Int(String),
    Str(String),
    Ident {
        path: Vec<StringWithId>,
        name: StringWithId,
    },
    Case(Vec<FnArm>),
    Paren(Expr),
    Do(Vec<Expr>),
    VariableDecl(VariableDecl),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeUnit {
    Ident {
        name: StringWithId,
        path: Vec<StringWithId>,
    },
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
    TypeRestriction(Box<Pattern>, Type, Forall),
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
    pub is_public: bool,
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
    Module {
        name: StringWithId,
        ast: Ast,
        is_public: bool,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
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
    let op = select! { Token::Op(s, id) => (s, Some(id)) };
    let ident = select! { Token::Ident(ident, id) => (ident, Some(id)) };
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
    let ident_with_path = ident
        .then_ignore(just(Token::ColonColon))
        .repeated()
        .then(ident_or_op.clone());
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
                .map(|(n, t)| (n, t.unwrap_or_default()))
                .collect(),
        });
    let type_ = recursive(|type_| {
        let type_unit = ident_with_path
            .clone()
            .map(|(path, name)| TypeUnit::Ident { name, path })
            .or(type_
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
                op.map_with_span(|(s, id), span: Span| (s, id, span))
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
    let pattern = recursive(|pattern| {
        let constructor_pattern = ident
            .then(
                pattern
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(open_paren.clone(), just(Token::Paren(')')))
                    .or_not(),
            )
            .map(|(name, args)| {
                PatternUnit::Ident(name, args.unwrap_or_default())
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
                    .map(|((s, s_span), (e, e_span))| {
                        vec![
                            OpSequenceUnit::Op(s, s_span),
                            OpSequenceUnit::Operand((e, e_span)),
                        ]
                    })
                    .repeated()
                    .flatten(),
            )
            .then(
                just(Token::Colon)
                    .ignore_then(
                        type_
                            .clone()
                            .map_with_span(|op, span: Span| (op, span)),
                    )
                    .or_not(),
            )
            .map_with_span(|p, s: Span| (p, s))
            .map(|((((e, e_span), oes), type_annotation), whole_span)| {
                let p =
                    [vec![OpSequenceUnit::Operand((e, e_span))], oes].concat();
                if let Some(((type_restriction, forall), _type_span)) =
                    type_annotation
                {
                    vec![OpSequenceUnit::Operand((
                        PatternUnit::TypeRestriction(
                            Box::new(p),
                            type_restriction,
                            forall,
                        ),
                        whole_span,
                    ))]
                } else {
                    p
                }
            })
    });
    let patterns = pattern
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .at_least(1);
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
                .ignore_then(
                    indented(expr.clone().repeated())
                        .or(expr.clone().map(|e| vec![e])),
                )
                .map(ExprUnit::Do);
            let expr_unit = do_
                .or(case)
                .or(int.map(ExprUnit::Int))
                .or(str.map(ExprUnit::Str))
                .or(variable_decl.map(ExprUnit::VariableDecl))
                .or(ident_with_path
                    .map(|(path, name)| ExprUnit::Ident { path, name }))
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
                        .map(|((name, s_span), (e, e_span))| {
                            vec![
                                OpSequenceUnit::Op(name, s_span),
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
                .then(just(Token::Colon).ignore_then(type_.clone()).or_not())
                .map(|((e, oes), t)| {
                    ([vec![OpSequenceUnit::Operand(e)], oes].concat(), t)
                })
        });
        just(Token::Pub)
            .or_not()
            .then(ident_or_op.clone())
            .then(just(Token::Colon).ignore_then(type_.clone()).or_not())
            .then_ignore(just(Token::Assign))
            .then(expr)
            .map_with_span(
                |(((pub_or_not, name), type_annotation), expr), span| {
                    VariableDecl {
                        name,
                        type_annotation,
                        expr,
                        span,
                        is_public: pub_or_not.is_some(),
                    }
                },
            )
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
        .map(|((name, args), forall)| DataDecl {
            name,
            fields: args.unwrap_or_default(),
            type_variables: forall.unwrap_or_default(),
            is_public: false,
        });
    let data_decl_infix = ident.then(op).then(ident).then(forall.or_not()).map(
        |(((ident1, name), ident2), forall)| DataDecl {
            name,
            fields: vec![ident1, ident2],
            type_variables: forall.unwrap_or_default(),
            is_public: false,
        },
    );
    let data_decl = just(Token::Pub)
        .or_not()
        .then_ignore(just(Token::Data))
        .then(data_decl_infix.or(data_decl_normal))
        .map(|(pub_or_not, d)| {
            Decl::Data(DataDecl {
                is_public: pub_or_not.is_some(),
                ..d
            })
        });
    let type_alias_decl = just(Token::Type)
        .ignore_then(ident)
        .then_ignore(just(Token::Assign))
        .then(type_.clone())
        .map(|(name, body)| Decl::TypeAlias(TypeAliasDecl { name, body }));
    let interface_decl = ident
        .delimited_by(just(Token::Interface), just(Token::Where))
        .then(indented(
            ident_or_op
                .then_ignore(just(Token::Colon))
                .then(type_)
                .repeated(),
        ))
        .map(|(name, vs)| {
            Decl::Interface(InterfaceDecl {
                name,
                variables: vs
                    .into_iter()
                    .map(|(n, (t, forall))| (n, t, forall))
                    .collect(),
            })
        });
    recursive(|decl| {
        let mod_ = just(Token::Pub)
            .or_not()
            .then_ignore(just(Token::Mod))
            .then(ident)
            .then(indented(decl.repeated()))
            .map(|((pub_or_not, name), decls)| Decl::Module {
                name,
                ast: Ast { decls },
                is_public: pub_or_not.is_some(),
            });
        choice((
            variable_decl.map(Decl::Variable),
            op_precedence_decl.map(Decl::OpPrecedence),
            data_decl,
            type_alias_decl,
            interface_decl,
            mod_,
        ))
    })
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
