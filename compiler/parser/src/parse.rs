use crate::lex::{Span, Token};
use crate::token_id::TokenId;
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::prelude::*;
use chumsky::{Error, Stream};

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Forall {
    pub type_variables: Vec<(StringWithId, Vec<Path>)>,
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
    Op(Path, Span),
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

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Path {
    pub from_root: bool,
    pub path: Vec<StringWithId>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExprUnit {
    Int(String),
    Str(String),
    Ident {
        path: Path,
    },
    Record {
        path: Path,
        fields: Vec<(StringWithId, Expr)>,
    },
    Case(Vec<FnArm>),
    Paren(Expr),
    Do(Vec<Expr>),
    VariableDecl(VariableDecl),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeUnit {
    Ident { path: Path },
    Paren(Type),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeApply(pub Type);

pub type StringWithId = (String, Option<Span>, Option<TokenId>);
pub type Type = Vec<OpSequenceUnit<(TypeUnit, Span), TypeApply>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit {
    Int(String),
    Str(String),
    Ident(Path, Vec<Pattern>),
    Underscore,
    TypeRestriction(Box<Pattern>, Type, Forall),
    Apply(Box<(PatternUnit, Span)>, Vec<ApplyPattern>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ApplyPattern {
    pub function: Expr,
    pub post_pattern: Pattern,
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
    pub is_public: bool,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum Associativity {
    Left,
    Right,
    UnaryLeft,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: StringWithId,
    pub fields: Vec<Field>,
    pub type_variables: Forall,
    pub is_public: bool,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Field {
    pub name: StringWithId,
    pub type_: Type,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeAliasDecl {
    pub name: StringWithId,
    pub body: (Type, Forall),
    pub is_public: bool,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InterfaceDecl {
    pub name: StringWithId,
    pub variables: Vec<(StringWithId, Type, Forall)>,
    pub is_public: bool,
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
    Use {
        path: Path,
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
    let op = (select! { Token::Op(s, id) => (s, Some(id)) })
        .map_with_span(|(i, id), s| (i, Some(s), id));
    let ident = (select! { Token::Ident(ident, id) => (ident, Some(id)) })
        .map_with_span(|(i, id), s| (i, Some(s), id));
    let underscore =
        select! { Token::Ident(ident, id) if ident == "_" => (ident, id) };
    let and = select! { Token::Op(ident, id) if ident == "&" => (ident, id) };
    let open_paren =
        just(Token::Paren('(')).or(just(Token::OpenParenWithoutPad));
    let ident_or_op =
        ident.or(op.delimited_by(open_paren.clone(), just(Token::Paren(')'))));
    let ident_with_path = just(Token::ColonColon)
        .or_not()
        .then(
            ident
                .then_ignore(just(Token::ColonColon))
                .repeated()
                .chain(ident_or_op.clone()),
        )
        .map(|(root_no_not, path)| Path {
            from_root: root_no_not.is_some(),
            path,
        });
    let forall = just(Token::Forall)
        .ignore_then(indented(
            ident
                .then(
                    just(Token::Colon)
                        .ignore_then(ident_with_path.clone().separated_by(and))
                        .or_not(),
                )
                .separated_by(just(Token::Comma).or_not())
                .allow_trailing(),
        ))
        .map(|type_variable_names| Forall {
            type_variables: type_variable_names
                .into_iter()
                .map(|(n, t)| (n, t.unwrap_or_default()))
                .collect(),
        });
    let type_without_forall = recursive(|type_| {
        let type_unit = ident_with_path
            .clone()
            .map(|path| TypeUnit::Ident { path })
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
                op.map(|(s, span, id)| (s, id, span.unwrap()))
                    .or(just(Token::Bar)
                        .map_with_span(|_, span| ("|".to_string(), None, span)))
                    .then(type_unit.clone())
                    .map_with_span(|((o, o_token, o_span), e), span: Span| {
                        vec![
                            OpSequenceUnit::Op(
                                Path {
                                    from_root: false,
                                    path: vec![(
                                        o,
                                        Some(o_span.clone()),
                                        o_token,
                                    )],
                                },
                                o_span,
                            ),
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
    let type_unit = ident_with_path
        .clone()
        .map(|path| TypeUnit::Ident { path })
        .or(type_without_forall
            .clone()
            .delimited_by(open_paren.clone(), just(Token::Paren(')')))
            .map(TypeUnit::Paren));
    let type_ = type_without_forall
        .clone()
        .then(forall.clone().or_not())
        .map(|(t, forall)| {
            (
                t,
                forall.unwrap_or_else(|| Forall {
                    type_variables: Vec::new(),
                }),
            )
        });
    let variable_decl = recursive(|variable_decl| {
        let expr = recursive(|expr_without_type_annotation| {
            let expr = expr_without_type_annotation
                .clone()
                .then(just(Token::Colon).ignore_then(type_.clone()).or_not());
            let pattern = recursive(|pattern| {
                let constructor_pattern = ident_with_path
                    .clone()
                    .then(
                        pattern
                            .clone()
                            .separated_by(just(Token::Comma))
                            .allow_trailing()
                            .delimited_by(
                                open_paren.clone(),
                                just(Token::Paren(')')),
                            )
                            .or_not(),
                    )
                    .map(|(name, args)| {
                        PatternUnit::Ident(name, args.unwrap_or_default())
                    });
                let pattern_unit = choice((
                    constructor_pattern,
                    underscore.map(|_| PatternUnit::Underscore),
                    int.map(PatternUnit::Int),
                    str.map(PatternUnit::Str),
                ));
                let apply_filter = indented(
                    expr_without_type_annotation
                        .map(|e| (e, None))
                        .then_ignore(just(Token::Colon))
                        .then(pattern)
                        .map(|(function, post_pattern)| ApplyPattern {
                            function,
                            post_pattern,
                        })
                        .separated_by(just(Token::Comma))
                        .allow_trailing(),
                );
                let pattern_unit = pattern_unit
                    .clone()
                    .map_with_span(|p, s| (p, s))
                    .then(apply_filter.map_with_span(|a, s| (a, s)).repeated())
                    .foldl(|acc, a| {
                        (PatternUnit::Apply(Box::new(acc), a.0), a.1)
                    });
                pattern_unit
                    .clone()
                    .then(
                        op.map_with_span(|op, span: Span| (op, span))
                            .then(pattern_unit.clone())
                            .map(|((s, s_span), (e, e_span))| {
                                vec![
                                    OpSequenceUnit::Op(
                                        Path {
                                            from_root: false,
                                            path: vec![s],
                                        },
                                        s_span,
                                    ),
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
                    .map_with_span(
                        |(((e, e_span), oes), type_annotation), whole_span| {
                            let p = [
                                vec![OpSequenceUnit::Operand((e, e_span))],
                                oes,
                            ]
                            .concat();
                            if let Some((
                                (type_restriction, forall),
                                _type_span,
                            )) = type_annotation
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
                        },
                    )
            });
            let patterns = pattern
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .at_least(1);
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
            let expr_unit = choice((
                do_,
                case,
                int.map(ExprUnit::Int),
                str.map(ExprUnit::Str),
                variable_decl.map(ExprUnit::VariableDecl),
                ident_with_path
                    .clone()
                    .then(indented(
                        ident
                            .then_ignore(just(Token::Colon))
                            .then(expr.clone())
                            .separated_by(just(Token::Comma).or_not())
                            .allow_trailing(),
                    ))
                    .map(|(name, fields)| ExprUnit::Record {
                        path: name,
                        fields,
                    }),
                ident_with_path.clone().map(|path| ExprUnit::Ident { path }),
                lambda.map(|a| ExprUnit::Case(vec![a])),
                expr.clone()
                    .delimited_by(open_paren, just(Token::Paren(')')))
                    .map(ExprUnit::Paren),
            ));
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
                                OpSequenceUnit::Op(
                                    Path {
                                        from_root: false,
                                        path: vec![name],
                                    },
                                    s_span,
                                ),
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
        })
        .then(just(Token::Colon).ignore_then(type_.clone()).or_not());
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
    let op_precedence_decl = just(Token::Pub)
        .or_not()
        .then(
            just(Token::Infixl)
                .map(|_| Associativity::Left)
                .or(just(Token::Infixr).map(|_| Associativity::Right)),
        )
        .then(int)
        .then(op)
        .map(
            |(((pub_or_not, associativity), i), (name, _span, _token_id))| {
                OpPrecedenceDecl {
                    name,
                    associativity,
                    precedence: i.parse().unwrap(),
                    is_public: pub_or_not.is_some(),
                }
            },
        );
    let data_decl_normal = ident
        .then(
            type_without_forall
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
            fields: args
                .into_iter()
                .flatten()
                .enumerate()
                .map(|(i, type_)| Field {
                    name: (format!("_{i}"), None, None),
                    type_,
                })
                .collect(),
            type_variables: forall.unwrap_or_default(),
            is_public: false,
        });
    let data_decl_record = ident
        .then(indented(
            ident
                .then_ignore(just(Token::Colon))
                .then(type_without_forall.clone())
                .separated_by(just(Token::Comma).or_not())
                .allow_trailing(),
        ))
        .then(forall.clone().or_not())
        .map(|((name, args), forall)| DataDecl {
            name,
            fields: args
                .into_iter()
                .map(|(name, type_)| Field { name, type_ })
                .collect(),
            type_variables: forall.unwrap_or_default(),
            is_public: false,
        });
    let data_decl_infix = type_unit
        .clone()
        .map_with_span(|t, s| (t, s))
        .then(op)
        .then(type_unit.map_with_span(|t, s| (t, s)))
        .then(forall.or_not())
        .map(|(((ident1, name), ident2), forall)| DataDecl {
            name,
            fields: vec![
                Field {
                    name: ("_0".to_string(), None, None),
                    type_: vec![OpSequenceUnit::Operand(ident1)],
                },
                Field {
                    name: ("_1".to_string(), None, None),
                    type_: vec![OpSequenceUnit::Operand(ident2)],
                },
            ],
            type_variables: forall.unwrap_or_default(),
            is_public: false,
        });
    let data_decl = just(Token::Pub)
        .or_not()
        .then_ignore(just(Token::Data))
        .then(data_decl_infix.or(data_decl_record).or(data_decl_normal))
        .map(|(pub_or_not, d)| {
            Decl::Data(DataDecl {
                is_public: pub_or_not.is_some(),
                ..d
            })
        });
    let type_alias_decl = just(Token::Pub)
        .or_not()
        .then_ignore(just(Token::Type))
        .then(ident)
        .then_ignore(just(Token::Assign))
        .then(type_.clone())
        .map(|((pub_or_not, name), body)| {
            Decl::TypeAlias(TypeAliasDecl {
                name,
                body,
                is_public: pub_or_not.is_some(),
            })
        });
    let interface_decl = just(Token::Pub)
        .or_not()
        .then_ignore(just(Token::Interface))
        .then(ident)
        .then(indented(
            ident_or_op
                .then_ignore(just(Token::Colon))
                .then(type_)
                .repeated(),
        ))
        .map(|((pub_or_not, name), vs)| {
            Decl::Interface(InterfaceDecl {
                name,
                variables: vs
                    .into_iter()
                    .map(|(n, (t, forall))| (n, t, forall))
                    .collect(),
                is_public: pub_or_not.is_some(),
            })
        });
    let use_decl = just(Token::Pub)
        .or_not()
        .then_ignore(just(Token::Use))
        .then(ident_with_path)
        .map(|(pub_or_not, path)| Decl::Use {
            path,
            is_public: pub_or_not.is_some(),
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
            use_decl,
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
                let e = e.map(|c| format!("{c:?}"));
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
