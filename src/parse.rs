use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::{
    prelude::*,
    text::{newline, Character},
    Error, Stream,
};
use std::iter;
use unic_ucd_category::GeneralCategory;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Token {
    Int(String),
    Str(String),
    Ident(String),
    CapitalHeadIdent(String),
    Op(String),
    Comma,
    Assign,
    Paren(char),
    OpenParenWithoutPad,
    Indent,
    Dedent,
    Case,
    Do,
    Forall,
    Infixl,
    Infixr,
    Data,
    Bar,
    BArrow,
    Colon,
}

trait RequiresIndet {
    fn requires_indent(&self) -> bool;
}

impl RequiresIndet for (Token, Span) {
    fn requires_indent(&self) -> bool {
        use Token::*;
        matches!(self, (Case | Do | Forall, _))
    }
}

pub type Span = std::ops::Range<usize>;

fn semantic_indentation<'a, C, T>(
    token: T,
    indent_tok: Token,
    dedent_tok: Token,
    src_len: usize,
) -> impl Parser<C, Vec<(Token, Span)>, Error = Simple<C>> + Clone + 'a
where
    C: Character + Eq + core::hash::Hash + 'a,
    T: Parser<C, (Token, Span), Error = Simple<C>> + Clone + 'a,
{
    let line_ws = filter(|c: &C| c.is_inline_whitespace());
    let line = token.repeated().then_ignore(line_ws.repeated());
    let lines = line_ws
        .repeated()
        .map_with_span(|token, span| (token, span))
        .then(line)
        .separated_by(newline())
        .padded();
    lines.map(move |lines| {
        let mut tokens: Vec<(Token, Span)> = Vec::new();
        let mut indent_level = 0;
        let mut requires_indent = false;
        let mut ignored_indents = vec![0];
        for ((indent, ident_span), mut line) in lines {
            if line.is_empty() {
                continue;
            }
            let indent_level_delta =
                indent.len() as i32 - indent_level as i32;
            indent_level = indent.len();
            match indent_level_delta.cmp(&0) {
                std::cmp::Ordering::Less => {
                    let mut dedent_level = -indent_level_delta;
                    while dedent_level > 0 {
                        let ignored_indents_h =
                            ignored_indents.pop().unwrap();
                        if ignored_indents_h >= dedent_level {
                            ignored_indents.push(
                                ignored_indents_h - dedent_level,
                            );
                            break;
                        } else {
                            dedent_level -= ignored_indents_h + 1;
                            tokens.push((
                                dedent_tok.clone(),
                                ident_span.clone(),
                            ));
                        }
                    }
                }
                std::cmp::Ordering::Equal => (),
                std::cmp::Ordering::Greater => {
                    if requires_indent {
                        tokens.push((
                            indent_tok.clone(),
                            ident_span.clone(),
                        ));
                        ignored_indents.push(indent_level_delta - 1);
                    } else {
                        *ignored_indents.last_mut().unwrap() +=
                            indent_level_delta;
                    }
                }
            }
            requires_indent = line
                .last()
                .map(|t| t.requires_indent())
                .unwrap_or(false);
            tokens.append(&mut line);
        }
        tokens.extend(
            (iter::repeat((
                dedent_tok.clone(),
                src_len - 1..src_len,
            )))
            .take(ignored_indents.len() - 1),
        );
        tokens
    })
}

fn lexer(
    src_len: usize,
) -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    let int = text::int(10).from_str().unwrapped().map(Token::Int);

    let ident = text::ident().map(|i: String| match i.as_str() {
        "case" => Token::Case,
        "do" => Token::Do,
        "forall" => Token::Forall,
        "infixl" => Token::Infixl,
        "infixr" => Token::Infixr,
        "data" => Token::Data,
        _ if i.chars().next().unwrap().is_uppercase() => {
            Token::CapitalHeadIdent(i)
        }
        _ => Token::Ident(i),
    });

    let str = filter(|&c| c != '"')
        .repeated()
        .delimited_by(just("\""), just("\""))
        .collect()
        .map(Token::Str);

    let unit = just('(')
        .then(just(')'))
        .map(|_| Token::CapitalHeadIdent("()".to_string()));

    let paren = just('(')
        .or(just(')'))
        .or(just('}'))
        .or(just('{'))
        .or(just('['))
        .or(just(']'))
        .map(Token::Paren);

    let op = filter::<_, _, Simple<char>>(|&c| {
        (GeneralCategory::of(c).is_punctuation()
            || GeneralCategory::of(c).is_symbol())
            && c != '"'
            && c != '('
            && c != ')'
    })
    .repeated()
    .at_least(1)
    .collect::<String>()
    .map(|op| match op.as_str() {
        "," => Token::Comma,
        "=>" => Token::BArrow,
        "|" => Token::Bar,
        "=" => Token::Assign,
        ":" => Token::Colon,
        _ => Token::Op(op),
    });

    let line_ws = filter(|c: &char| c.is_inline_whitespace());

    let tt = line_ws
        .repeated()
        .ignore_then(unit)
        .or(just('(').map(|_| Token::OpenParenWithoutPad))
        .or(line_ws
            .repeated()
            .ignore_then(int.or(str).or(paren).or(op).or(ident)))
        .map_with_span(|tok, span| (tok, span));

    semantic_indentation(tt, Token::Indent, Token::Dedent, src_len)
        .then_ignore(end())
}

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
                .or(ident_or_op.clone().map(ExprUnit::Ident))
                .or(lambda.map(|a| ExprUnit::Case(vec![a])))
                .or(variable_decl.map(ExprUnit::VariableDecl))
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

pub fn parse(src: &str) -> Ast {
    let len = src.chars().count();
    let ts = lexer(len).parse(src);
    let parser = parser();
    let r = parser.parse(Stream::from_iter(
        len..len + 1,
        ts.unwrap().into_iter(),
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
                report.finish().print(Source::from(&src)).unwrap();
            }
            panic!()
        }
    }
}
