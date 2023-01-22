use crate::token_id::TokenId;
use chumsky::prelude::*;
use chumsky::text::{newline, Character};
use std::iter;
use unic_ucd_category::GeneralCategory;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Token {
    Int(String),
    Str(String),
    Ident(String, TokenId),
    Op(String, TokenId),
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
    ColonColon,
    Type,
    Interface,
    Where,
    Mod,
    Question,
    Pub,
    Use,
}

trait RequiresIndent {
    fn requires_indent(&self) -> bool;
}

impl RequiresIndent for (Token, Span) {
    fn requires_indent(&self) -> bool {
        use Token::*;
        matches!(self, (Do | Forall | Where, _))
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
        let mut last_span = 0..0;
        for ((indent, ident_span), mut line) in lines {
            if line.is_empty() {
                continue;
            }
            let l = if line.len() >= 2 && line[0].0 == Token::Bar {
                line[1].1.start - ident_span.start
            } else {
                indent.len()
            };
            let indent_level_delta = l as i32 - indent_level as i32;
            indent_level = l;
            match indent_level_delta.cmp(&0) {
                std::cmp::Ordering::Less => {
                    let mut dedent_level = -indent_level_delta;
                    while dedent_level > 0 {
                        let ignored_indents_h = ignored_indents.pop().unwrap();
                        if ignored_indents_h >= dedent_level {
                            ignored_indents
                                .push(ignored_indents_h - dedent_level);
                            break;
                        } else {
                            dedent_level -= ignored_indents_h + 1;
                            tokens
                                .push((dedent_tok.clone(), last_span.clone()));
                        }
                    }
                }
                std::cmp::Ordering::Equal => (),
                std::cmp::Ordering::Greater => {
                    let requirers_ident_case = line[0].0 == Token::Bar;
                    if requires_indent
                        && requirers_ident_case
                        && indent_level_delta >= 2
                    {
                        tokens.push((indent_tok.clone(), ident_span.clone()));
                        tokens.push((indent_tok.clone(), ident_span.clone()));
                        ignored_indents.push(indent_level_delta);
                        ignored_indents.push(indent_level_delta - 2);
                    } else if requires_indent || requirers_ident_case {
                        tokens.push((indent_tok.clone(), ident_span.clone()));
                        ignored_indents.push(indent_level_delta - 1);
                    } else {
                        *ignored_indents.last_mut().unwrap() +=
                            indent_level_delta;
                    }
                }
            }
            requires_indent =
                line.last().map(|t| t.requires_indent()).unwrap_or(false);
            if line[0].0 == Token::OpenParenWithoutPad {
                line[0].0 = Token::Paren('(');
            }
            last_span = line[0].1.clone();
            tokens.append(&mut line);
        }
        tokens.extend(
            (iter::repeat((dedent_tok.clone(), src_len - 1..src_len)))
                .take(ignored_indents.len() - 1),
        );
        tokens
    })
}

fn lexer(
    src_len: usize,
) -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    let int = text::int(10).from_str().unwrapped().map(Token::Int);
    let ident =
        filter(|c: &char| c.to_char().is_ascii_alphabetic() || *c == '_')
            .map(Some)
            .chain::<char, Vec<_>, _>(
                filter(|c: &char| {
                    c.to_char().is_ascii_alphanumeric()
                        || *c == '_'
                        || *c == '\''
                })
                .repeated(),
            )
            .collect();
    let ident = ident.map(|i: String| match i.as_str() {
        "case" => Token::Case,
        "do" => Token::Do,
        "forall" => Token::Forall,
        "infixl" => Token::Infixl,
        "infixr" => Token::Infixr,
        "data" => Token::Data,
        "type" => Token::Type,
        "interface" => Token::Interface,
        "where" => Token::Where,
        "mod" => Token::Mod,
        "pub" => Token::Pub,
        "use" => Token::Use,
        _ => Token::Ident(i, TokenId::new()),
    });

    #[allow(clippy::is_digit_ascii_radix)]
    // This `escape` copied from https://github.com/zesterer/chumsky/blob/6107b2f98a22e8d22a6ee64b0ab4f727166d6769/examples/json.rs#L39
    // MIT License: https://github.com/zesterer/chumsky/blob/6107b2f98a22e8d22a6ee64b0ab4f727166d6769/LICENSE
    let escape = just('\\').ignore_then(
        just('\\')
            .or(just('/'))
            .or(just('"'))
            .or(just('b').to('\x08'))
            .or(just('f').to('\x0C'))
            .or(just('n').to('\n'))
            .or(just('r').to('\r'))
            .or(just('t').to('\t'))
            .or(just('u').ignore_then(
                filter(|c: &char| c.is_digit(16))
                    .repeated()
                    .exactly(4)
                    .collect::<String>()
                    .validate(|digits, span, emit| {
                        char::from_u32(
                            u32::from_str_radix(&digits, 16).unwrap(),
                        )
                        .unwrap_or_else(|| {
                            emit(Simple::custom(
                                span,
                                "invalid unicode character",
                            ));
                            '\u{FFFD}' // unicode replacement character
                        })
                    }),
            )),
    );
    let str = filter(|c| *c != '\\' && *c != '"')
        .or(escape)
        .repeated()
        .delimited_by(just("\""), just("\""))
        .collect()
        .map(Token::Str);

    let unit = just('(')
        .then(just(')'))
        .map(|_| Token::Ident("()".to_string(), TokenId::new()));

    let paren = choice((
        just('('),
        just(')'),
        just('}'),
        just('{'),
        just('['),
        just(']'),
    ))
    .map(Token::Paren);

    let op = just(",")
        .map(|_| Token::Comma)
        .or(just("?").map(|_| Token::Question))
        .or(filter::<_, _, Simple<char>>(|&c| {
            (GeneralCategory::of(c).is_punctuation()
                || GeneralCategory::of(c).is_symbol())
                && c != '"'
                && c != '('
                && c != ')'
                && c != '_'
        })
        .repeated()
        .at_least(1)
        .collect::<String>()
        .map(|op| match op.as_str() {
            "=>" => Token::BArrow,
            "|" => Token::Bar,
            "=" => Token::Assign,
            "::" => Token::ColonColon,
            ":" => Token::Colon,
            _ => Token::Op(op, TokenId::new()),
        }));
    let comment = just("//").then(take_until(just('\n'))).padded();

    let line_ws = filter(|c: &char| c.is_inline_whitespace());

    let tt = line_ws
        .repeated()
        .ignore_then(unit.map_with_span(|tok, span| (tok, span)))
        .or(just('(')
            .map(|_| Token::OpenParenWithoutPad)
            .map_with_span(|tok, span| (tok, span)))
        .or(line_ws.repeated().ignore_then(
            choice((int, str, paren, op, ident))
                .map_with_span(|tok, span| (tok, span))
                .padded_by(comment.repeated()),
        ));

    semantic_indentation(tt, Token::Indent, Token::Dedent, src_len)
        .then_ignore(end())
}

pub fn lex(src: &str) -> (Vec<(Token, Span)>, usize) {
    let len = src.chars().count();
    let ts = lexer(len).parse(src).unwrap();
    (ts, len)
}
