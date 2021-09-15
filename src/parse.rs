use crate::ast::{
    DataDeclaration, Dec, Declaration, Expr, FnArm,
    InfixConstructorSequence, OpSequence, Pattern, AST,
};
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_while1},
    character::complete::{anychar, digit1, one_of, space0},
    combinator::{opt, recognize, verify},
    multi::{many0, many1},
    sequence::{delimited, pair, preceded, tuple},
    AsChar, IResult, Parser,
};
use unic_ucd_category::GeneralCategory;

fn separator0(input: &str) -> IResult<&str, Vec<char>> {
    many0(one_of("\r\n\t "))(input)
}

pub fn parse(source: &str) -> IResult<&str, AST> {
    let (input, declarations) = many1(dec)(source)?;
    Ok((input, AST { declarations }))
}

fn dec(input: &str) -> IResult<&str, Dec> {
    pad(alt((
        declaration.map(Dec::Variable),
        infix_constructor_declaration.map(Dec::Data),
        data_declaration.map(Dec::Data),
    )))(input)
}

fn pad<'a, O, F>(
    f: F,
) -> impl FnMut(&'a str) -> IResult<&'a str, O, nom::error::Error<&str>>
where
    F: FnMut(&'a str) -> IResult<&'a str, O, nom::error::Error<&str>>,
{
    delimited(separator0, f, separator0)
}

fn declaration(input: &str) -> IResult<&str, Declaration> {
    let (input, (identifier, _, _, _, _, value)) = tuple((
        identifier,
        space0,
        tag(":"),
        type_expr,
        tag("="),
        op_sequence,
    ))(input)?;
    Ok((
        input,
        Declaration {
            identifier,
            datatype: (),
            value,
        },
    ))
}

fn identifier_separators(input: &str) -> IResult<&str, String> {
    pad(identifier)(input)
}

fn data_declaration(input: &str) -> IResult<&str, DataDeclaration> {
    let (input, (_, _, name, fields)) = tuple((
        tag("data"),
        separator0,
        capital_head_identifier,
        opt(tuple((
            tag("("),
            identifier_separators,
            many0(preceded(tag(","), identifier_separators)),
            opt(tag(",")),
            tag(")"),
        ))),
    ))(input)?;
    let fields = if let Some((_, field0, mut field1, _, _)) = fields {
        let mut field0 = vec![field0];
        field0.append(&mut field1);
        field0
    } else {
        Vec::new()
    };
    Ok((
        input,
        DataDeclaration {
            name,
            field_len: fields.len(),
        },
    ))
}

fn infix_constructor_declaration(
    input: &str,
) -> IResult<&str, DataDeclaration> {
    let (input, (_, _l, name, _r)) = tuple((
        tag("data"),
        identifier_separators,
        op,
        identifier_separators,
    ))(input)?;
    Ok((input, DataDeclaration { name, field_len: 2 }))
}

fn type_expr(input: &str) -> IResult<&str, OpSequence> {
    op_sequence(input)
}

fn identifier(input: &str) -> IResult<&str, String> {
    let head = verify(anychar, |c| {
        is_identifier_char(*c) && !c.is_dec_digit() || *c == '_'
    });
    let tail = verify(anychar, |c| is_identifier_char(*c));
    let op = delimited(tag("("), op, tag(")"));
    alt((
        recognize(pair(head, many0(tail)))
            .map(|s: &str| s.to_string()),
        op,
    ))(input)
}

fn capital_head_identifier(input: &str) -> IResult<&str, String> {
    let head = verify(anychar, |c| {
        c.is_uppercase()
            && is_identifier_char(*c)
            && !c.is_dec_digit()
    });
    let tail = verify(anychar, |c| is_identifier_char(*c));
    let op = delimited(tag("("), op, tag(")"));
    alt((
        recognize(pair(head, many0(tail)))
            .map(|s: &str| s.to_string()),
        op,
    ))(input)
}

fn is_identifier_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn expr(input: &str) -> IResult<&str, Expr> {
    pad(alt((
        str_literal.map(|s| Expr::StrLiteral(s.to_string())),
        num_literal.map(|s| Expr::Number(s.to_string())),
        unit,
        lambda,
        declaration.map(|d| Expr::Declaration(Box::new(d))),
        identifier.map(|s| Expr::Identifier(s)),
        paren,
    )))(input)
}

fn paren(input: &str) -> IResult<&str, Expr> {
    let (input, s) =
        delimited(tag("("), op_sequence, tag(")"))(input)?;
    Ok((input, Expr::Parenthesized(s)))
}

fn lambda(input: &str) -> IResult<&str, Expr> {
    let (input, (_, _, arms, _)) =
        tuple((tag("fn"), separator0, many1(fn_arm), tag("--")))(
            input,
        )?;
    Ok((input, Expr::Lambda(arms)))
}

fn fn_arm(input: &str) -> IResult<&str, FnArm> {
    let (input, (_, pattern0, mut pattern1, _, _, arguments)) =
        tuple((
            tag("|"),
            infix_constructor_sequence,
            many0(preceded(tag(","), infix_constructor_sequence)),
            opt(tag(",")),
            tag("=>"),
            many1(op_sequence),
        ))(input)?;
    Ok((
        input,
        FnArm {
            pattern: {
                let mut p = vec![pattern0];
                p.append(&mut pattern1);
                p
            },
            exprs: arguments,
        },
    ))
}

fn pattern(input: &str) -> IResult<&str, Pattern> {
    pad(alt((
        str_literal.map(|s| Pattern::StrLiteral(s.to_string())),
        num_literal.map(|s| Pattern::Number(s.to_string())),
        tag("()").map(|_| {
            Pattern::Constructor("()".to_string(), Vec::new())
        }),
        tag("_").map(|_| Pattern::Underscore),
        constructor_pattern,
        identifier.map(|s| Pattern::Binder(s)),
    )))(input)
}

fn constructor_pattern(input: &str) -> IResult<&str, Pattern> {
    let (input, (name, fields)) = tuple((
        capital_head_identifier,
        opt(tuple((
            tag("("),
            pattern,
            many0(preceded(tag(","), pattern)),
            opt(tag(",")),
            tag(")"),
        ))),
    ))(input)?;
    let fields = if let Some((_, field0, mut field1, _, _)) = fields {
        let mut field0 = vec![field0];
        field0.append(&mut field1);
        field0
    } else {
        Vec::new()
    };
    Ok((input, Pattern::Constructor(name, fields)))
}

fn str_literal(input: &str) -> IResult<&str, &str> {
    let (input, s) =
        recognize(tuple((tag("\""), is_not("\""), tag("\""))))(
            input,
        )?;
    Ok((input, s))
}

fn num_literal(input: &str) -> IResult<&str, &str> {
    digit1(input).map(|(i, s)| (i, s))
}

fn fn_call(input: &str) -> IResult<&str, Vec<Expr>> {
    let (input, (_, a0, a1, _, _)) = tuple((
        tag("("),
        op_sequence,
        many0(preceded(tag(","), op_sequence)),
        opt(tag(",")),
        tag(")"),
    ))(input)?;
    let mut a0 = vec![Expr::Parenthesized(a0)];
    let mut a1 =
        a1.into_iter().map(|s| Expr::Parenthesized(s)).collect();
    a0.append(&mut a1);
    Ok((input, a0))
}

fn unit(input: &str) -> IResult<&str, Expr> {
    let (input, _) = tag("()")(input)?;
    Ok((input, Expr::Unit))
}

fn infix_constructor_sequence(
    input: &str,
) -> IResult<&str, InfixConstructorSequence> {
    let (input, (_, e, eo, _)) = tuple((
        separator0,
        pattern,
        many0(tuple((pad(op), pattern))),
        separator0,
    ))(input)?;
    let (os, mut es): (Vec<_>, Vec<_>) = eo.into_iter().unzip();
    Ok((
        input,
        InfixConstructorSequence {
            operators: os,
            operands: {
                let mut e = vec![e];
                e.append(&mut es);
                e
            },
        },
    ))
}

fn op_sequence(input: &str) -> IResult<&str, OpSequence> {
    let (input, (_, e, eo, _)) = tuple((
        separator0,
        expr,
        many0(alt((
            fn_call.map(|es| {
                es.into_iter()
                    .map(|e| ("fn_call".to_string(), e))
                    .collect()
            }),
            tuple((pad(op), expr)).map(|(s, e)| vec![(s, e)]),
        ))),
        separator0,
    ))(input)?;
    let (os, mut es): (Vec<_>, Vec<_>) =
        eo.concat().into_iter().unzip();
    Ok((
        input,
        OpSequence {
            operators: os,
            operands: {
                let mut e = vec![e];
                e.append(&mut es);
                e
            },
        },
    ))
}

fn op(input: &str) -> IResult<&str, String> {
    verify(
        take_while1(|c| {
            (GeneralCategory::of(c).is_punctuation()
                || GeneralCategory::of(c).is_symbol())
                && c != '"'
                && c != '('
                && c != ')'
        }),
        |s: &str| {
            s != "=" && s != "=>" && s != "|" && s != "--" && s != ","
        },
    )(input)
    .map(|(i, s)| (i, s.to_string()))
}
