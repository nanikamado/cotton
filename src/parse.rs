use crate::ast0::{
    Associativity, Ast, DataDecl, Decl, Expr, FnArm, Forall,
    InfixConstructorSequence, InfixTypeSequence, OpSequence,
    OpSequenceUnit, OperatorPrecedence, Pattern, Type, VariableDecl,
};
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_while1},
    character::complete::{self, anychar, digit1, one_of},
    combinator::{opt, recognize, verify},
    multi::{many0, many1},
    sequence::{delimited, pair, preceded, tuple},
    AsChar, IResult, Parser,
};
use unic_ucd_category::GeneralCategory;

fn separator0(input: &str) -> IResult<&str, Vec<char>> {
    many0(one_of("\r\n\t "))(input)
}

fn separator1(input: &str) -> IResult<&str, Vec<char>> {
    many1(one_of("\r\n\t "))(input)
}

pub fn parse(source: &str) -> IResult<&str, Ast> {
    let (input, decls) = many1(dec)(source)?;
    Ok((input, Ast { decls }))
}

fn dec(input: &str) -> IResult<&str, Decl> {
    pad(alt((
        decl.map(Decl::Variable),
        infix_constructor_decl.map(Decl::Data),
        data_decl.map(Decl::Data),
        operator_precedence_decl.map(Decl::Precedence),
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

fn decl(input: &str) -> IResult<&str, VariableDecl> {
    let (input, (identifier, _, data_type, _, _, value)) =
        tuple((
            identifier,
            separator0,
            opt(tuple((tag(":"), infix_type_sequence, opt(forall)))),
            separator0,
            tag("="),
            op_sequence,
        ))(input)?;
    Ok((
        input,
        VariableDecl {
            identifier,
            type_annotation: data_type.map(|(_, t, forall)| {
                (t, forall.unwrap_or_default())
            }),
            value,
        },
    ))
}

fn forall(input: &str) -> IResult<&str, Forall> {
    let (input, (_, id, ids, _, _, _)) = tuple((
        tag("forall"),
        identifier_separators,
        many0(preceded(tag(","), identifier_separators)),
        opt(tag(",")),
        separator0,
        tag("--"),
    ))(input)?;
    Ok((
        input,
        Forall {
            type_variable_names: [vec![id], ids].concat(),
        },
    ))
}

fn identifier_separators(input: &str) -> IResult<&str, String> {
    pad(identifier)(input)
}

fn data_decl(input: &str) -> IResult<&str, DataDecl> {
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
        DataDecl {
            name,
            field_len: fields.len(),
        },
    ))
}

fn infix_constructor_decl(input: &str) -> IResult<&str, DataDecl> {
    let (input, (_, _l, name, _r)) = tuple((
        tag("data"),
        identifier_separators,
        op,
        identifier_separators,
    ))(input)?;
    Ok((input, DataDecl { name, field_len: 2 }))
}

fn type_expr(input: &str) -> IResult<&str, Type> {
    alt((
        identifier.map(Type::Identifier),
        tag("()").map(|_| Type::Identifier("()".to_string())),
        delimited(tag("("), infix_type_sequence, tag(")"))
            .map(Type::Paren),
    ))(input)
}

pub fn infix_type_sequence(
    input: &str,
) -> IResult<&str, InfixTypeSequence> {
    let (input, (_, e, eo, _)) = tuple((
        separator0,
        type_expr,
        many0(alt((
            type_call.map(|es| {
                es.into_iter().map(OpSequenceUnit::Apply).collect()
            }),
            tuple((pad(type_op), type_expr))
                .map(|(s, e)| vec![s, OpSequenceUnit::Operand(e)]),
        ))),
        separator0,
    ))(input)?;
    let eo = std::iter::once(OpSequenceUnit::Operand(e))
        .chain(eo.into_iter().flatten())
        .collect();
    Ok((input, eo))
}

fn type_call(input: &str) -> IResult<&str, Vec<Type>> {
    let (input, (_, a0, a1, _, _)) = tuple((
        tag("["),
        infix_type_sequence,
        many0(preceded(tag(","), infix_type_sequence)),
        opt(tag(",")),
        tag("]"),
    ))(input)?;
    let mut a0 = vec![Type::Paren(a0)];
    let mut a1 = a1.into_iter().map(Type::Paren).collect();
    a0.append(&mut a1);
    Ok((input, a0))
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
    alt((
        str_literal.map(|s| Expr::StrLiteral(s.to_string())),
        num_literal.map(|s| Expr::Number(s.to_string())),
        unit,
        lambda,
        decl.map(|d| Expr::Decl(Box::new(d))),
        identifier.map(Expr::Identifier),
        paren,
    ))(input)
}

fn paren(input: &str) -> IResult<&str, Expr> {
    let (input, s) =
        delimited(tag("("), op_sequence, tag(")"))(input)?;
    Ok((input, Expr::Paren(s)))
}

fn lambda(input: &str) -> IResult<&str, Expr> {
    let (input, (_, _, arms, _)) =
        tuple((tag("fn"), separator0, many1(fn_arm), tag("--")))(
            input,
        )?;
    Ok((input, Expr::Lambda(arms)))
}

fn fn_arm(input: &str) -> IResult<&str, FnArm> {
    let (
        input,
        (_, pattern0, type0, pattern1_type1, _, _, arguments),
    ) = tuple((
        tag("|"),
        infix_constructor_sequence,
        opt(preceded(tag(":"), infix_type_sequence)),
        many0(preceded(
            tag(","),
            tuple((
                infix_constructor_sequence,
                opt(preceded(tag(":"), infix_type_sequence)),
            )),
        )),
        opt(tag(",")),
        tag("=>"),
        many1(op_sequence),
    ))(input)?;
    let (mut pattern1, mut type1) =
        pattern1_type1.into_iter().unzip();
    Ok((
        input,
        FnArm {
            pattern: {
                let mut p = vec![pattern0];
                p.append(&mut pattern1);
                p
            },
            pattern_type: {
                let mut p = vec![type0];
                p.append(&mut type1);
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
        identifier.map(Pattern::Binder),
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
    let mut a0 = vec![Expr::Paren(a0)];
    let mut a1 = a1.into_iter().map(Expr::Paren).collect();
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
        many0(tuple((pad(op), pattern)).map(|(s, e)| {
            vec![
                OpSequenceUnit::Operator(s),
                OpSequenceUnit::Operand(e),
            ]
        })),
        separator0,
    ))(input)?;
    let eo = std::iter::once(OpSequenceUnit::Operand(e))
        .chain(eo.into_iter().flatten())
        .collect();
    Ok((input, eo))
}

fn op_sequence(input: &str) -> IResult<&str, OpSequence> {
    let (input, (_, e, eo, _)) = tuple((
        separator0,
        expr,
        many0(alt((
            fn_call.map(|es| {
                es.into_iter().map(OpSequenceUnit::Apply).collect()
            }),
            tuple((pad(op), expr)).map(|(s, e)| {
                vec![
                    OpSequenceUnit::Operator(s),
                    OpSequenceUnit::Operand(e),
                ]
            }),
        ))),
        separator0,
    ))(input)?;
    let eo = std::iter::once(OpSequenceUnit::Operand(e))
        .chain(eo.into_iter().flatten())
        .collect();
    Ok((input, eo))
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
        |s: &str| !["=", "=>", "|", "--", ",", ":"].contains(&s),
    )(input)
    .map(|(i, s)| (i, s.to_string()))
}

fn type_op(input: &str) -> IResult<&str, OpSequenceUnit<Type>> {
    alt((op, tag("|").map(|_| "|".to_string())))
        .map(OpSequenceUnit::Operator)
        .parse(input)
}

fn operator_precedence_decl(
    input: &str,
) -> IResult<&str, OperatorPrecedence> {
    alt((
        tuple((
            tag("infixl"),
            separator1,
            complete::i64,
            separator1,
            op,
        ))
        .map(|(_, _, precedence, _, name)| {
            OperatorPrecedence {
                name,
                associativity: Associativity::Left,
                precedence: precedence as i32,
            }
        }),
        tuple((
            tag("infixr"),
            separator1,
            complete::i64,
            separator1,
            op,
        ))
        .map(|(_, _, precedence, _, name)| {
            OperatorPrecedence {
                name,
                associativity: Associativity::Right,
                precedence: precedence as i32,
            }
        }),
    ))
    .parse(input)
}
