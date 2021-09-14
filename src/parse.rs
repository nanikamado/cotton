use crate::ast::{
    Declaration, Expr, FnArm, OpSequence, Pattern, AST,
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
    let (input, declarations) = many1(declaration)(source)?;
    Ok((input, AST { declarations }))
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

fn is_identifier_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn expr(input: &str) -> IResult<&str, Expr> {
    delimited(
        separator0,
        alt((
            str_literal.map(|s| Expr::StrLiteral(s.to_string())),
            num_literal.map(|s| Expr::Number(s.to_string())),
            unit,
            lambda,
            declaration.map(|d| Expr::Declaration(Box::new(d))),
            identifier.map(|s| Expr::Identifier(s)),
        )),
        separator0,
    )(input)
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
            pattern,
            many0(preceded(tag(","), pattern)),
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
    delimited(
        separator0,
        alt((
            str_literal.map(|s| Pattern::StrLiteral(s.to_string())),
            num_literal.map(|s| Pattern::Number(s.to_string())),
            tag("()").map(|_| Pattern::Constructor("()".to_string())),
            tag("_").map(|_| Pattern::Underscore),
            identifier.map(|s| Pattern::Binder(s)),
        )),
        separator0,
    )(input)
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
    let mut a0 = vec![Expr::Parenthesized(Box::new(a0))];
    let mut a1 = a1
        .into_iter()
        .map(|s| Expr::Parenthesized(Box::new(s)))
        .collect();
    a0.append(&mut a1);
    Ok((input, a0))
}

fn unit(input: &str) -> IResult<&str, Expr> {
    let (input, _) = tag("()")(input)?;
    Ok((input, Expr::Unit))
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
            tuple((delimited(separator0, op, separator0), expr))
                .map(|(s, e)| vec![(s, e)]),
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

// #[test]
// fn fib_op_sequence() {
//     assert_eq!(
//         op_sequence("fib(n - 1) + fib(n - 2)"),
//         Ok((
//             "",
//             OpSequence {
//                 operators: ["fn_call", "+", "fn_call"]
//                     .iter()
//                     .map(|s| s.to_string())
//                     .collect(),
//                 operands: vec![
//                     Operand::Expr(Expr::Identifier(
//                         "fib".to_string()
//                     )),
//                     Operand::FnCallArguments(vec![OpSequence {
//                         operators: vec!["-".to_string()],
//                         operands: vec![
//                             Operand::Expr(Expr::Identifier(
//                                 "n".to_string()
//                             )),
//                             Operand::Expr(Expr::Number(
//                                 "1".to_string()
//                             ))
//                         ]
//                     }]),
//                     Operand::Expr(Expr::Identifier(
//                         "fib".to_string()
//                     )),
//                     Operand::FnCallArguments(vec![OpSequence {
//                         operators: vec!["-".to_string()],
//                         operands: vec![
//                             Operand::Expr(Expr::Identifier(
//                                 "n".to_string()
//                             )),
//                             Operand::Expr(Expr::Number(
//                                 "2".to_string()
//                             ))
//                         ]
//                     }])
//                 ],
//             }
//         ))
//     )
// }

// #[test]
// fn helloworld_parse() {
//     assert_eq!(
//         parse(
//             r#"main : () -> ()
//     = fn
//     | () =>
//         println("Hello, world.")
//     --"#
//         ),
//         Ok((
//             "",
//             AST {
//                 declarations: vec![Declaration {
//                     identifier: "main".to_string(),
//                     datatype: (),
//                     value: Expr::Function(vec![FnArm {
//                         pattern: "()".to_string(),
//                         exprs: vec![Expr::FnCall {
//                             function: Box::new(
//                                 Expr::Identifier(
//                                     "println".to_string()
//                                 )
//                                 .into()
//                             ),
//                             arguments: vec![Expr::StrLiteral(
//                                 "Hello, world.".to_string()
//                             )
//                             .into(),]
//                         }]
//                     }])
//                     .into()
//                 }]
//             }
//         ))
//     )
// }
