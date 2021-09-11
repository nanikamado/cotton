use crate::ast::{Declaration, Expr, FnArm, OpExpr, Operand, AST};
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_while1},
    character::complete::{anychar, digit1, one_of, space0},
    combinator::verify,
    multi::{many0, many1, many_m_n},
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

fn type_expr(input: &str) -> IResult<&str, OpExpr> {
    op_sequence(input)
}

fn identifier(input: &str) -> IResult<&str, String> {
    let head = verify(anychar, |c| {
        is_identifier_char(*c) && !c.is_dec_digit()
    });
    let tail = verify(anychar, |c| is_identifier_char(*c));
    let (input, (h, t)) = pair(head, many0(tail))(input)?;
    Ok((input, h.to_string() + &t.into_iter().collect::<String>()))
}

fn is_identifier_char(c: char) -> bool {
    c.is_alphanumeric()
}

fn expr(input: &str) -> IResult<&str, Expr> {
    delimited(
        separator0,
        alt((
            str_literal,
            num_literal,
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
    let (input, (_, pattern, _, arguments)) =
        tuple((tag("|"), expr, tag("=>"), many1(op_sequence)))(
            input,
        )?;
    Ok((
        input,
        FnArm {
            pattern: format!("{:?}", pattern),
            exprs: arguments,
        },
    ))
}

fn str_literal(input: &str) -> IResult<&str, Expr> {
    let (input, s) =
        delimited(tag("\""), is_not("\""), tag("\""))(input)?;
    Ok((input, Expr::StrLiteral(s.to_string())))
}

fn num_literal(input: &str) -> IResult<&str, Expr> {
    digit1(input).map(|(i, s)| (i, Expr::Number(s.to_string())))
}

fn fn_call(input: &str) -> IResult<&str, Operand> {
    let (input, (_, mut a0, mut a1, _, _)) = tuple((
        tag("("),
        many_m_n(0, 1, op_sequence),
        many0(preceded(tag(","), op_sequence)),
        many_m_n(0, 1, tag(",")),
        tag(")"),
    ))(input)?;
    Ok((
        input,
        Operand::FnCallArguments({
            a0.append(&mut a1);
            a0
        }),
    ))
}

fn unit(input: &str) -> IResult<&str, Expr> {
    let (input, _) = tag("()")(input)?;
    Ok((input, Expr::Unit))
}

fn op_sequence(input: &str) -> IResult<&str, OpExpr> {
    let (input, (_, e, eo, _)) = tuple((
        separator0,
        expr,
        many0(alt((
            tuple((delimited(separator0, op, separator0), expr))
                .map(|(s, e)| (s, Operand::Expr(e))),
            fn_call.map(|o| ("fn_call".to_string(), o)),
        ))),
        separator0,
    ))(input)?;
    let (os, mut es): (Vec<_>, Vec<_>) = eo.into_iter().unzip();
    Ok((
        input,
        OpExpr {
            operators: os,
            operands: {
                let mut e = vec![Operand::Expr(e)];
                e.append(&mut es);
                e
            },
        },
    ))
}

fn op(input: &str) -> IResult<&str, String> {
    verify(
        take_while1(|c| {
            GeneralCategory::of(c).is_punctuation()
                || GeneralCategory::of(c).is_symbol()
        }),
        |s: &str| {
            s != "="
                && s != "=>"
                && s != "|"
                && s != "--"
                && !s.contains("\"")
                && !s.contains("(")
                && !s.contains(")")
        },
    )(input)
    .map(|(i, s)| (i, s.to_string()))
}

#[test]
fn fib_op_sequence() {
    assert_eq!(
        op_sequence("fib(n - 1) + fib(n - 2)"),
        Ok((
            "",
            OpExpr {
                operators: ["fn_call", "+", "fn_call"]
                    .iter()
                    .map(|s| s.to_string())
                    .collect(),
                operands: vec![
                    Operand::Expr(Expr::Identifier(
                        "fib".to_string()
                    )),
                    Operand::FnCallArguments(vec![OpExpr {
                        operators: vec!["-".to_string()],
                        operands: vec![
                            Operand::Expr(Expr::Identifier(
                                "n".to_string()
                            )),
                            Operand::Expr(Expr::Number(
                                "1".to_string()
                            ))
                        ]
                    }]),
                    Operand::Expr(Expr::Identifier(
                        "fib".to_string()
                    )),
                    Operand::FnCallArguments(vec![OpExpr {
                        operators: vec!["-".to_string()],
                        operands: vec![
                            Operand::Expr(Expr::Identifier(
                                "n".to_string()
                            )),
                            Operand::Expr(Expr::Number(
                                "2".to_string()
                            ))
                        ]
                    }])
                ],
            }
        ))
    )
}

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
