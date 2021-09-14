use std::collections::HashMap;

use crate::ast::Pattern;
use crate::ast2::{Declaration, Expr, FnArm, AST};
use itertools::Itertools;
use once_cell::sync::Lazy;

pub fn compile(ast: AST) -> String {
    format!(
        "{}{}{}",
        "{
        let println = a => console.log(a);
        let $plus = a => b => a + b;
        let $minus = a => b => a - b;
        let $mod = a => b => a % b;",
        ast.declarations.into_iter().map(declaration).join(""),
        "main('()');}",
    )
}

fn declaration(d: Declaration) -> String {
    format!("let {} = {};", d.identifier, expr(&d.value, 0))
}

static PRIMITIVES: Lazy<HashMap<&str, &str>> = Lazy::new(|| {
    [("+", "$plus"), ("-", "$minus"), ("%", "$mod")].iter().cloned().collect()
});

fn expr(e: &Expr, name_count: u32) -> String {
    match e {
        Expr::Lambda(a) => format!(
            "{} {{ return {} 'unexpected';}}",
            (0..a[0].pattern.len())
                .map(|c| format!("${} => ", name_count + c as u32))
                .join(""),
            a.iter().map(|e| fn_arm(e, name_count)).join("")
        ),
        Expr::Number(a) => a.clone(),
        Expr::StrLiteral(a) => a.clone(),
        Expr::Identifier(a) => match PRIMITIVES.get(&a[..]) {
            Some(s) => s.to_string(),
            None => a.clone(),
        },
        Expr::Declaration(a) => declaration(*a.clone()),
        Expr::Call(f, a) => format!(
            "({})({})",
            expr(&*f, name_count),
            expr(&*a, name_count)
        ),
        Expr::Unit => "null".to_string(),
    }
}

fn multi_expr(es: &[Expr], name_count: u32) -> String {
    format!("({})", es.iter().map(|e| expr(e, name_count)).join(","))
}

fn fn_arm(e: &FnArm, name_count: u32) -> String {
    let cond = condition(&e.pattern, name_count);
    let binds = bindings(&e.pattern, name_count);
    if binds.is_empty() {
        format!(
            "{} ? {} :",
            cond,
            multi_expr(&e.exprs, name_count + e.pattern.len() as u32),
        )
    } else {
        format!(
            "{} ? ({} {}){} :",
            cond,
            binds.iter().map(|(s, _)| format!("{} =>", s)).join(""),
            multi_expr(&e.exprs, name_count + e.pattern.len() as u32),
            binds.iter().map(|(_, n)| format!("(${})", n)).join(""),
        )
    }
}

fn condition(pattern: &[Pattern], name_count: u32) -> String {
    pattern
        .iter()
        .zip(name_count..)
        .filter_map(|(p, n)| match p {
            Pattern::Number(a) | Pattern::StrLiteral(a) => {
                Some((a.clone(), n))
            }
            Pattern::Constructor(a) => Some((format!("'{}'", a), n)),
            _ => None,
        })
        .map(|(a, n)| format!("{} === ${} &&", a, n))
        .join("")
        + &"true"
}

fn bindings(
    pattern: &[Pattern],
    name_count: u32,
) -> Vec<(&str, u32)> {
    pattern
        .iter()
        .zip(name_count..)
        .filter_map(|(p, n)| match p {
            Pattern::Binder(a) => Some((&a[..], n)),
            _ => None,
        })
        .collect()
}
