use std::collections::HashMap;

use crate::ast::Pattern;
use crate::ast2::{Declaration, Expr, FnArm, AST};
use itertools::Itertools;
use once_cell::sync::Lazy;

pub fn compile(ast: AST) -> String {
    format!(
        "{}{}{}",
        "{
        let println = a => {
            console.log(a);
        };
        let $plus = a => b => {
            return a + b;
        };
        let $minus = a => b => {
            return a - b;
        };",
        ast.declarations.into_iter().map(declaration).join(""),
        "main('()');}",
    )
}

fn declaration(d: Declaration) -> String {
    format!("let {} = {};", d.identifier, expr(&d.value, 0))
}

static PRIMITIVES: Lazy<HashMap<&str, &str>> = Lazy::new(|| {
    [("+", "$plus"), ("-", "$minus")].iter().cloned().collect()
});

fn expr(e: &Expr, name_count: u32) -> String {
    match e {
        Expr::Lambda(a) => format!(
            "${} => {{ return {} 'unexpected';}}",
            name_count,
            a.iter().map(|e| fn_arm(e, name_count + 1)).join("")
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
    match &e.pattern {
        Pattern::Binder(a) => {
            format!(
                "true ? ({} => {})(${}) :",
                a,
                multi_expr(&e.exprs, name_count),
                name_count - 1,
            )
        }
        Pattern::Underscore => multi_expr(&e.exprs, name_count),
        Pattern::Number(a) | Pattern::StrLiteral(a) => format!(
            "(${} === {}) ? {} :",
            name_count - 1,
            a,
            multi_expr(&e.exprs, name_count)
        ),
        Pattern::Constructor(a) => format!(
            "(${} === '{}') ? {} :",
            name_count - 1,
            a,
            multi_expr(&e.exprs, name_count)
        ),
    }
}
