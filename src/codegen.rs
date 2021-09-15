use crate::ast0::{DataDeclaration, Pattern};
use crate::ast1::{Ast, Declaration, Expr, FnArm};
use itertools::Itertools;
use once_cell::sync::Lazy;
use std::collections::{HashMap, HashSet};
use unic_ucd_category::GeneralCategory;

pub fn compile(ast: Ast) -> String {
    format!(
        "{}{}{}{}",
        "{
        let println = a => console.log(a);
        let $plus = a => b => a + b;
        let $minus = a => b => a - b;
        let $mod = a => b => a % b;",
        ast.data_declarations
            .into_iter()
            .map(data_declaration)
            .join(""),
        ast.declarations.into_iter().map(declaration).join(""),
        "main({name: '$unicode_28_29'});}",
    )
}

fn data_declaration(d: DataDeclaration) -> String {
    let name = convert_name(&d.name);
    format!(
        "let {} = {} ({{name: '{}', {}}});",
        name,
        (0..d.field_len).map(|i| format!("${} =>", i)).join(""),
        name,
        (0..d.field_len).map(|i| format!("{0}: ${0}", i)).join(", "),
    )
}

fn declaration(d: Declaration) -> String {
    format!(
        "let {} = {};",
        convert_name(&d.identifier),
        expr(&d.value, 0)
    )
}

static PRIMITIVES: Lazy<HashMap<&str, &str>> = Lazy::new(|| {
    [("+", "$plus"), ("-", "$minus"), ("%", "$mod")]
        .iter()
        .cloned()
        .collect()
});

fn expr(e: &Expr, name_count: u32) -> String {
    match e {
        Expr::Lambda(a) => format!(
            "{} {} 'unexpected'",
            (0..a[0].pattern.len())
                .map(|c| format!("${} => ", name_count + c as u32))
                .join(""),
            a.iter().map(|e| fn_arm(e, name_count)).join("")
        ),
        Expr::Number(a) => a.clone(),
        Expr::StrLiteral(a) => a.clone(),
        Expr::Identifier(a) => match PRIMITIVES.get(&a[..]) {
            Some(s) => s.to_string(),
            None => convert_name(a),
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
    let rst = _condition(
        pattern,
        &(0..pattern.len())
            .map(|i| format!("${}", i + name_count as usize))
            .collect_vec(),
    )
    .join(" && ");
    if rst.is_empty() {
        "true".to_string()
    } else {
        rst
    }
}

fn _condition(pattern: &[Pattern], names: &[String]) -> Vec<String> {
    pattern
        .iter()
        .zip(names)
        .flat_map(|(p, n)| match p {
            Pattern::Number(a) | Pattern::StrLiteral(a) => {
                vec![format!("{} === {}", a.clone(), n)]
            }
            Pattern::Constructor(a, ps) => {
                let mut v = vec![format!(
                    "'{}' === {}.name",
                    convert_name(a),
                    n
                )];
                v.append(&mut _condition(
                    ps,
                    &(0..ps.len())
                        .map(|i| format!("{}[{}]", n, i))
                        .collect_vec(),
                ));
                v
            }
            _ => Vec::new(),
        })
        .collect()
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

fn convert_name(name: &str) -> String {
    if is_valid_js_name(name) {
        name.to_string()
    } else {
        "$unicode".to_string()
            + &name
                .chars()
                .map(|c| format! {"_{:x}",c as u32})
                .join("")
    }
}

fn is_valid_js_name_head(c: char) -> bool {
    GeneralCategory::of(c).is_letter()
        || c == '$'
        || c == '_'
        || GeneralCategory::of(c) == GeneralCategory::LetterNumber
}

static UNUSABLE_NAMES: Lazy<HashSet<&str>> = Lazy::new(|| {
    [
        "do",
        "if",
        "in",
        "for",
        "let",
        "new",
        "try",
        "var",
        "case",
        "else",
        "enum",
        "eval",
        "false",
        "null",
        "undefined",
        "NaN",
        "this",
        "true",
        "void",
        "with",
        "break",
        "catch",
        "class",
        "const",
        "super",
        "throw",
        "while",
        "yield",
        "delete",
        "export",
        "import",
        "public",
        "return",
        "static",
        "switch",
        "typeof",
        "default",
        "extends",
        "finally",
        "package",
        "private",
        "continue",
        "debugger",
        "function",
        "arguments",
        "interface",
        "protected",
        "implements",
        "instanceof",
    ]
    .iter()
    .copied()
    .collect()
});

fn is_valid_js_name(name: &str) -> bool {
    let mut cs = name.chars();
    if let Some(h) = cs.next() {
        is_valid_js_name_head(h)
            && cs.all(|c| {
                is_valid_js_name_head(c)
                    || matches!(
                        GeneralCategory::of(c),
                        GeneralCategory::DecimalNumber
                            | GeneralCategory::NonspacingMark
                            | GeneralCategory::SpacingMark
                            | GeneralCategory::ConnectorPunctuation
                    )
            })
            && !UNUSABLE_NAMES.contains(name)
    } else {
        false
    }
}
