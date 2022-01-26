use crate::ast1::{
    decl_id::DeclId, Ast, DataDeclaration, Declaration, Expr, FnArm,
    Pattern,
};
use crate::type_check::intrinsics::INTRINSIC_VARIABLES;
use itertools::Itertools;
use once_cell::sync::Lazy;
use std::collections::{HashMap, HashSet};
use stripmargin::StripMargin;
use unic_ucd_category::GeneralCategory;

pub fn codegen(ast: Ast) -> String {
    format!(
        "{}{}{}{}${}$main($unicode_28_29);}}",
        r#"{
        |let $$unexpected = () => {throw new Error("unexpected")};
        |let $$bool = a => a ? $$True : $$False;
        |let $$True = {name: 'True'};
        |let $$False = {name: 'False'};
        |let $unicode_28_29 = {name: 'unicode_28_29'};
        |"#
        .strip_margin(),
        PRIMITIVES_DEF
            .iter()
            .flat_map(|(name, def)| {
                (*INTRINSIC_VARIABLES)[*name].iter().map(
                    move |(_, id)| {
                        format!(
                            "let ${}${}={}",
                            id,
                            convert_name(name),
                            def
                        )
                    },
                )
            })
            .join(""),
        ast.data_declarations
            .into_iter()
            .map(data_declaration)
            .join(""),
        ast.declarations.iter().map(declaration).join(""),
        ast.entry_point.unwrap()
    )
}

fn data_declaration(d: DataDeclaration) -> String {
    let name = convert_name(&d.name);
    format!(
        "let ${}${}={}({{name:'{}',{}}});",
        d.decl_id,
        name,
        (0..d.field_len).map(|i| format!("${}=>", i)).join(""),
        name,
        (0..d.field_len).map(|i| format!("{0}:${0}", i)).join(", "),
    )
}

fn declaration(d: &Declaration) -> String {
    format!(
        "let ${}${}={};",
        d.decl_id,
        convert_name(&d.identifier),
        expr(&d.value, 0)
    )
}

static PRIMITIVES_DEF: Lazy<HashMap<&str, &str>> = Lazy::new(|| {
    [
        ("num_to_string", "a => String(a);"),
        ("<", "a => b => $$bool(a < b);"),
        ("-", "a => b => a - b;"),
        ("+", "a => b => a + b;"),
        ("print", "a => process.stdout.write(a);"),
        ("println", "a => console.log(a);"),
        ("True", "{name: 'True'};"),
        ("False", "{name: 'False'};"),
        ("%", "a => b => a % b;"),
        ("!=", "a => b => $$bool(a !== b);"),
    ]
    .iter()
    .copied()
    .collect()
});

fn expr(e: &Expr, name_count: u32) -> String {
    match e {
        Expr::Lambda(a) => format!(
            r#"{}{}$$unexpected()"#,
            (0..a[0].pattern.len())
                .map(|c| format!("${}=>", name_count + c as u32))
                .join(""),
            a.iter().map(|e| fn_arm(e, name_count)).join("")
        ),
        Expr::Number(a) => a.clone(),
        Expr::StrLiteral(a) => a.clone(),
        Expr::Identifier { info, decl_id, .. } => {
            format!("${}${}", decl_id.unwrap(), convert_name(info))
        }
        Expr::Declaration(a) => declaration(a),
        Expr::Call(f, a) => format!(
            "{}({})",
            expr(&*f, name_count),
            expr(&*a, name_count)
        ),
        Expr::Unit => "$unicode_28_29".to_string(),
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
            "{}?{}:",
            cond,
            multi_expr(&e.exprs, name_count + e.pattern.len() as u32),
        )
    } else {
        format!(
            "{}?({}{}){}:",
            cond,
            binds
                .iter()
                .map(|(s, _, id)| format!("${}${}=>", id, s))
                .join(""),
            multi_expr(&e.exprs, name_count + e.pattern.len() as u32),
            binds.iter().map(|(_, n, _)| format!("({})", n)).join(""),
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
    .join("&&");
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
                vec![format!("{}==={}", a, n)]
            }
            Pattern::Constructor(a, ps) => {
                let mut v = vec![format!(
                    "'{}'==={}.name",
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
) -> Vec<(&str, String, DeclId)> {
    _bindings(
        pattern,
        (0..pattern.len())
            .map(|i| format!("${}", i + name_count as usize))
            .collect(),
    )
}

fn _bindings(
    pattern: &[Pattern],
    names: Vec<String>,
) -> Vec<(&str, String, DeclId)> {
    pattern
        .iter()
        .zip(names)
        .flat_map(|(p, n)| match p {
            Pattern::Binder(a, id) => vec![(&a[..], n, *id)],
            Pattern::Constructor(_, ps) => _bindings(
                ps,
                (0..ps.len())
                    .map(|i| format!("{}[{}]", n, i))
                    .collect(),
            ),
            _ => Vec::new(),
        })
        .collect()
}

fn convert_name(name: &str) -> String {
    if is_valid_js_name(name) {
        name.to_string()
    } else {
        "unicode".to_string()
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
