use crate::{
    ast_step2::{decl_id::DeclId, Pattern, PatternUnit},
    ast_step4::{
        Ast, DataDecl, Expr, ExprWithType, FnArm, VariableDecl,
    },
    intrinsics::IntrinsicVariable,
};
use fxhash::FxHashMap;
use itertools::Itertools;
use once_cell::sync::Lazy;
use stripmargin::StripMargin;
use unic_ucd_category::GeneralCategory;

pub fn codegen(ast: Ast) -> String {
    format!(
        "let $$bool=a=>a?{}:{};{}{}{}{}${}$main({});}}",
        PRIMITIVES_DEF[&IntrinsicVariable::True],
        PRIMITIVES_DEF[&IntrinsicVariable::False],
        r#"{
        |let $$unexpected = () => {throw new Error("unexpected")};
        |"#
        .strip_margin(),
        PRIMITIVES_DEF
            .iter()
            .map(|(variable, def)| {
                format!(
                    "let ${}${}={};",
                    variable,
                    convert_name(variable.to_str()),
                    def
                )
            })
            .join(""),
        ast.data_decl.into_iter().map(data_decl).join(""),
        ast.variable_decl.iter().map(variable_decl).join(""),
        ast.entry_point,
        PRIMITIVES_DEF[&IntrinsicVariable::Unit],
    )
}

fn data_decl(d: DataDecl) -> String {
    let name = convert_name(d.name);
    format!(
        "let ${}${}={}({{name:'${}${}',{}}});",
        d.decl_id,
        name,
        (0..d.field_len).map(|i| format!("${}=>", i)).join(""),
        d.decl_id,
        name,
        (0..d.field_len).map(|i| format!("{0}:${0}", i)).join(", "),
    )
}

fn variable_decl(d: &VariableDecl) -> String {
    format!(
        "let ${}${}={};",
        d.decl_id,
        convert_name(d.name),
        expr(&d.value, 0)
    )
}

static PRIMITIVES_DEF: Lazy<FxHashMap<IntrinsicVariable, &str>> =
    Lazy::new(|| {
        use IntrinsicVariable::*;
        [
            (I64ToString, "a => String(a)"),
            (Lt, "a => b => $$bool(a < b)"),
            (Minus, "a => b => a - b"),
            (Plus, "a => b => a + b"),
            (Print, "a => process.stdout.write(a)"),
            (Println, "a => console.log(a)"),
            (True, "{name: '$True$True'}"),
            (False, "{name: '$False$False'}"),
            (Percent, "a => b => a % b"),
            (Neq, "a => b => $$bool(a !== b)"),
            (Unit, "{name: '$Unit$unicode_28_29'}"),
        ]
        .iter()
        .copied()
        .collect()
    });

fn expr((e, t): &ExprWithType, name_count: u32) -> String {
    let s = match e {
        Expr::Lambda(a) => format!(
            r#"({}{}$$unexpected())"#,
            (0..a[0].pattern.len())
                .map(|c| format!("${}=>", name_count + c as u32))
                .join(""),
            a.iter().map(|e| fn_arm(e, name_count)).join("")
        ),
        Expr::Number(a) => a.to_string(),
        Expr::StrLiteral(a) => format!("\"{}\"", a),
        Expr::Ident {
            name: info,
            variable_id,
            type_args,
        } => {
            format!(
                "${}${} /* ({}) [{}] */",
                variable_id,
                convert_name(info),
                info,
                type_args.iter().format_with("", |args, f| f(
                    &format!(
                        "[args: ({})]",
                        args.iter().format(", ")
                    )
                ))
            )
        }
        Expr::Call(f, a) => format!(
            "{}({})",
            expr(f, name_count),
            expr(a, name_count)
        ),
        Expr::DoBlock(exprs) => {
            format!(
                "({})",
                exprs.iter().map(|e| expr(e, name_count)).join(",")
            )
        }
    };
    format!("{s} /*: {t} */")
}

fn fn_arm(e: &FnArm, name_count: u32) -> String {
    let cond = condition(&e.pattern, name_count);
    let binds = bindings(&e.pattern, name_count);
    if binds.is_empty() {
        format!(
            "{}?{}:",
            cond,
            expr(&e.expr, name_count + e.pattern.len() as u32),
        )
    } else {
        format!(
            "{}?({}{}){}:",
            cond,
            binds
                .iter()
                .map(|(s, _, id)| format!("${}${}=>", id, s))
                .join(""),
            expr(&e.expr, name_count + e.pattern.len() as u32),
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
        .flat_map(|(p, n)| {
            if p.len() == 1 {
                use PatternUnit::*;
                match &p[0] {
                    I64(a) | Str(a) => {
                        vec![format!("{}==={}", a, n)]
                    }
                    Constructor { id, args } => {
                        let mut v = vec![format!(
                            "'${}${}'==={}.name",
                            id,
                            convert_name(id.name()),
                            n
                        )];
                        v.append(&mut _condition(
                            args,
                            &(0..args.len())
                                .map(|i| format!("{}[{}]", n, i))
                                .collect_vec(),
                        ));
                        v
                    }
                    _ => Vec::new(),
                }
            } else {
                unimplemented!()
            }
        })
        .collect()
}

fn bindings<'a>(
    pattern: &'a [Pattern],
    name_count: u32,
) -> Vec<(&'a str, String, DeclId)> {
    _bindings(
        pattern,
        (0..pattern.len())
            .map(|i| format!("${}", i + name_count as usize))
            .collect(),
    )
}

fn _bindings<'a>(
    pattern: &'a [Pattern],
    names: Vec<String>,
) -> Vec<(&'a str, String, DeclId)> {
    pattern
        .iter()
        .zip(names)
        .flat_map(|(p, n)| {
            if p.len() == 1 {
                match &p[0] {
                    PatternUnit::Binder(a, id) => {
                        vec![(&a[..], n, *id)]
                    }
                    PatternUnit::Constructor { args, .. } => {
                        _bindings(
                            args,
                            (0..args.len())
                                .map(|i| format!("{}[{}]", n, i))
                                .collect(),
                        )
                    }
                    _ => Vec::new(),
                }
            } else {
                unimplemented!()
            }
        })
        .collect()
}

fn convert_name(name: &str) -> String {
    if is_valid_name(name) {
        name.to_string()
    } else {
        "unicode".to_string()
            + &name
                .chars()
                .map(|c| format! {"_{:x}",c as u32})
                .join("")
    }
}

fn is_valid_name(name: &str) -> bool {
    name.chars().all(|c| {
        GeneralCategory::of(c).is_letter()
            || matches!(
                GeneralCategory::of(c),
                GeneralCategory::DecimalNumber
                    | GeneralCategory::NonspacingMark
                    | GeneralCategory::SpacingMark
                    | GeneralCategory::ConnectorPunctuation
                    | GeneralCategory::LetterNumber
            )
            || c == '_'
    }) && !(name.len() >= 8 && name[0..8] == *"unicode_")
}
