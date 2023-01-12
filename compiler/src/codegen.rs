mod type_restriction_pattern;

use self::type_restriction_pattern::IS_INSTANCE_OF;
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step2::types::merge_vec;
use crate::ast_step3::{DataDecl, VariableId};
use crate::ast_step4::{PatternUnit, Type};
use crate::ast_step5::{Ast, Expr, ExprWithType, FnArm, Pattern, VariableDecl};
use crate::intrinsics::{IntrinsicConstructor, IntrinsicVariable};
use fxhash::FxHashMap;
use itertools::Itertools;
use once_cell::sync::Lazy;
use std::fmt::Write;
use stripmargin::StripMargin;
use unic_ucd_category::GeneralCategory;

pub fn codegen(ast: Ast) -> String {
    format!(
        "let $$bool=a=>a?{}:{};{}{IS_INSTANCE_OF}{}{}{}{}${}$main({});}}",
        PRIMITIVE_CONSTRUCTOR_DEF[&IntrinsicConstructor::True],
        PRIMITIVE_CONSTRUCTOR_DEF[&IntrinsicConstructor::False],
        r#"{
        |let $$unexpected=()=>{throw new Error("unexpected")};
        |let $field_accessor=i=>a=>a[i];
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
        PRIMITIVE_CONSTRUCTOR_DEF
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
        PRIMITIVE_CONSTRUCTOR_DEF[&IntrinsicConstructor::Unit],
    )
}

fn data_decl(d: DataDecl) -> String {
    let name = convert_name(&d.name.to_string());
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
        convert_name(&d.name.to_string()),
        expr(&d.value, 0)
    )
}

static PRIMITIVES_DEF: Lazy<FxHashMap<IntrinsicVariable, &'static str>> =
    Lazy::new(|| {
        use IntrinsicVariable::*;
        [
            (I64ToString, "a => String(a)"),
            (Lt, "a => b => $$bool(a < b)"),
            (Minus, "a => b => a - b"),
            (Plus, "a => b => a + b"),
            (Multi, "a => b => a * b"),
            (Print, "a => process.stdout.write(a)"),
            (Println, "a => console.log(a)"),
            (Percent, "a => b => a % b"),
            (Neq, "a => b => $$bool(a !== b)"),
            (Eq, "a => b => $$bool(a === b)"),
            (Append, "a => b => a + b"),
        ]
        .iter()
        .copied()
        .collect()
    });

static PRIMITIVE_CONSTRUCTOR_DEF: Lazy<
    FxHashMap<IntrinsicConstructor, &'static str>,
> = Lazy::new(|| {
    use IntrinsicConstructor::*;
    [
        (True, "{name: '$True$True'}"),
        (False, "{name: '$False$False'}"),
        (Unit, "{name: '$Unit$unicode_28_29'}"),
    ]
    .iter()
    .copied()
    .collect()
});

fn expr((e, t): &ExprWithType, name_count: u32) -> String {
    let s = match e {
        Expr::Lambda(a) => {
            let bindings = a.iter().flat_map(|e| bindings(&e.pattern));
            format!(
                r#"({}{{{}return {}$$unexpected()}})"#,
                (0..a[0].pattern.len())
                    .map(|c| format!("${}=>", name_count + c as u32))
                    .join(""),
                bindings.format_with("", |(name, id, t), f| f(&format_args!(
                    "let ${id}${name} /* : {t} */;",
                ))),
                a.iter().map(|e| fn_arm(e, name_count)).join("")
            )
        }
        Expr::Number(a) => a.to_string(),
        Expr::StrLiteral(a) => format!("\"{}\"", a),
        Expr::Ident {
            name: _,
            variable_id:
                VariableId::FieldAccessor {
                    constructor: _,
                    field,
                },
        } => {
            format!("$field_accessor({field})")
        }
        Expr::Ident { name, variable_id } => {
            format!(
                "${}${} /* ({}) */",
                variable_id,
                convert_name(name.to_string().as_str()),
                name,
            )
        }
        Expr::Call(f, a) => {
            format!("{}({})", expr(f, name_count), expr(a, name_count))
        }
        Expr::DoBlock(exprs) => {
            format!("({})", exprs.iter().map(|e| expr(e, name_count)).join(","))
        }
    };
    format!("{s} /*: {t} */")
}

fn fn_arm(e: &FnArm, name_count: u32) -> String {
    let cond = condition(&e.pattern, name_count);
    format!(
        "{}?{}:",
        cond,
        expr(&e.expr, name_count + e.pattern.len() as u32),
    )
}

fn condition(pattern: &[Pattern], name_count: u32) -> String {
    let mut condition = "true".to_string();
    _condition(
        pattern,
        &(0..pattern.len())
            .map(|i| format!("${}", i + name_count as usize))
            .collect_vec(),
        name_count + pattern.len() as u32,
        &mut condition,
    );
    condition
}

fn single_condition(
    p: &Pattern,
    arg: &str,
    name_count: u32,
    condition: &mut String,
) {
    if p.patterns.len() != 1 {
        unimplemented!()
    }
    use PatternUnit::*;
    match &p.patterns[0] {
        I64(a) | Str(a) => {
            write!(condition, "&&{}==={}", a, arg).unwrap();
        }
        Constructor { id, name } => {
            write!(
                condition,
                "&&'${}${}'==={}.name",
                id,
                convert_name(&name.to_string()),
                arg
            )
            .unwrap();
        }
        TypeRestriction(p, t) => {
            write!(
                condition,
                "&&is_instance_of({},{},[])",
                arg,
                t.type_to_js_obj().0
            )
            .unwrap();
            single_condition(p, arg, name_count, condition);
        }
        Apply {
            pre_pattern,
            function,
            post_pattern,
        } => {
            let tmp = format!("$tmp${}", tmp_variable::new());
            write!(condition, "&&({tmp}={arg},true)").unwrap();
            single_condition(pre_pattern, &tmp, name_count, condition);
            let f = expr(function, name_count);
            single_condition(
                post_pattern,
                &format!("{}({})", f, tmp),
                name_count,
                condition,
            );
        }
        Binder(name, decl_id) => {
            write!(
                condition,
                "&&(${decl_id}${}={arg},true)",
                convert_name(name)
            )
            .unwrap();
        }
        Underscore => (),
    }
}

fn _condition(
    pattern: &[Pattern],
    names: &[String],
    name_count: u32,
    condition: &mut String,
) {
    for (p, arg) in pattern.iter().zip(names) {
        single_condition(p, arg, name_count, condition);
    }
}

fn bindings(pattern: &[Pattern]) -> Vec<(String, DeclId, &Type)> {
    fn _bindings_unit(p: &Pattern) -> Vec<(String, DeclId, &Type)> {
        if p.patterns.len() == 1 {
            match &p.patterns[0] {
                PatternUnit::Binder(a, id) => {
                    vec![(convert_name(a), *id, &p.type_)]
                }
                PatternUnit::TypeRestriction(p, _) => _bindings_unit(p),
                PatternUnit::Apply {
                    pre_pattern,
                    post_pattern,
                    function: _,
                } => merge_vec(
                    _bindings_unit(pre_pattern),
                    _bindings_unit(post_pattern),
                ),
                _ => Vec::new(),
            }
        } else {
            unimplemented!()
        }
    }
    pattern.iter().flat_map(_bindings_unit).collect()
}

fn convert_name(name: &str) -> String {
    if is_valid_name(name) {
        name.to_string()
    } else {
        "unicode".to_string()
            + &name.chars().map(|c| format! {"_{:x}",c as u32}).join("")
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

mod tmp_variable {
    use std::sync::Mutex;

    static COUNT: Mutex<u32> = Mutex::new(0);

    pub fn new() -> u32 {
        let mut c = COUNT.lock().unwrap();
        *c += 1;
        *c
    }
}
