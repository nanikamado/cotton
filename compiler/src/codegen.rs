mod type_restriction_pattern;

use self::type_restriction_pattern::IS_INSTANCE_OF;
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step2::types::merge_vec;
use crate::ast_step2::{get_type_name, TypeId};
use crate::ast_step3::{DataDecl, VariableId};
use crate::ast_step4::Type;
use crate::ast_step5::{
    Ast, Expr, ExprWithType, FnArm, Function, LambdaId, Pattern, PatternUnit,
    VariableDecl,
};
use crate::intrinsics::{IntrinsicConstructor, IntrinsicVariable};
use fxhash::FxHashMap;
use itertools::Itertools;
use once_cell::sync::Lazy;
use std::fmt::{Display, Write};
use stripmargin::StripMargin;
use strum::IntoEnumIterator;
use unic_ucd_category::GeneralCategory;

pub fn codegen(ast: Ast) -> String {
    format!(
        "let $$bool=a=>a?{}:{};{}{IS_INSTANCE_OF}{}{}{}{}{}{}({},{{}});}}",
        PRIMITIVE_CONSTRUCTOR_DEF[&IntrinsicConstructor::True],
        PRIMITIVE_CONSTRUCTOR_DEF[&IntrinsicConstructor::False],
        r#"{
        |let $$unexpected=()=>{throw new Error("unexpected")};
        |let $field_accessor=i=>a=>a[i];
        |"#
        .strip_margin(),
        IntrinsicVariable::iter()
            .map(|v| format!("let $intrinsic${}={};", v, primitive_def(v)))
            .format(""),
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
        ast.functions
            .into_iter()
            .map(|f| FunctionWithEnv(f, &ast.variable_names))
            .join(""),
        ast.data_decl.into_iter().map(data_decl).join(""),
        ast.variable_decl
            .iter()
            .map(|d| variable_decl(d, &ast.variable_names))
            .join(""),
        ast.entry_point,
        PRIMITIVE_CONSTRUCTOR_DEF[&IntrinsicConstructor::Unit],
    )
}

struct FunctionWithEnv<'a>(Function, &'a FxHashMap<VariableId, String>);

impl Display for FunctionWithEnv<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let context = self
            .0
            .context
            .iter()
            .enumerate()
            .map(|(i, c)| (*c, i))
            .collect();
        let mut env = Env {
            context: &context,
            variable_names: self.1,
        };
        let e = expr(&self.0.body, &mut env);
        write!(
            f,
            "let {}/*(lm{},{})*/=(${}$pa,ctx)=>{};",
            LambdaId::Normal(self.0.id),
            self.0.original_id,
            self.0.origin_type,
            self.0.parameter,
            e
        )
    }
}

fn data_decl(d: DataDecl) -> String {
    let name = convert_name(&d.name.to_string());
    format!(
        "let ${}${}=({})=>({{name:'${}${}',{}}});",
        d.decl_id,
        name,
        (0..d.field_len).format_with(",", |i, f| f(&format_args!("${i}"))),
        d.decl_id,
        name,
        (0..d.field_len).map(|i| format!("{i}:${i}")).join(", "),
    )
}

fn variable_decl(
    d: &VariableDecl,
    variable_names: &FxHashMap<VariableId, String>,
) -> String {
    let mut env = Env {
        context: &Default::default(),
        variable_names,
    };
    format!(
        "let ${}${}={};",
        d.decl_id,
        convert_name(&d.name.to_string()),
        expr(&d.value, &mut env)
    )
}

fn primitive_def(i: IntrinsicVariable) -> &'static str {
    match i {
        IntrinsicVariable::Minus => "(a, b) => a - b",
        IntrinsicVariable::Plus => "(a, b) => a + b",
        IntrinsicVariable::Percent => "(a, b) => a % b",
        IntrinsicVariable::Multi => "(a, b) => a * b",
        IntrinsicVariable::Div => {
            r#"(a,b)=>b===0?(()=>{throw new Error("division by zero")})():~~(a / b)"#
        }
        IntrinsicVariable::Lt => "(a, b) => $$bool(a < b)",
        IntrinsicVariable::Neq => "(a, b) => $$bool(a !== b)",
        IntrinsicVariable::Eq => "(a, b) => $$bool(a === b)",
        IntrinsicVariable::PrintStr => "a => process.stdout.write(a)",
        IntrinsicVariable::I64ToString => "a => String(a)",
        IntrinsicVariable::AppendStr => "(a, b) => a + b",
    }
}

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

struct DeclIdWithEnv<'a> {
    decl_id: DeclId,
    ctx: &'a FxHashMap<DeclId, usize>,
    variable_names: &'a FxHashMap<VariableId, String>,
}

impl Display for DeclIdWithEnv<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(c) = self.ctx.get(&self.decl_id) {
            write!(f, "ctx._{c}")
        } else {
            write!(
                f,
                "{}",
                VariableIdWithEnv(
                    VariableId::Local(self.decl_id),
                    self.variable_names
                )
            )
        }
    }
}

struct VariableIdWithEnv<'a>(VariableId, &'a FxHashMap<VariableId, String>);

impl Display for VariableIdWithEnv<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let VariableId::IntrinsicVariable(_) = self.0 {
            write!(f, "$intrinsic${}", self.0)
        } else if let VariableId::IntrinsicConstructor(i) = self.0 {
            write!(
                f,
                "${}${}",
                self.0,
                convert_name(
                    get_type_name(TypeId::Intrinsic(i.into()))
                        .unwrap()
                        .to_string()
                        .as_str()
                )
            )
        } else if self.1.contains_key(&self.0) {
            write!(f, "${}${}", self.0, convert_name(self.1[&self.0].as_str()))
        } else {
            write!(f, "${}$pa", self.0)
        }
    }
}

struct Env<'a> {
    context: &'a FxHashMap<DeclId, usize>,
    variable_names: &'a FxHashMap<VariableId, String>,
}

fn expr((e, t): &ExprWithType, env: &mut Env) -> String {
    let s = match e {
        Expr::Lambda {
            tag,
            context: ctx,
            lambda_id: _,
        } => {
            format!(
                r#"({{name:"fn",tag:{tag},ctx:{{{}}}}})"#,
                ctx.iter().enumerate().format_with(",", |(i, c), f| f(
                    &format_args!(
                        "_{i}:{}",
                        DeclIdWithEnv {
                            decl_id: *c,
                            ctx: env.context,
                            variable_names: env.variable_names
                        }
                    )
                ))
            )
        }
        Expr::Match { arms, arguments } => {
            let bindings = arms.iter().flat_map(|e| bindings(&e.pattern));
            format!(
                r#"{{{}return {}$$unexpected()}}"#,
                bindings.format_with("", |(id, t), f| f(&format_args!(
                    "let {} /* -- {t} */;",
                    VariableIdWithEnv(
                        VariableId::Local(id),
                        env.variable_names
                    )
                ))),
                arms.iter().map(|e| fn_arm(e, arguments, env)).join("")
            )
        }
        Expr::Number(a) => a.to_string(),
        Expr::StrLiteral(a) => format!("{a:?}"),
        Expr::Ident {
            variable_id:
                VariableId::FieldAccessor {
                    constructor: _,
                    field,
                },
        } => {
            format!("$field_accessor({field})")
        }
        Expr::Ident {
            variable_id: VariableId::Local(decl_id),
        } => {
            format!(
                "{} /* ({}) */",
                DeclIdWithEnv {
                    decl_id: *decl_id,
                    variable_names: env.variable_names,
                    ctx: env.context
                },
                env.variable_names[&VariableId::Local(*decl_id)],
            )
        }
        Expr::Ident { variable_id } => {
            format!(
                "{} /* ({}) */",
                VariableIdWithEnv(*variable_id, env.variable_names),
                env.variable_names[variable_id],
            )
        }
        Expr::Call {
            f,
            a,
            possible_functions,
        } => {
            format!(
                "((tmp,a)=>{}$$unexpected())({},{})",
                possible_functions.iter().enumerate().format_with(
                    "",
                    |(i, lambda_id), f| f(&format_args!(
                        "tmp.tag==={i}?{lambda_id}(a,tmp.ctx):"
                    ))
                ),
                expr(f, env),
                expr(a, env),
            )
        }
        Expr::DoBlock(exprs) => {
            format!("({})", exprs.iter().map(|e| expr(e, env)).join(","))
        }
        Expr::BasicCall { args, id } => {
            use crate::ast_step3::BasicFunction::*;
            match id {
                Intrinsic(id) => {
                    format!(
                        "$intrinsic${id}({})",
                        args.iter().format_with(",", |a, f| f(&format_args!(
                            "{}",
                            expr(a, env)
                        )))
                    )
                }
                Construction(id) => {
                    if args.is_empty() {
                        format!(
                            "${id}${}",
                            convert_name(
                                get_type_name(TypeId::from(*id))
                                    .unwrap()
                                    .to_string()
                                    .as_str()
                            ),
                        )
                    } else {
                        format!(
                            "${id}${}({})",
                            convert_name(
                                get_type_name(TypeId::from(*id))
                                    .unwrap()
                                    .to_string()
                                    .as_str()
                            ),
                            args.iter().format_with(",", |a, f| f(
                                &format_args!("{}", expr(a, env))
                            ))
                        )
                    }
                }
            }
        }
    };
    format!("{s} /* -- {t} */")
}

fn fn_arm(e: &FnArm, names: &[DeclId], env: &mut Env) -> String {
    let cond = condition(&e.pattern, names, env);
    format!("{}?{}:", cond, expr(&e.expr, env))
}

fn condition(pattern: &[Pattern], names: &[DeclId], env: &mut Env) -> String {
    let mut condition = "true".to_string();
    _condition(pattern, names, &mut condition, env);
    condition
}

fn single_condition(
    p: &Pattern,
    arg: &str,
    condition: &mut String,

    env: &mut Env,
) {
    if p.patterns.len() != 1 {
        unimplemented!()
    }
    use PatternUnit::*;
    match &p.patterns[0] {
        I64(a) | Str(a) => {
            write!(condition, "&&{a}==={arg}").unwrap();
        }
        Constructor { id } => {
            write!(
                condition,
                "&&'{}'==={}.name",
                VariableIdWithEnv((*id).into(), env.variable_names),
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
            single_condition(p, arg, condition, env);
        }
        Apply {
            pre_pattern,
            function,
            post_pattern,
            possible_functions,
        } => {
            let tmp = format!("$tmp${}", tmp_variable::new());
            write!(condition, "&&({tmp}={arg},true)").unwrap();
            single_condition(pre_pattern, &tmp, condition, env);
            let tmp2 = format!("$tmp${}", tmp_variable::new());
            let f = expr(function, env);
            write!(condition, "&&({tmp2}={f},true)").unwrap();
            single_condition(
                post_pattern,
                &format!(
                    "({}$$unexpected())",
                    possible_functions.iter().enumerate().format_with(
                        "",
                        |(i, lambda_id), f| f(&format_args!(
                            "{tmp2}.tag==={i}?{lambda_id}({tmp},{tmp2}.ctx):"
                        ))
                    ),
                ),
                condition,
                env,
            );
        }
        Binder(decl_id) => {
            write!(
                condition,
                "&&({}={arg},true)",
                VariableIdWithEnv(
                    VariableId::Local(*decl_id),
                    env.variable_names
                )
            )
            .unwrap();
        }
        Underscore => (),
    }
}

fn _condition(
    pattern: &[Pattern],
    names: &[DeclId],
    condition: &mut String,

    env: &mut Env,
) {
    for (p, arg) in pattern.iter().zip(names) {
        single_condition(
            p,
            DeclIdWithEnv {
                decl_id: *arg,
                ctx: env.context,
                variable_names: env.variable_names,
            }
            .to_string()
            .as_str(),
            condition,
            env,
        );
    }
}

fn bindings(pattern: &[Pattern]) -> Vec<(DeclId, &Type)> {
    fn _bindings_unit(p: &Pattern) -> Vec<(DeclId, &Type)> {
        if p.patterns.len() == 1 {
            match &p.patterns[0] {
                PatternUnit::Binder(id) => {
                    vec![(*id, &p.type_)]
                }
                PatternUnit::TypeRestriction(p, _) => _bindings_unit(p),
                PatternUnit::Apply {
                    pre_pattern,
                    post_pattern,
                    function: _,
                    possible_functions: _,
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
