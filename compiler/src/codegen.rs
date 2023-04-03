mod c_type;
mod collector;
mod type_restriction_pattern;

use self::c_type::{CAggregateType, CType};
use self::type_restriction_pattern::IS_INSTANCE_OF;
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step2::ConstructorId;
use crate::ast_step3::DataDecl;
use crate::ast_step5::{
    Ast, Block, Expr, Instruction, LocalVariable, LocalVariableCollector,
    TaggedFn, Tester, Type, VariableDecl, VariableId,
};
use crate::intrinsics::{IntrinsicConstructor, IntrinsicVariable};
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use std::fmt::{Display, Write};
use stripmargin::StripMargin;
use strum::IntoEnumIterator;
use unic_ucd_category::GeneralCategory;

pub fn codegen(ast: Ast) -> String {
    let function_context = ast
        .functions
        .iter()
        .map(|f| {
            (
                f.id,
                f.context
                    .iter()
                    .map(|&c| ast.variable_types.get_type(c).clone())
                    .collect_vec(),
            )
        })
        .collect();
    let mut c_type_env = c_type::Env {
        function_context,
        aggregate_types: Default::default(),
        memo: Default::default(),
        fx_type_map: ast.fx_type_map,
    };
    let local_variable_types: LocalVariableCollector<(Type, CType)> =
        ast.variable_types.map(|t| {
            let ct = c_type_env.c_type(&t, None);
            (t, ct)
        });
    let global_variable_types = ast
        .variable_decls
        .iter()
        .map(|d| (d.decl_id, c_type_env.c_type(&d.t, None)))
        .collect();
    let env = Env {
        context: &Default::default(),
        variable_names: &ast.variable_names,
        local_variable_types: &local_variable_types,
        global_variable_types: &global_variable_types,
    };
    let mut s = String::new();
    write!(
        &mut s,
        "let $$bool=a=>a?{{tag:0}}:{{tag:1}};{}{IS_INSTANCE_OF}{}{}{}{}
        /*{}*/",
        r#"
        |let $$unexpected=()=>{throw new Error("unexpected")};
        |let $field_accessor=(i,a)=>a[i];
        |"#
        .strip_margin(),
        IntrinsicVariable::iter()
            .map(|v| format!("let $intrinsic${}={};", v, primitive_def(v)))
            .format(""),
        IntrinsicConstructor::iter().format_with("", |i, f| f(&format_args!(
            "let {0}=()=>{{name: '{0}'}};",
            Dis(&ConstructorId::Intrinsic(i), &env),
        ))),
        ast.data_decls
            .into_iter()
            .format_with("", |d, f| f(&Dis(&d, &env))),
        ast.variable_decls
            .iter()
            .format_with("", |d, f| f(&format_args!(
                "let ${}${}=()=>{};",
                d.decl_id,
                convert_name(
                    &env.variable_names[&VariableId::Global(d.decl_id)]
                ),
                Dis(&TerminalBlock(&d.value, d.ret), &env)
            ))),
        c_type_env.aggregate_types.into_raw().iter().format_with(
            "",
            |(t, i), f| {
                match t {
                    CAggregateType::Struct(fields) => f(&format_args!(
                        "{} {{{}}}\n",
                        CType::Aggregate(*i),
                        fields
                            .iter()
                            .enumerate()
                            .format_with("", |(i, field), f| f(&format_args!(
                                "{field} _{i};",
                            )))
                    )),
                    CAggregateType::Union(ts) => f(&format_args!(
                        "{} {{int tag;union {{{}}} value}}\n",
                        CType::Aggregate(*i),
                        ts.iter().enumerate().format_with("", |(i, t), f| f(
                            &format_args!("{t} _{i};")
                        ))
                    )),
                }
            }
        )
    )
    .unwrap();
    write!(
        &mut s,
        "{}{}({{tag:0}},{{}});",
        ast.functions.into_iter().format_with("", |function, f| {
            let env = Env {
                context: &function
                    .context
                    .into_iter()
                    .enumerate()
                    .map(|(i, d)| (d, i))
                    .collect(),
                variable_names: &ast.variable_names,
                local_variable_types: &local_variable_types,
                global_variable_types: &global_variable_types,
            };
            let (t, ct) = env.local_variable_types.get_type(function.parameter);
            f(&format_args!(
                "let {}=({}/*({},{})*/,ctx)=>{};",
                function.id,
                Dis(&VariableId::Local(function.parameter), &env),
                ct,
                t,
                Dis(&TerminalBlock(&function.body, function.ret), &env)
            ))
        }),
        ast.entry_point
    )
    .unwrap();
    s
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

#[derive(Debug)]
struct Env<'a> {
    context: &'a FxHashMap<LocalVariable, usize>,
    variable_names: &'a FxHashMap<VariableId, String>,
    local_variable_types: &'a LocalVariableCollector<(Type, CType)>,
    global_variable_types: &'a FxHashMap<DeclId, CType>,
}

fn collect_local_variables_block(b: &Block, vs: &mut FxHashSet<LocalVariable>) {
    for i in &b.instructions {
        match i {
            Instruction::Assign(Some(d), _) => {
                vs.insert(*d);
            }
            Instruction::TryCatch(a, b) => {
                collect_local_variables_block(a, vs);
                collect_local_variables_block(b, vs);
            }
            _ => (),
        }
    }
}

struct Dis<'a, T>(&'a T, &'a Env<'a>);

impl<'a, T: DisplayWithEnv> Display for Dis<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt_with_env(self.1, f)
    }
}

trait DisplayWithEnv {
    fn fmt_with_env(
        &self,
        env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result;
}

impl DisplayWithEnv for DataDecl {
    fn fmt_with_env(
        &self,
        env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "let {0}=({1})=>({{name:'{0}',{2}}});",
            Dis(&ConstructorId::DeclId(self.decl_id), env),
            (0..self.field_len)
                .format_with(",", |i, f| f(&format_args!("${i}"))),
            (0..self.field_len).map(|i| format!("{i}:${i}")).join(", "),
        )
    }
}

impl DisplayWithEnv for VariableDecl {
    fn fmt_with_env(
        &self,
        env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let ct = &env.global_variable_types[&self.decl_id];
        write!(
            f,
            "let {}/*({},{})*/=(()=>({{{}||$$unexpected();{}}}))();",
            Dis(&VariableId::Global(self.decl_id), env),
            ct,
            self.t,
            Dis(&self.value, env),
            Dis(&self.ret, env)
        )
    }
}

struct TerminalBlock<'a>(&'a Block, VariableId);

impl DisplayWithEnv for TerminalBlock<'_> {
    fn fmt_with_env(
        &self,
        env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let mut vs = FxHashSet::default();
        collect_local_variables_block(self.0, &mut vs);
        if vs.is_empty() {
            write!(
                f,
                "{{{}||$$unexpected();return {};}}",
                Dis(self.0, env),
                Dis(&self.1, env)
            )
        } else {
            write!(
                f,
                "{{let {};{}||$$unexpected();return {};}}",
                vs.iter().format_with(",", |v, f| {
                    let (t, ct) = env.local_variable_types.get_type(*v);
                    f(&format_args!(
                        "{}/*({},{})*/",
                        Dis(&VariableId::Local(*v), env),
                        ct,
                        t
                    ))
                }),
                Dis(self.0, env),
                Dis(&self.1, env)
            )
        }
    }
}

impl DisplayWithEnv for Block {
    fn fmt_with_env(
        &self,
        env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        if self.instructions.is_empty() {
            write!(f, "true")
        } else {
            write!(f, "(")?;
            self.instructions[0].fmt_with_env(env, f)?;
            for i in &self.instructions[1..] {
                write!(f, "&&")?;
                i.fmt_with_env(env, f)?;
            }
            write!(f, ")")
        }
    }
}

struct TagCheck<'a>(&'a u32, VariableId);

impl DisplayWithEnv for TagCheck<'_> {
    fn fmt_with_env(
        &self,
        env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "{}.tag==={}", Dis(&self.1, env), self.0)
    }
}

impl DisplayWithEnv for Instruction {
    fn fmt_with_env(
        &self,
        env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            Instruction::Assign(d, e) => {
                match d {
                    Some(d) => {
                        write!(f, "({}=", Dis(&VariableId::Local(*d), env),)?
                    }
                    None => write!(f, "(")?,
                }
                write!(f, "{},true)", Dis(e, env))
            }
            Instruction::Test(Tester::Constructor { id, tag }, e) => {
                write!(f, "({}/* is {}? */)", Dis(&TagCheck(tag, *e), env), id)
            }
            Instruction::Test(Tester::I64 { value }, e) => {
                write!(f, "({}==={value})", Dis(e, env))
            }
            Instruction::Test(Tester::Str { value }, e) => {
                write!(f, "({}==={value:?})", Dis(e, env))
            }
            Instruction::FailTest => {
                write!(f, "false")
            }
            Instruction::TryCatch(a, b) => {
                write!(f, "({}||{})", Dis(a, env), Dis(b, env))
            }
        }
    }
}

impl DisplayWithEnv for Expr {
    fn fmt_with_env(
        &self,
        env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            Expr::Lambda {
                lambda_id: _,
                context,
            } => write!(
                f,
                r#"({{{}}})"#,
                context.iter().enumerate().format_with(",", |(i, c), f| f(
                    &format_args!("_{i}:{}", Dis(&VariableId::Local(*c), env))
                ))
            ),
            Expr::I64(a) => write!(f, "{a}"),
            Expr::Str(a) => write!(f, "{a:?}"),
            Expr::Ident(i) => i.fmt_with_env(env, f),
            Expr::Call {
                f: g,
                a,
                possible_functions: TaggedFn::Untagged(id),
            } => write!(f, "{id}({},{})", Dis(a, env), Dis(g, env)),
            Expr::Call {
                f: g,
                a,
                possible_functions: TaggedFn::Tagged(possible_functions),
            } => write!(
                f,
                "({}$$unexpected())",
                possible_functions.iter().enumerate().format_with(
                    "",
                    |(i, lambda_id), f| f(&format_args!(
                        "{0}.tag==={i}?{lambda_id}({1},{0}.value):",
                        Dis(g, env),
                        Dis(a, env),
                    ))
                ),
            ),
            Expr::BasicCall { args, id } => {
                use crate::ast_step3::BasicFunction::*;
                match id {
                    Intrinsic(id) => write!(
                        f,
                        "$intrinsic${id}({})",
                        args.iter().format_with(",", |a, f| f(&format_args!(
                            "{}",
                            Dis(a, env)
                        )))
                    ),
                    Construction(id) => {
                        write!(
                            f,
                            "{}({})",
                            Dis(id, env),
                            args.iter()
                                .format_with(",", |a, f| f(&Dis(a, env)))
                        )
                    }
                    FieldAccessor {
                        constructor: _,
                        field,
                    } => {
                        debug_assert_eq!(args.len(), 1);
                        write!(
                            f,
                            "$field_accessor({field},{})",
                            Dis(&args[0], env)
                        )
                    }
                }
            }
            Expr::Upcast { tag, value } => {
                write!(f, "{{tag:{tag},value:{}}}", Dis(value, env))
            }
            Expr::Downcast { tag, value } => {
                write!(
                    f,
                    "({0}.tag==={tag}?{0}.value:$$unexpected())",
                    Dis(value, env)
                )
            }
            Expr::Ref(v) => write!(f, "{{ref:{}}}", Dis(v, env)),
            Expr::Deref(v) => write!(f, "{}.ref", Dis(v, env)),
        }
    }
}

impl DisplayWithEnv for VariableId {
    fn fmt_with_env(
        &self,
        env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            VariableId::Global(d) => {
                write!(f, "${d}${}()", convert_name(&env.variable_names[self]))
            }
            VariableId::Local(d) => {
                if let Some(d) = env.context.get(d) {
                    write!(f, "ctx._{d}")
                } else {
                    write!(f, "${d}$")
                }
            }
        }
    }
}

impl DisplayWithEnv for ConstructorId {
    fn fmt_with_env(
        &self,
        _env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            ConstructorId::DeclId(d) => write!(f, "c{d}"),
            ConstructorId::Intrinsic(d) => write!(f, "c{d}"),
        }
    }
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
