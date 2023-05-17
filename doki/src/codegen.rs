mod c_type;
mod collector;

use self::c_type::{CAggregateType, CType};
use crate::ast_step1::{ConstructorId, ConstructorNames, TypeId};
use crate::ast_step2::{
    self, Ast, Block, Expr, Function, GlobalVariableId, Instruction,
    LocalVariable, LocalVariableCollector, Tester, Type, TypeUnit,
    VariableDecl, VariableId,
};
use crate::intrinsics::{IntrinsicType, IntrinsicVariable};
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
        reffed_aggregates: Default::default(),
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
        constructor_names: &ast.constructor_names,
    };
    let mut s = String::new();
    let unit_t: Type = TypeUnit::Normal {
        id: TypeId::Intrinsic(IntrinsicType::Unit),
        args: Vec::new(),
    }
    .into();
    write!(
        &mut s,
        "{0} __unit(){{
            return ({0}){{}};
        }}
        {1}{2}{3}",
        c_type_env.c_type(&unit_t, None),
        r#"
        |int __unexpected(){
        |    puts("unexpected");
        |    exit(1);
        |}
        |"#
        .strip_margin(),
        IntrinsicVariable::iter()
            .map(|v| format!(
                "{} intrinsic_{v}({}){}",
                primitive_ret_type(v, &mut c_type_env),
                primitive_arg_types(v, &mut c_type_env)
                    .iter()
                    .enumerate()
                    .format_with(", ", |(i, t), f| f(&format_args!(
                        "{t} _{i}"
                    ))),
                primitive_def(v)
            ))
            .format(""),
        ast.variable_decls
            .iter()
            .format_with("", |d, f| f(&format_args!(
                "{} g_{}_{}(){}",
                env.global_variable_types[&d.decl_id],
                d.decl_id,
                convert_name(
                    &env.variable_names[&VariableId::Global(d.decl_id)]
                ),
                Dis(&TerminalBlock(&d.value, d.ret), &env)
            ))),
    )
    .unwrap();
    write_fns(&mut s, &ast.functions, &mut c_type_env, &env, true);
    let mut fn_headers = String::new();
    write_fns(
        &mut fn_headers,
        &ast.functions,
        &mut c_type_env,
        &env,
        false,
    );
    write!(
        &mut s,
        "int main() {{
            {}((struct t0){{}},(struct t0){{}});
        }}",
        ast.entry_point
    )
    .unwrap();
    let mut s2 = String::new();
    let aggregates: FxHashMap<_, _> = c_type_env
        .aggregate_types
        .into_raw()
        .into_iter()
        .map(|(a, b)| (b, a))
        .collect();
    let sorted = sort_aggregates(&aggregates);
    write!(
        &mut s2,
        "
        #include <stdio.h>
        #include <stdlib.h>
        #include <string.h>
        {}{}{fn_headers}{}{s}",
        sorted.iter().format_with("", |(i, t), f| {
            match t {
                CAggregateType::Struct(fields) => f(&format_args!(
                    "{} {{{}}};\n",
                    CType::Aggregate(*i),
                    fields
                        .iter()
                        .enumerate()
                        .format_with("", |(i, field), f| f(&format_args!(
                            "{field} _{i};",
                        )))
                )),
                CAggregateType::Union(ts) => f(&format_args!(
                    "union u{i} {{{}}};
                        {} {{int tag;union u{i} value;}};",
                    ts.iter().enumerate().format_with("", |(i, t), f| f(
                        &format_args!("{t} _{i};")
                    )),
                    CType::Aggregate(*i),
                )),
            }
        }),
        c_type_env.reffed_aggregates.iter().format_with("", |i, f| {
            let t = CType::Aggregate(*i);
            f(&format_args!(
                "{t}* ref_t{i}({t} a) {{
                    {t}* tmp = malloc(sizeof({t}));
                    *tmp = a;
                    return tmp;
                }}"
            ))
        }),
        ast.variable_decls
            .iter()
            .format_with("", |d, f| f(&format_args!(
                "{} g_{}_{}();",
                env.global_variable_types[&d.decl_id],
                d.decl_id,
                convert_name(
                    &env.variable_names[&VariableId::Global(d.decl_id)]
                ),
            )))
    )
    .unwrap();
    s2
}

fn primitive_def(i: IntrinsicVariable) -> &'static str {
    match i {
        IntrinsicVariable::Minus => "{return _0 - _1;}",
        IntrinsicVariable::Plus => "{return _0 + _1;}",
        IntrinsicVariable::Percent => "{return _0 % _1;}",
        IntrinsicVariable::Multi => "{return _0 * _1;}",
        IntrinsicVariable::Div => "{return _0 / _1;}",
        IntrinsicVariable::Lt => "{return _0 < _1;}",
        IntrinsicVariable::Eq => "{return _0 == _1;}",
        IntrinsicVariable::PrintStr => r#"{printf("%s", _0);return __unit();}"#,
        IntrinsicVariable::I64ToString => {
            r#"{
                int l = snprintf(NULL, 0, "%d", _0) + 1;
                char* s = malloc(l);
                snprintf(s, l, "%d", _0);
                return s;
            }"#
        }
        IntrinsicVariable::AppendStr => {
            r#"{
                int l = strlen(_0) + strlen(_1);
                char* s = malloc(sizeof(char) * (l + 1));
                sprintf(s, "%s%s", _0, _1);
                return s;
            }"#
        }
    }
}

fn primitive_arg_types(
    i: IntrinsicVariable,
    env: &mut c_type::Env,
) -> Vec<CType> {
    i.runtime_arg_type()
        .into_iter()
        .map(|t| env.c_type(&t, None))
        .collect()
}

fn primitive_ret_type(i: IntrinsicVariable, env: &mut c_type::Env) -> CType {
    let t = TypeUnit::Normal {
        id: TypeId::Intrinsic(i.runtime_return_type()),
        args: Vec::new(),
    }
    .into();
    env.c_type(&t, None)
}

fn sort_aggregates(
    aggregates: &FxHashMap<usize, CAggregateType>,
) -> Vec<(usize, &CAggregateType)> {
    let mut done = FxHashSet::default();
    let mut sorted = Vec::with_capacity(aggregates.len());
    for i in aggregates.keys() {
        sort_aggregates_rec(*i, aggregates, &mut done, &mut sorted);
    }
    sorted
}
fn sort_aggregates_rec<'a>(
    i: usize,
    h: &'a FxHashMap<usize, CAggregateType>,
    done: &mut FxHashSet<usize>,
    sorted: &mut Vec<(usize, &'a CAggregateType)>,
) {
    if !done.contains(&i) {
        let a = &h[&i];
        done.insert(i);
        let cs = match a {
            CAggregateType::Union(cs) => cs,
            CAggregateType::Struct(cs) => cs,
        };
        for c in cs {
            if let CType::Aggregate(i) = c {
                sort_aggregates_rec(*i, h, done, sorted);
            }
        }
        sorted.push((i, a));
    }
}

fn write_fns(
    s: &mut String,
    functions: &[Function],
    c_type_env: &mut c_type::Env,
    env: &Env,
    write_body: bool,
) {
    write!(
        s,
        "{}",
        functions.iter().format_with("", |function, f| {
            let env = Env {
                context: &function
                    .context
                    .iter()
                    .enumerate()
                    .map(|(i, d)| (*d, i))
                    .collect(),
                variable_names: env.variable_names,
                local_variable_types: env.local_variable_types,
                global_variable_types: env.global_variable_types,
                constructor_names: env.constructor_names,
            };
            let (t, ct) = env.local_variable_types.get_type(function.parameter);
            f(&format_args!(
                "{} {}({} {}/*{}*/,{} ctx)",
                env.get_type(function.ret),
                function.id,
                ct,
                Dis(&VariableId::Local(function.parameter), &env),
                ast_step2::DisplayTypeWithEnv(t, env.constructor_names),
                CType::Aggregate(
                    c_type_env.aggregate_types.get(CAggregateType::Struct(
                        function
                            .context
                            .iter()
                            .map(|l| env
                                .local_variable_types
                                .get_type(*l)
                                .1
                                .clone())
                            .collect()
                    ))
                )
            ))?;
            if write_body {
                f(&format_args!(
                    "{};",
                    Dis(&TerminalBlock(&function.body, function.ret), &env)
                ))
            } else {
                f(&";")
            }
        })
    )
    .unwrap()
}

#[derive(Debug)]
struct Env<'a> {
    context: &'a FxHashMap<LocalVariable, usize>,
    variable_names: &'a FxHashMap<VariableId, String>,
    local_variable_types: &'a LocalVariableCollector<(Type, CType)>,
    global_variable_types: &'a FxHashMap<GlobalVariableId, CType>,
    constructor_names: &'a ConstructorNames,
}

impl Env<'_> {
    fn get_type(&self, v: VariableId) -> &CType {
        match v {
            VariableId::Local(v) => &self.local_variable_types.get_type(v).1,
            VariableId::Global(v) => &self.global_variable_types[&v],
        }
    }
}

fn collect_local_variables_block(b: &Block, vs: &mut FxHashSet<LocalVariable>) {
    for i in &b.instructions {
        match i {
            Instruction::Assign(d, _) => {
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

impl DisplayWithEnv for VariableDecl {
    fn fmt_with_env(
        &self,
        env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let ct = &env.global_variable_types[&self.decl_id];
        write!(
            f,
            "{} {}/*{}*/=(()=>({{{}||__unexpected();{}}}))();",
            ct,
            Dis(&VariableId::Global(self.decl_id), env),
            ast_step2::DisplayTypeWithEnv(&self.t, env.constructor_names),
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
        if let VariableId::Local(l) = self.1 {
            vs.insert(l);
        }
        collect_local_variables_block(self.0, &mut vs);
        if vs.is_empty() {
            write!(
                f,
                "{{{}||__unexpected();return {};}}",
                Dis(self.0, env),
                Dis(&self.1, env)
            )
        } else {
            write!(
                f,
                "{{{}{}||__unexpected();return {};}}",
                vs.iter().format_with("", |v, f| {
                    let (t, ct) = env.local_variable_types.get_type(*v);
                    f(&format_args!(
                        "{} /*{}*/ {};",
                        ct,
                        ast_step2::DisplayTypeWithEnv(t, env.constructor_names),
                        Dis(&VariableId::Local(*v), env),
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
            write!(f, "1")
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
        write!(f, "{}.tag=={}", Dis(&self.1, env), self.0)
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
                let t = &env.local_variable_types.get_type(*d).1;
                write!(
                    f,
                    "({}={},1)",
                    Dis(&VariableId::Local(*d), env),
                    Dis(&(e, t), env)
                )
            }
            Instruction::Test(Tester::Tag { tag }, e) => {
                write!(f, "({})", Dis(&TagCheck(tag, *e), env))
            }
            Instruction::Test(Tester::I64 { value }, e) => {
                write!(f, "({}=={value})", Dis(e, env))
            }
            Instruction::Test(Tester::Str { value }, e) => {
                write!(f, "({}=={value:?})", Dis(e, env))
            }
            Instruction::FailTest => {
                write!(f, "0")
            }
            Instruction::ImpossibleTypeError => {
                write!(f, "__unexpected()")
            }
            Instruction::TryCatch(a, b) => {
                write!(f, "({}||{})", Dis(a, env), Dis(b, env))
            }
        }
    }
}

impl DisplayWithEnv for (&Expr, &CType) {
    fn fmt_with_env(
        &self,
        env: &Env<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let (e, t) = self;
        match e {
            Expr::Lambda {
                lambda_id: _,
                context,
            } => write!(
                f,
                r#"({}){{{}}}"#,
                t,
                context.iter().format_with(",", |c, f| f(&format_args!(
                    "{}",
                    Dis(&VariableId::Local(*c), env)
                )))
            ),
            Expr::I64(a) => write!(f, "{a}"),
            Expr::Str(a) => write!(f, "{a:?}"),
            Expr::Ident(i) => i.fmt_with_env(env, f),
            Expr::Call {
                f: g,
                a,
                real_function,
            } => write!(f, "{real_function}({},{})", Dis(a, env), Dis(g, env)),
            Expr::BasicCall { args, id } => {
                use crate::ast_step1::BasicFunction::*;
                match id {
                    Intrinsic(id) => write!(
                        f,
                        "intrinsic_{id}({})",
                        args.iter().format_with(",", |a, f| f(&format_args!(
                            "{}",
                            Dis(a, env)
                        )))
                    ),
                    Construction(id) => {
                        write!(
                            f,
                            "/*{}*/({}){{{}}}",
                            Dis(id, env),
                            t,
                            args.iter()
                                .format_with(",", |a, f| f(&Dis(a, env)))
                        )
                    }
                    IntrinsicConstruction(id) => {
                        write!(
                            f,
                            "/*{}*/({}){{{}}}",
                            id,
                            t,
                            args.iter()
                                .format_with(",", |a, f| f(&Dis(a, env)))
                        )
                    }
                    FieldAccessor {
                        constructor: _,
                        field,
                    } => {
                        debug_assert_eq!(args.len(), 1);
                        write!(f, "{}._{field}", Dis(&args[0], env))
                    }
                }
            }
            Expr::Upcast { tag, value } => {
                let i = if let CType::Aggregate(i) = t {
                    i
                } else {
                    panic!()
                };
                write!(f, "({t}){{{tag},(union u{i}){}}}", Dis(value, env))
            }
            Expr::Downcast { tag, value } => {
                write!(
                    f,
                    "({0}.tag=={tag}||__unexpected(),{0}.value._{tag})",
                    Dis(value, env)
                )
            }
            Expr::Ref(v) => {
                let t = if let CType::Ref(t) = t { t } else { panic!() };
                let i = if let CType::Aggregate(t) = **t {
                    t
                } else {
                    panic!()
                };
                write!(f, "ref_t{i}({})", Dis(v, env))
            }
            Expr::Deref(v) => write!(f, "*{}", Dis(v, env)),
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
                write!(f, "g_{d}_{}()", convert_name(&env.variable_names[self]))
            }
            VariableId::Local(d) => {
                if let Some(d) = env.context.get(d) {
                    write!(f, "ctx._{d}")
                } else {
                    write!(f, "l_{d}")
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
        write!(f, "{self}")
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
