use super::{
    collect_tuple_rev,
    types::{Type, TypeUnit, TypeVariable},
    TypeId,
};
use crate::{
    ast_step1::name_id::Name, ast_step3::GlobalVariableType, OpPrecedenceMap,
};
use fxhash::FxHashMap;
use itertools::Itertools;
use std::fmt::Display;

pub struct PrintTypeOfGlobalVariableForUser<'a> {
    pub t: &'a GlobalVariableType,
    pub op_precedence_map: &'a OpPrecedenceMap<'a>,
}

pub struct PrintTypeOfLocalVariableForUser<'a> {
    pub t: &'a Type,
    pub op_precedence_map: &'a OpPrecedenceMap<'a>,
    pub type_variable_decls: &'a FxHashMap<TypeUnit, Name>,
}

impl Display for PrintTypeOfGlobalVariableForUser<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            fmt_type_with_env(
                &self.t.t,
                self.op_precedence_map,
                &Default::default()
            )
            .0
        )?;
        Ok(())
    }
}

impl Display for PrintTypeOfLocalVariableForUser<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            fmt_type_with_env(
                self.t,
                self.op_precedence_map,
                self.type_variable_decls
            )
            .0
        )?;
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq)]
enum OperatorContext {
    Single,
    Fn,
    Or,
    OtherOperator,
}

fn fmt_type_with_env(
    t: &Type,
    op_precedence_map: &OpPrecedenceMap,
    type_variable_decls: &FxHashMap<TypeUnit, Name>,
) -> (String, OperatorContext) {
    if t.is_empty() {
        ("∅".to_string(), OperatorContext::Single)
    } else if t.len() == 1 {
        fmt_type_unit_with_env(
            t.iter().next().unwrap(),
            op_precedence_map,
            type_variable_decls,
        )
    } else {
        (
            t.iter()
                .format_with(" | ", |t, f| {
                    let (t, t_context) = fmt_type_unit_with_env(
                        t,
                        op_precedence_map,
                        type_variable_decls,
                    );
                    let s = match t_context {
                        OperatorContext::Single | OperatorContext::Or => t,
                        _ => format!("({})", t),
                    };
                    f(&s)
                })
                .to_string(),
            OperatorContext::Or,
        )
    }
}

fn fmt_type_unit_with_env(
    t: &TypeUnit,
    op_precedence_map: &OpPrecedenceMap,
    type_variable_decls: &FxHashMap<TypeUnit, Name>,
) -> (String, OperatorContext) {
    use OperatorContext::*;
    if let Some(s) = type_variable_decls.get(t) {
        return (s.to_string(), Single);
    }
    match t {
        TypeUnit::Fn(a, b) => {
            let (b, b_context) =
                fmt_type_with_env(b, op_precedence_map, type_variable_decls);
            let (a, a_context) =
                fmt_type_with_env(a, op_precedence_map, type_variable_decls);
            let s = match (a_context, b_context) {
                (Single, Single | Fn) => format!("{} -> {}", a, b),
                (Single, _) => format!("{} -> ({})", a, b),
                (_, Single | Fn) => format!("({}) -> {}", a, b),
                _ => format!("({}) -> ({})", a, b),
            };
            (s, Fn)
        }
        TypeUnit::Variable(TypeVariable::Normal(_)) => {
            ("_".to_string(), Single)
        }
        TypeUnit::Variable(d) => (d.to_string(), Single),
        TypeUnit::RecursiveAlias { body } => (
            format!(
                "rec[{}]",
                fmt_type_with_env(body, op_precedence_map, type_variable_decls)
                    .0
            ),
            Single,
        ),
        TypeUnit::Const { id } => (format!(":{}", id), Single),
        TypeUnit::Tuple(hs, ts) => {
            let ts = collect_tuple_rev(ts);
            let hts = hs
                .iter()
                .flat_map(|h| ts.iter().map(move |t| (h, t)))
                .collect_vec();
            if hts.len() == 1 {
                let (h, tuple_rev) = hts[0];
                if let TypeUnit::Const { id } = &**h {
                    fmt_tuple(
                        *id,
                        tuple_rev,
                        op_precedence_map,
                        type_variable_decls,
                    )
                } else {
                    (
                        fmt_tuple_as_tuple(
                            h,
                            tuple_rev,
                            op_precedence_map,
                            type_variable_decls,
                        ),
                        OperatorContext::Single,
                    )
                }
            } else {
                let t = format!(
                    "{}",
                    hts.iter().format_with(" | ", |(h, t), f| {
                        if let TypeUnit::Const { id } = &***h {
                            let (t, t_context) = fmt_tuple(
                                *id,
                                t,
                                op_precedence_map,
                                type_variable_decls,
                            );
                            match t_context {
                                Single | Or => f(&t),
                                _ => f(&format_args!("({})", t)),
                            }
                        } else {
                            f(&fmt_tuple_as_tuple(
                                h,
                                t,
                                op_precedence_map,
                                type_variable_decls,
                            ))
                        }
                    })
                );
                (t, Or)
            }
        }
        TypeUnit::TypeLevelFn(f) => (
            format!(
                "fn[{}]",
                fmt_type_with_env(f, op_precedence_map, type_variable_decls).0
            ),
            Single,
        ),
        TypeUnit::TypeLevelApply { f, a } => {
            let (f, f_context) =
                fmt_type_with_env(f, op_precedence_map, type_variable_decls);
            let (a, _) =
                fmt_type_with_env(a, op_precedence_map, type_variable_decls);
            let s = if f_context == Single {
                format!("{}[{}]", f, a)
            } else {
                format!("({})[{}]", f, a)
            };
            (s, Single)
        }
        TypeUnit::Restrictions {
            t,
            variable_requirements,
            subtype_relations,
        } => (
            format!(
                "{} where {{{subtype_relations}, {}}}",
                t,
                variable_requirements.iter().format_with(
                    ",\n",
                    |(name, t), f| f(&format_args!("?{} : {}", name, t))
                )
            ),
            OtherOperator,
        ),
    }
}

fn fmt_tuple(
    head: TypeId,
    tuple_rev: &[&Type],
    op_precedence_map: &OpPrecedenceMap,
    type_variable_decls: &FxHashMap<TypeUnit, Name>,
) -> (String, OperatorContext) {
    use OperatorContext::*;
    if tuple_rev.is_empty() {
        (head.to_string(), Single)
    } else if tuple_rev.len() == 1 {
        (
            format!(
                "{}[{}]",
                head,
                fmt_type_with_env(
                    tuple_rev[0],
                    op_precedence_map,
                    type_variable_decls
                )
                .0
            ),
            Single,
        )
    } else if op_precedence_map.get(head.to_string().as_str()).is_some() {
        debug_assert_eq!(tuple_rev.len(), 2);
        (
            tuple_rev
                .iter()
                .rev()
                .map(|t| {
                    let (t, t_context) = fmt_type_with_env(
                        t,
                        op_precedence_map,
                        type_variable_decls,
                    );
                    match t_context {
                        Single => t,
                        _ => format!("({})", t),
                    }
                })
                .format(&format!(" {} ", head))
                .to_string(),
            OtherOperator,
        )
    } else {
        (
            format!(
                "{}[{}]",
                head,
                tuple_rev.iter().rev().format_with(", ", |t, f| {
                    let (t, t_context) = fmt_type_with_env(
                        t,
                        op_precedence_map,
                        type_variable_decls,
                    );
                    let s = match t_context {
                        Single => t,
                        _ => format!("({})", t),
                    };
                    f(&s)
                })
            ),
            Single,
        )
    }
}

fn fmt_tuple_as_tuple(
    head: &TypeUnit,
    tuple_rev: &[&Type],
    op_precedence_map: &OpPrecedenceMap,
    type_variable_decls: &FxHashMap<TypeUnit, Name>,
) -> String {
    format!(
        "({}{})",
        fmt_type_unit_with_env(head, op_precedence_map, type_variable_decls).0,
        tuple_rev
            .iter()
            .rev()
            .format_with("", |t, f| f(&format_args!(
                ", {}",
                fmt_type_with_env(t, op_precedence_map, type_variable_decls).0
            )))
    )
}
