use crate::{
    ast_step2::{name_id::Name, types::Type},
    OpPrecedenceMap, PrintTypeOfLocalVariableForUser,
};
use ariadne::{Label, Report, ReportKind, Source};
use colored::{ColoredString, Colorize};
use itertools::Itertools;
use parser::Span;
use std::{fmt::Display, io::Write};

#[derive(Debug, PartialEq, Eq)]
pub enum CompileError {
    NoSuitableVariable {
        name: Name,
        reason: Vec<CompileError>,
    },
    ManyCandidates {
        satisfied: Vec<String>,
    },
    NotSubtypeOf {
        sub_type: Type,
        super_type: Type,
        reason: NotSubtypeReason,
        span: Span,
    },
    InexhaustiveMatch {
        description: String,
    },
}

impl CompileError {
    pub fn write<W: Write>(
        &self,
        src: &str,
        w: &mut W,
        filename: &str,
        op_precedence_map: &OpPrecedenceMap,
    ) -> std::io::Result<()> {
        match self {
            CompileError::NoSuitableVariable { name, reason } => {
                if reason.is_empty() {
                    write!(w, "{} not found", name)
                } else if reason.len() == 1 {
                    reason[0].write(src, w, filename, op_precedence_map)
                } else {
                    writeln!(
                        w,
                        "Can not find suitable variable for {}. \
                        There are {} candidates \
                        but no one could be used because:",
                        name,
                        reason.len(),
                    )?;
                    for r in reason {
                        r.write(src, w, filename, op_precedence_map)?;
                    }
                    Ok(())
                }
            }
            CompileError::ManyCandidates { satisfied } => write!(
                w,
                "There are {} candidates for one requirement: {}.\
                Can not dicide which one to use.",
                satisfied.len(),
                satisfied.iter().format(", "),
            ),
            CompileError::NotSubtypeOf {
                sub_type,
                super_type,
                reason,
                span,
            } => {
                let report =
                    Report::build(ReportKind::Error, filename, span.start)
                        .with_label(
                            Label::new((filename, span.clone())).with_message(
                                format!(
                                    "expected `{}` but found `{}`.",
                                    print_type(super_type, op_precedence_map),
                                    print_type(sub_type, op_precedence_map),
                                ),
                            ),
                        )
                        .with_message(NotSubtypeReasonDisplay {
                            reason,
                            depth: 0,
                            op_precedence_map,
                        });
                report.finish().write((filename, Source::from(src)), w)?;
                Ok(())
            }
            CompileError::InexhaustiveMatch { description } => {
                write!(w, "{}", description)
            }
        }
    }
}

fn print_type(t: &Type, op_precedence_map: &OpPrecedenceMap) -> ColoredString {
    PrintTypeOfLocalVariableForUser {
        t,
        op_precedence_map,
        type_variable_decls: &Default::default(),
    }
    .to_string()
    .bold()
}

#[derive(Debug, PartialEq, Eq)]
pub enum NotSubtypeReason {
    NotSubtype {
        left: Type,
        right: Type,
        reasons: Vec<NotSubtypeReason>,
    },
    NoIntersection {
        left: Type,
        right: Type,
        reasons: Vec<NotSubtypeReason>,
    },
}

struct NotSubtypeReasonDisplay<'a> {
    reason: &'a NotSubtypeReason,
    depth: usize,
    op_precedence_map: &'a OpPrecedenceMap<'a>,
}

impl Display for NotSubtypeReasonDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.reason {
            NotSubtypeReason::NotSubtype {
                left,
                right,
                reasons,
            } => {
                write!(
                    f,
                    "`{}` is not subtype of `{}`",
                    print_type(left, self.op_precedence_map),
                    print_type(right, self.op_precedence_map)
                )?;
                fmt_reasons(reasons, f, self.depth, self.op_precedence_map)
            }
            NotSubtypeReason::NoIntersection {
                left,
                right,
                reasons,
            } => {
                write!(
                    f,
                    "`{}` and `{}` are disjoint",
                    print_type(left, self.op_precedence_map),
                    print_type(right, self.op_precedence_map)
                )?;
                fmt_reasons(reasons, f, self.depth, self.op_precedence_map)
            }
        }
    }
}

fn fmt_reasons(
    reasons: &[NotSubtypeReason],
    f: &mut std::fmt::Formatter<'_>,
    depth: usize,
    op_precedence_map: &OpPrecedenceMap,
) -> std::fmt::Result {
    match reasons.len() {
        0 => Ok(()),
        1 => write!(
            f,
            "\n{}because {}",
            " ".repeat(depth * 4),
            NotSubtypeReasonDisplay {
                reason: &reasons[0],
                depth,
                op_precedence_map
            }
        ),
        _ => write!(
            f,
            "\n{}because\n{}\n{}and {}",
            " ".repeat(depth * 4),
            reasons[0..reasons.len() - 1]
                .iter()
                .format_with("\n", |r, f| f(&format_args!(
                    "{}{},",
                    " ".repeat((depth + 1) * 4),
                    NotSubtypeReasonDisplay {
                        reason: r,
                        depth: depth + 2,
                        op_precedence_map
                    }
                ))),
            " ".repeat((depth + 1) * 4),
            NotSubtypeReasonDisplay {
                reason: reasons.last().unwrap(),
                depth: depth + 2,
                op_precedence_map
            }
        ),
    }
}
