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
        satisfied: Vec<(Type, String)>,
        span: Span,
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
    RecursionLimit,
    InaccessibleName {
        path: Name,
        span: Span,
    },
}

impl CompileError {
    pub fn write<W: Write>(
        self,
        src: &str,
        w: &mut W,
        filename: &str,
        op_precedence_map: &OpPrecedenceMap,
    ) -> std::io::Result<()> {
        match self {
            CompileError::NoSuitableVariable { name, reason } => {
                if reason.is_empty() {
                    writeln!(w, "{} not found", name)
                } else if reason.len() == 1 {
                    reason.into_iter().next().unwrap().write(
                        src,
                        w,
                        filename,
                        op_precedence_map,
                    )
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
            CompileError::ManyCandidates { satisfied, span } => {
                log::debug!(
                    "satisfied: {}",
                    satisfied.iter().map(|(_, s)| s).format(", ")
                );
                let report =
                    Report::build(ReportKind::Error, filename, span.start)
                        .with_label(Label::new((filename, span)).with_message(
                            format!(
                            "There are {} candidates for this variable.\n{}\
                                    Could not dicide which one to use.",
                            satisfied.len(),
                            satisfied.iter().map(|(t, _)| t).format_with(
                                "",
                                |t, f| f(&format_args!(
                                    "{}\n",
                                    print_type(t, op_precedence_map)
                                ))
                            )
                        ),
                        ));
                report.finish().write((filename, Source::from(src)), w)
            }
            CompileError::NotSubtypeOf {
                sub_type,
                super_type,
                reason,
                span,
            } => {
                log::debug!("{} is not subtype of {}", sub_type, super_type);
                let report =
                    Report::build(ReportKind::Error, filename, span.start)
                        .with_label(Label::new((filename, span)).with_message(
                            format!(
                                "expected `{}` but found `{}`.",
                                print_type(&super_type, op_precedence_map),
                                print_type(&sub_type, op_precedence_map),
                            ),
                        ))
                        .with_message(NotSubtypeReasonDisplay {
                            reason: &reason,
                            depth: 0,
                            op_precedence_map,
                        });
                report.finish().write((filename, Source::from(src)), w)?;
                Ok(())
            }
            CompileError::InexhaustiveMatch { description } => {
                writeln!(w, "{}", description)
            }
            CompileError::RecursionLimit => {
                writeln!(w, "recursion of implicit variable reaced the limit.")
            }
            CompileError::InaccessibleName { path, span } => {
                let report =
                    Report::build(ReportKind::Error, filename, span.start)
                        .with_label(
                            Label::new((filename, span)).with_message(format!(
                                "`{:?}` is private",
                                path
                            )),
                        )
                        .with_message(format!(
                            "`{:?}` exists but is inaccessible from outside.",
                            path
                        ));
                report.finish().write((filename, Source::from(src)), w)?;
                Ok(())
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum NotSubtypeReason {
    NotSubtype {
        left: Type,
        right: Type,
        reasons: Vec<NotSubtypeReason>,
    },
    Disjoint {
        left: Type,
        right: Type,
        reasons: Vec<NotSubtypeReason>,
    },
    LoopLimit {
        left: Type,
        right: Type,
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
            NotSubtypeReason::Disjoint {
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
            NotSubtypeReason::LoopLimit { left, right } => {
                write!(
                    f,
                    "could not verify `{}` is subtype of `{}` \
                    because of the loop count limit.",
                    print_type(left, self.op_precedence_map),
                    print_type(right, self.op_precedence_map)
                )
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
