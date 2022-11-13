use crate::ast_step2::{name_id::Name, types::Type};
use ariadne::{Label, Report, ReportKind, Source};
use colored::Colorize;
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
    ) -> std::io::Result<()> {
        match self {
            CompileError::NoSuitableVariable { name, reason } => {
                if reason.is_empty() {
                    write!(w, "{} not found", name)
                } else if reason.len() == 1 {
                    reason[0].write(src, w, filename)
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
                        r.write(src, w, filename)?;
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
                                    super_type.to_string().bold(),
                                    sub_type.to_string().bold(),
                                ),
                            ),
                        )
                        .with_message(reason);
                report.finish().write((filename, Source::from(src)), w)?;
                Ok(())
            }
            CompileError::InexhaustiveMatch { description } => {
                write!(w, "{}", description)
            }
        }
    }
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

impl Display for NotSubtypeReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            NotSubtypeReasonDisplay {
                reason: self,
                depth: 0
            }
        )
    }
}

struct NotSubtypeReasonDisplay<'a> {
    reason: &'a NotSubtypeReason,
    depth: usize,
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
                    left.to_string().bold(),
                    right.to_string().bold()
                )?;
                fmt_reasons(reasons, f, self.depth)
            }
            NotSubtypeReason::NoIntersection {
                left,
                right,
                reasons,
            } => {
                write!(
                    f,
                    "`{}` and `{}` are disjoint",
                    left.to_string().bold(),
                    right.to_string().bold()
                )?;
                fmt_reasons(reasons, f, self.depth)
            }
        }
    }
}

fn fmt_reasons(
    reasons: &[NotSubtypeReason],
    f: &mut std::fmt::Formatter<'_>,
    depth: usize,
) -> std::fmt::Result {
    match reasons.len() {
        0 => Ok(()),
        1 => write!(
            f,
            "\n{}because {}",
            " ".repeat(depth * 4),
            NotSubtypeReasonDisplay {
                reason: &reasons[0],
                depth
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
                        depth: depth + 2
                    }
                ))),
            " ".repeat((depth + 1) * 4),
            NotSubtypeReasonDisplay {
                reason: reasons.last().unwrap(),
                depth: depth + 2
            }
        ),
    }
}
