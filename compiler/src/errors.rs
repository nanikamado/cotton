use crate::ast_step1::name_id::Path;
use crate::ast_step2::imports::Imports;
use crate::ast_step2::types::Type;
use crate::PrintTypeOfLocalVariableForUser;
use ariadne::{Label, Report, ReportKind, Source};
use colored::{ColoredString, Colorize};
use itertools::Itertools;
use parser::Span;
use std::fmt::Display;
use std::io::Write;

#[derive(Debug, PartialEq, Eq)]
pub enum CompileError {
    NoSuitableVariable {
        reason: Vec<CompileError>,
        span: Span,
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
    RecursionLimit,
    InaccessibleName {
        path: Path,
        span: Span,
    },
    NotFound {
        path: Path,
        span: Span,
    },
    NoOpPrecedenceDecl {
        path: Path,
        span: Span,
    },
    TooManySuper {
        span: Span,
    },
}

impl CompileError {
    pub fn write<W: Write>(
        self,
        src: &str,
        w: &mut W,
        filename: &str,
        imports: &Imports,
    ) -> std::io::Result<()> {
        match self {
            CompileError::NoSuitableVariable { reason, span } => {
                if reason.is_empty() {
                    let report =
                        Report::build(ReportKind::Error, filename, span.start)
                            .with_label(
                                Label::new((filename, span)).with_message(
                                    "cannot find this variable in this scope"
                                        .to_string(),
                                ),
                            );
                    report.finish().write((filename, Source::from(src)), w)?;
                    Ok(())
                } else if reason.len() == 1 {
                    reason
                        .into_iter()
                        .next()
                        .unwrap()
                        .write(src, w, filename, imports)
                } else {
                    let m = "cannot find suitable definition for this variable"
                        .to_string();
                    let report =
                        Report::build(ReportKind::Error, filename, span.start)
                            .with_label(
                                Label::new((filename, span)).with_message(m),
                            );
                    report
                        .finish()
                        .write((filename, Source::from(src)), &mut *w)?;
                    writeln!(
                        w,
                        "There are {} candidates but no one could be used because:",
                        reason.len(),
                    )?;
                    for r in reason {
                        r.write(src, w, filename, imports)?;
                    }
                    Ok(())
                }
            }
            CompileError::NotFound { path, span } => {
                let report =
                    Report::build(ReportKind::Error, filename, span.start)
                        .with_label(
                            Label::new((filename, span)).with_message(format!(
                                "cannot find `{path:?}`"
                            )),
                        )
                        .with_message("not found in this scope");
                report.finish().write((filename, Source::from(src)), w)?;
                Ok(())
            }
            CompileError::NoOpPrecedenceDecl { path, span } => {
                let report =
                    Report::build(ReportKind::Error, filename, span.start)
                        .with_label(Label::new((filename, span)).with_message(
                            format!(
                    "precedence declaration for operator `{path:?}` not found"
                ),
                        ))
                        .with_message("no precedence declaration");
                report.finish().write((filename, Source::from(src)), w)?;
                Ok(())
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
                                    Could not decide which one to use.",
                            satisfied.len(),
                            satisfied.iter().map(|(t, _)| t).format_with(
                                "",
                                |t, f| f(&format_args!(
                                    "{}\n",
                                    print_type(t, imports)
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
                                print_type(&super_type, imports),
                                print_type(&sub_type, imports),
                            ),
                        ))
                        .with_message(NotSubtypeReasonDisplay {
                            reason: &reason,
                            depth: 0,
                            imports,
                        });
                report.finish().write((filename, Source::from(src)), w)?;
                Ok(())
            }
            CompileError::RecursionLimit => {
                writeln!(w, "recursion of implicit variable reached the limit.")
            }
            CompileError::InaccessibleName { path, span } => {
                let report =
                    Report::build(ReportKind::Error, filename, span.start)
                        .with_label(
                            Label::new((filename, span))
                                .with_message(format!("`{path:?}` is private")),
                        )
                        .with_message(format!(
                    "`{path:?}` exists but is inaccessible from outside."
                ));
                report.finish().write((filename, Source::from(src)), w)?;
                Ok(())
            }
            CompileError::TooManySuper { span } => {
                let report =
                    Report::build(ReportKind::Error, filename, span.start)
                        .with_label(
                            Label::new((filename, span)).with_message(
                                "there are too many super keywords",
                            ),
                        );
                report.finish().write((filename, Source::from(src)), w)?;
                Ok(())
            }
        }
    }
}

fn print_type(t: &Type, imports: &Imports) -> ColoredString {
    PrintTypeOfLocalVariableForUser {
        t,
        imports,
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
    imports: &'a Imports,
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
                    print_type(left, self.imports),
                    print_type(right, self.imports)
                )?;
                fmt_reasons(reasons, f, self.depth, self.imports)
            }
            NotSubtypeReason::Disjoint {
                left,
                right,
                reasons,
            } => {
                write!(
                    f,
                    "`{}` and `{}` are disjoint",
                    print_type(left, self.imports),
                    print_type(right, self.imports)
                )?;
                fmt_reasons(reasons, f, self.depth, self.imports)
            }
            NotSubtypeReason::LoopLimit { left, right } => {
                write!(
                    f,
                    "could not verify `{}` is subtype of `{}` \
                    because of the loop count limit.",
                    print_type(left, self.imports),
                    print_type(right, self.imports)
                )
            }
        }
    }
}

fn fmt_reasons(
    reasons: &[NotSubtypeReason],
    f: &mut std::fmt::Formatter<'_>,
    depth: usize,
    imports: &Imports,
) -> std::fmt::Result {
    match reasons.len() {
        0 => Ok(()),
        1 => write!(
            f,
            "\n{}* because {}",
            "│".repeat(depth),
            NotSubtypeReasonDisplay {
                reason: &reasons[0],
                depth,
                imports
            }
        ),
        _ => write!(
            f,
            "\n│{0} because\n{0}├╮\n│{0}* {1}{2}\n{0}* and {3}",
            "│".repeat(depth),
            NotSubtypeReasonDisplay {
                reason: &reasons[0],
                depth: depth + 1,
                imports
            },
            reasons[1..reasons.len() - 1]
                .iter()
                .format_with("", |r, f| f(&format_args!(
                    "\n{}├╮\n{}* {}",
                    "│".repeat(depth),
                    "│".repeat(depth + 1),
                    NotSubtypeReasonDisplay {
                        reason: r,
                        depth: depth + 1,
                        imports
                    }
                ))),
            NotSubtypeReasonDisplay {
                reason: reasons.last().unwrap(),
                depth,
                imports
            },
        ),
    }
}
