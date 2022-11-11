use crate::ast_step2::{name_id::Name, types::Type};
use itertools::Itertools;
use std::fmt::Display;

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
    },
    InexhaustiveMatch {
        description: String,
    },
}

impl Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::NoSuitableVariable { name, reason } => {
                if reason.is_empty() {
                    write!(f, "{} not found", name)
                } else if reason.len() == 1 {
                    write!(f, "{}", reason[0])
                } else {
                    write!(
                        f,
                        "Can not find suitable variable for {}. \
                        There are {} candidates \
                        but no one could be used because:\n{}",
                        name,
                        reason.len(),
                        reason.iter().format("\n")
                    )
                }
            }
            CompileError::ManyCandidates { satisfied } => write!(
                f,
                "There are {} candidates for one requirement: {}.\
                Can not dicide which one to use.",
                satisfied.len(),
                satisfied.iter().format(", "),
            ),
            CompileError::NotSubtypeOf {
                sub_type,
                super_type,
                reason,
            } => {
                write!(
                    f,
                    "expected `{}` but found `{}`. {}",
                    super_type, sub_type, reason,
                )
            }
            CompileError::InexhaustiveMatch { description } => {
                write!(f, "{}", description)
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
                write!(f, "`{left}` is not subtype of `{right}`",)?;
                fmt_reasons(reasons, f, self.depth)
            }
            NotSubtypeReason::NoIntersection {
                left,
                right,
                reasons,
            } => {
                write!(f, "`{left}` and `{right}` are disjoint",)?;
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
