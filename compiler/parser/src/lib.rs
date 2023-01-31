mod lex;
pub mod parse;
pub mod token_id;

pub use self::parse::*;
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
pub use lex::*;

pub fn parse(src: &str) -> Ast {
    let r = crate::lex::lex(src)
        .map_err(|s| {
            s.into_iter()
                .map(|s| s.map(|c| c.to_string()))
                .collect::<Vec<_>>()
        })
        .and_then(|(ts, src_len)| {
            parse_result(ts, src_len).map_err(|s| {
                s.into_iter()
                    .map(|s| s.map(|t| format!("{t:?}")))
                    .collect::<Vec<_>>()
            })
        });
    match r {
        Ok(ast) => ast,
        Err(es) => {
            for e in es {
                let e = e.map(|c| format!("{c:?}"));
                let report =
                    Report::build(ReportKind::Error, (), e.span().start);
                let report = match e.reason() {
                    chumsky::error::SimpleReason::Unclosed {
                        span,
                        delimiter,
                    } => report
                        .with_message(format!(
                            "Unclosed delimiter {}",
                            delimiter.fg(Color::Yellow)
                        ))
                        .with_label(
                            Label::new(span.clone())
                                .with_message(format!(
                                    "Unclosed delimiter {}",
                                    delimiter.fg(Color::Yellow)
                                ))
                                .with_color(Color::Yellow),
                        )
                        .with_label(
                            Label::new(e.span())
                                .with_message(format!(
                                    "Must be closed before this {}",
                                    e.found()
                                        .unwrap_or(&"end of file".to_string())
                                        .fg(Color::Red)
                                ))
                                .with_color(Color::Red),
                        ),
                    chumsky::error::SimpleReason::Unexpected => report
                        .with_message(format!(
                            "{}, expected {}",
                            if e.found().is_some() {
                                "Unexpected token in input"
                            } else {
                                "Unexpected end of input"
                            },
                            if e.expected().len() == 0 {
                                "something else".to_string()
                            } else {
                                e.expected()
                                    .map(|expected| match expected {
                                        Some(expected) => expected.to_string(),
                                        None => "end of input".to_string(),
                                    })
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            }
                        ))
                        .with_label(
                            Label::new(e.span())
                                .with_message(format!(
                                    "Unexpected token {}",
                                    e.found()
                                        .unwrap_or(&"end of file".to_string())
                                        .fg(Color::Red)
                                ))
                                .with_color(Color::Red),
                        ),
                    chumsky::error::SimpleReason::Custom(msg) => {
                        report.with_message(msg).with_label(
                            Label::new(e.span())
                                .with_message(format!("{}", msg.fg(Color::Red)))
                                .with_color(Color::Red),
                        )
                    }
                };
                report.finish().eprint(Source::from(&src)).unwrap();
            }
            std::process::exit(1)
        }
    }
}
