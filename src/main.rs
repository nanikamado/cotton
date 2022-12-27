use clap::{command, Arg, ArgAction, ArgGroup};
use compiler::{run, Command};
use log::LevelFilter;
use std::str::FromStr;
use std::{fs, process};

fn main() {
    #[cfg(feature = "backtrace-on-stack-overflow")]
    unsafe {
        backtrace_on_stack_overflow::enable()
    };
    let matches = command!()
        .arg(
            Arg::new("language-server")
                .long("language-server")
                .help("Run language server")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new("filename")
                .required_unless_present_any(["language-server"]),
        )
        .arg(
            Arg::new("js")
                .short('j')
                .long("js")
                .help(
                    "Output the generated JavaScript code \
                    instead of executing it",
                )
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new("rust")
                .short('r')
                .long("rust-backend")
                .help("Compile to Rust code")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new("types")
                .short('t')
                .long("types")
                .help("Output the type of each toplevel declaration")
                .action(ArgAction::SetTrue),
        )
        .group(
            ArgGroup::new("action")
                .required(false)
                .args(&["js", "rust", "types"]),
        )
        .arg(
            Arg::new("loglevel")
                .short('l')
                .long("loglevel")
                .takes_value(true)
                .possible_values([
                    "off", "error", "warn", "info", "debug", "trace",
                ])
                .default_value("error"),
        )
        .get_matches();
    let command = match (
        matches.get_flag("js"),
        matches.get_flag("rust"),
        matches.get_flag("types"),
        matches.get_flag("language-server"),
    ) {
        (true, false, false, false) => Command::PrintJs,
        (false, true, false, false) => Command::RunRust,
        (false, false, true, false) => Command::PrintTypes,
        (false, false, false, true) => {
            #[cfg(feature = "language-server")]
            {
                language_server::run();
                return;
            }
            #[cfg(not(feature = "language-server"))]
            panic!();
        }
        (false, false, false, false) => Command::RunJs,
        _ => unreachable!(),
    };
    let file_name = matches.value_of("filename").unwrap();
    let loglevel =
        LevelFilter::from_str(matches.value_of("loglevel").unwrap()).unwrap();
    match fs::read_to_string(file_name) {
        Ok(source) => run(&source, file_name, command, loglevel),
        Err(e) => {
            eprintln!("{}", e);
            process::exit(1)
        }
    }
}
