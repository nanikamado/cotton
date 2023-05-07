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
            Arg::new("emit-c")
                .short('c')
                .long("emit-c")
                .help(
                    "Output the generated C code \
                    instead of executing it",
                )
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
                .args(&["emit-c", "types"]),
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
        matches.get_flag("emit-c"),
        matches.get_flag("types"),
        matches.get_flag("language-server"),
    ) {
        (true, false, false) => Command::PrintCSrc,
        (false, true, false) => Command::PrintTypes,
        (false, false, true) => {
            #[cfg(feature = "language-server")]
            {
                language_server::run();
                return;
            }
            #[cfg(not(feature = "language-server"))]
            panic!();
        }
        (false, false, false) => Command::RunC,
        _ => unreachable!(),
    };
    let file_name = matches.value_of("filename").unwrap();
    let loglevel =
        LevelFilter::from_str(matches.value_of("loglevel").unwrap()).unwrap();
    match fs::read_to_string(file_name) {
        Ok(source) => run(&source, file_name, command, loglevel),
        Err(e) => {
            eprintln!("{e}");
            process::exit(1)
        }
    }
}
