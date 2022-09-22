use clap::{command, Arg, ArgAction, ArgGroup};
use cotton::{run, Command};
use log::LevelFilter;
use std::{fs, process, str::FromStr};

fn main() {
    let matches = command!()
        .arg(Arg::new("filename").required(true))
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
    let file_name = matches.value_of("filename").unwrap();
    let command = match (
        matches.get_flag("js"),
        matches.get_flag("rust"),
        matches.get_flag("types"),
    ) {
        (true, false, false) => Command::PrintJs,
        (false, true, false) => Command::RunRust,
        (false, false, true) => Command::PrintTypes,
        (false, false, false) => Command::RunJs,
        _ => unreachable!(),
    };
    let loglevel =
        LevelFilter::from_str(matches.value_of("loglevel").unwrap()).unwrap();
    match fs::read_to_string(file_name) {
        Ok(source) => run(&source, command, loglevel),
        Err(e) => {
            eprintln!("{}", e);
            process::exit(1)
        }
    }
}
