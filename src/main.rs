use clap::{
    crate_authors, crate_description, crate_name, crate_version, App,
    Arg,
};
use cotton::run;
use log::LevelFilter;
use std::{fs, process, str::FromStr};

fn main() {
    let matches = App::new(crate_name!())
        .version(crate_version!())
        .author(crate_authors!())
        .about(crate_description!())
        .arg(Arg::new("filename").required(true))
        .arg(
            Arg::new("js")
                .short('j')
                .long("js")
                .takes_value(false)
                .help(
                    "Output the generated JavaScript code \
                    instead of executing it",
                ),
        )
        .arg(
            Arg::new("rust")
                .short('r')
                .long("rust-backend")
                .takes_value(false)
                .help("Compile to Rust code."),
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
    let output_js = matches.is_present("js");
    let use_rust_backend = matches.is_present("rust");
    let loglevel =
        LevelFilter::from_str(matches.value_of("loglevel").unwrap())
            .unwrap();
    match fs::read_to_string(file_name) {
        Ok(source) => {
            run(&source, output_js, use_rust_backend, loglevel)
        }
        Err(e) => {
            eprintln!("{}", e);
            process::exit(1)
        }
    }
}
