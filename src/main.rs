use clap::{crate_authors, crate_description, crate_name, crate_version, App, Arg};
use cotton::run;
use std::{fs, process};

fn main() {
    let matches = App::new(crate_name!())
        .version(crate_version!())
        .author(crate_authors!())
        .about(crate_description!())
        .arg(Arg::with_name("filename").required(true))
        .get_matches();
    let file_name = matches.value_of("filename").unwrap();
    match fs::read_to_string(file_name) {
        Ok(source) => run(&source),
        Err(e) => {
            eprintln!("{}", e);
            process::exit(1)
        }
    }
}
