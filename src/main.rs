use clap::{
    crate_authors, crate_description, crate_name, crate_version, App,
    Arg,
};
use cotton::run;
use std::{fs, process};

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
                .help("Output the generated JavaScript code instead of executing it"),
        )
        .get_matches();
    let file_name = matches.value_of("filename").unwrap();
    let output_js = matches.is_present("js");
    match fs::read_to_string(file_name) {
        Ok(source) => run(&source, output_js),
        Err(e) => {
            eprintln!("{}", e);
            process::exit(1)
        }
    }
}
