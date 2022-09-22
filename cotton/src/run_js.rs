use std::{
    io::Write,
    process::{self, Stdio},
};

pub fn run(js: &str) {
    let mut child = process::Command::new("node")
        .stdin(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(js.as_bytes())
        .unwrap();
    child.wait().unwrap();
}
