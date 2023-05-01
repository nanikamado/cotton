use std::fs;
use std::io::{ErrorKind, Write};
use std::process::{self, Stdio};
use tempfile::NamedTempFile;

pub fn run(c_src: &str) -> Result<(), ()> {
    let tmp = NamedTempFile::new().unwrap();
    let tmp_path = tmp.path().to_str().unwrap().to_string();
    tmp.close().unwrap();
    match process::Command::new("clang")
        .args(["-x", "c", "-o", &tmp_path, "-"])
        .stdin(Stdio::piped())
        .spawn()
    {
        Ok(mut child) => {
            child
                .stdin
                .as_mut()
                .unwrap()
                .write_all(c_src.as_bytes())
                .unwrap();
            assert!(child.wait().unwrap().success());
            process::Command::new(&tmp_path)
                .spawn()
                .unwrap()
                .wait()
                .unwrap();
            fs::remove_file(tmp_path).unwrap();
            Ok(())
        }
        Err(e) => {
            match e.kind() {
                ErrorKind::NotFound => eprintln!(
                    "clang command not found. \
                    You need to install clang."
                ),
                _ => eprintln!("failed to run clang"),
            };
            fs::remove_file(tmp_path).unwrap();
            Err(())
        }
    }
}
