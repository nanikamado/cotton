use assert_cmd::{
    assert::Assert,
    prelude::{CommandCargoExt, OutputAssertExt},
};
use itertools::Itertools;
use std::process::Command;
use stripmargin::StripMargin;

fn test_examples(file_name: &str, stdout: &str) {
    Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .arg(["../examples/", file_name].concat())
        .assert()
        .stdout(stdout.to_string())
        .success();
}

fn test_test(file_name: &str) -> Assert {
    Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .arg(["../test/", file_name].concat())
        .assert()
}

#[test]
fn fibonacci() {
    test_examples("fibonacci.cot", "55\n");
}

fn fizzbuzz_model() -> String {
    (1..=100)
        .map(|i| match (i % 3, i % 5) {
            (0, 0) => "FizzBuzz\n".to_string(),
            (0, _) => "Fizz\n".to_string(),
            (_, 0) => "Buzz\n".to_string(),
            _ => format!("{}\n", i),
        })
        .join("")
}

#[test]
fn fizzbuzz() {
    test_examples("fizzbuzz.cot", &fizzbuzz_model());
}

#[test]
fn helloworld() {
    test_examples("helloworld.cot", "Hello, world.\n");
}

#[test]
fn list() {
    test_examples(
        "list.cot",
        &(0..100).map(|i| format!("{}\n", i)).join(""),
    );
}

#[test]
fn multiple_dispatch() {
    test_examples("multiple_dispatch.cot", "Hogeeeeee\nFugaaaaaa\n");
}

const PRIMES: &str = "\
    |2
    |3
    |5
    |7
    |11
    |13
    |17
    |19
    |23
    |29
    |31
    |37
    |41
    |43
    |47
    |53
    |59
    |61
    |67
    |71
    |73
    |79
    |83
    |89
    |97
    |";

#[test]
fn prime() {
    test_examples("prime.cot", &PRIMES.strip_margin());
}

#[test]
fn prime2() {
    test_examples("prime2.cot", &PRIMES.strip_margin());
}

#[test]
fn mutal_recursive_type_alias() {
    test_examples("mutual_recursive_type_alias.cot", "2\n2\n");
}

#[test]
fn list_fail() {
    test_test("list_fail.cot").failure();
}

#[test]
fn list_without_types() {
    let out = (0..100).map(|i| format!("{}\n", i)).join("");
    test_test("list_without_types.cot").stdout(out).success();
}

#[test]
fn mutual_recursive_type_alias_fail() {
    test_test("mutual_recursive_type_alias_fail.cot").failure();
}

#[test]
fn bin_tree() {
    test_examples("bin_tree.cot", "ok\n");
}

#[test]
fn red_black_tree() {
    test_examples("red_black_tree.cot", "ok\n");
}

#[test]
fn to_string_fail() {
    test_test("to_string.cot").failure();
}
