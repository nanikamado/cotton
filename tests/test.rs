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
        .arg(["examples/", file_name].concat())
        .assert()
        .stdout(stdout.to_string())
        .success();
}

fn test_test(file_name: &str) -> Assert {
    Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .arg(["tests/", file_name].concat())
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
    test_examples("list.cot", &(0..100).map(|i| format!("{}\n", i)).join(""));
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
    test_test("list_fail.cot").code(1);
}

#[test]
fn list_without_types() {
    let out = (0..100).map(|i| format!("{}\n", i)).join("");
    test_test("list_without_types.cot").stdout(out).success();
}

#[test]
fn mutual_recursive_type_alias_fail() {
    test_test("mutual_recursive_type_alias_fail.cot").code(1);
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
    test_test("to_string.cot").code(1);
}

#[test]
fn do_order() {
    test_test("do_order.cot").stdout("a\na\nb\n").success();
}

#[test]
fn fold() {
    test_examples("fold.cot", "15\n120\n");
}

#[test]
fn red_black_tree_strongly_typed() {
    test_examples("red_black_tree_strongly_typed.cot", "ok\n");
}

#[test]
fn red_black_tree_strongly_typed_fail1() {
    test_test("red_black_tree_strongly_typed_fail1.cot").code(1);
}

#[test]
fn red_black_tree_strongly_typed_fail2() {
    test_test("red_black_tree_strongly_typed_fail2.cot").code(1);
}

#[test]
fn interface() {
    test_examples("interface.cot", "HogeeeeeeHogeeeeee\nFugaaaaaaFugaaaaaa\n");
}

#[test]
fn rfold_with_empty() {
    test_test("rfold_with_empty.cot")
        .stdout("abc\n6\n")
        .success();
}

#[test]
fn tuple_infer() {
    test_test("tuple_infer.cot").stdout("b\n").success();
}

#[test]
fn tuple_infer_fail() {
    test_test("tuple_infer_fail.cot").code(1);
}

#[test]
fn puts() {
    test_examples("puts.cot", "1\n[1, 2, 3]\n");
}

#[test]
fn flat_map() {
    test_examples(
        "flat_map.cot",
        "ok\n\
        [2, 3, 4]\n\
        [1, 10001, 101, 10101, 2, \
        10002, 102, 10102, 3, 10003, 103, 10103]\n",
    );
}
