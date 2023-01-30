use assert_cmd::assert::Assert;
use assert_cmd::prelude::{CommandCargoExt, OutputAssertExt};
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
            _ => format!("{i}\n"),
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
    test_examples("list.cot", &(0..100).map(|i| format!("{i}\n")).join(""));
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
fn mutual_recursive_type_alias() {
    test_examples("mutual_recursive_type_alias.cot", "2\n2\n");
}

#[test]
fn list_fail() {
    test_test("list_fail.cot").code(1);
}

#[test]
fn list_without_types() {
    let out = (0..100).map(|i| format!("{i}\n")).join("");
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
fn println() {
    test_examples("println.cot", "1\n[1, 2, 3]\n");
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

#[test]
fn question() {
    test_examples(
        "question.cot",
        &"101
        |201
        |301
        |102
        |202
        |302
        |103
        |203
        |303
        |"
        .strip_margin(),
    );
}

#[test]
fn question2() {
    test_examples("question2.cot", "2025\n");
}

#[test]
fn question_eval_order() {
    test_test("question_eval_order.cot")
        .stdout("1\n2\n3\n4\n")
        .success();
}

#[test]
fn question_eval_order2() {
    test_test("question_eval_order2.cot")
        .stdout("1\n2\n3\n4\n")
        .success();
}

#[test]
fn simple_subtype_error_fail() {
    test_test("simple_subtype_error_fail.cot").code(1);
}

#[test]
fn result_println() {
    test_examples("result_println.cot", "Ok(ok!)\nErr(!)\n");
}

#[test]
fn nexts() {
    test_examples("nexts.cot", "D1\n");
}

const PALINDROME: &str = "[D1, D1, D1, D1, D1, D1] palindrome!
[D1, D1, D1, D1, D1, D2]
[D1, D1, D1, D1, D2, D1]
[D1, D1, D1, D1, D2, D2]
[D1, D1, D1, D2, D1, D1]
[D1, D1, D1, D2, D1, D2]
[D1, D1, D1, D2, D2, D1]
[D1, D1, D1, D2, D2, D2]
[D1, D1, D2, D1, D1, D1]
[D1, D1, D2, D1, D1, D2]
[D1, D1, D2, D1, D2, D1]
[D1, D1, D2, D1, D2, D2]
[D1, D1, D2, D2, D1, D1] palindrome!
[D1, D1, D2, D2, D1, D2]
[D1, D1, D2, D2, D2, D1]
[D1, D1, D2, D2, D2, D2]
[D1, D2, D1, D1, D1, D1]
[D1, D2, D1, D1, D1, D2]
[D1, D2, D1, D1, D2, D1] palindrome!
[D1, D2, D1, D1, D2, D2]
[D1, D2, D1, D2, D1, D1]
[D1, D2, D1, D2, D1, D2]
[D1, D2, D1, D2, D2, D1]
[D1, D2, D1, D2, D2, D2]
[D1, D2, D2, D1, D1, D1]
[D1, D2, D2, D1, D1, D2]
[D1, D2, D2, D1, D2, D1]
[D1, D2, D2, D1, D2, D2]
[D1, D2, D2, D2, D1, D1]
[D1, D2, D2, D2, D1, D2]
[D1, D2, D2, D2, D2, D1] palindrome!
[D1, D2, D2, D2, D2, D2]
[D2, D1, D1, D1, D1, D1]
[D2, D1, D1, D1, D1, D2] palindrome!
[D2, D1, D1, D1, D2, D1]
[D2, D1, D1, D1, D2, D2]
[D2, D1, D1, D2, D1, D1]
[D2, D1, D1, D2, D1, D2]
[D2, D1, D1, D2, D2, D1]
[D2, D1, D1, D2, D2, D2]
[D2, D1, D2, D1, D1, D1]
[D2, D1, D2, D1, D1, D2]
[D2, D1, D2, D1, D2, D1]
[D2, D1, D2, D1, D2, D2]
[D2, D1, D2, D2, D1, D1]
[D2, D1, D2, D2, D1, D2] palindrome!
[D2, D1, D2, D2, D2, D1]
[D2, D1, D2, D2, D2, D2]
[D2, D2, D1, D1, D1, D1]
[D2, D2, D1, D1, D1, D2]
[D2, D2, D1, D1, D2, D1]
[D2, D2, D1, D1, D2, D2] palindrome!
[D2, D2, D1, D2, D1, D1]
[D2, D2, D1, D2, D1, D2]
[D2, D2, D1, D2, D2, D1]
[D2, D2, D1, D2, D2, D2]
[D2, D2, D2, D1, D1, D1]
[D2, D2, D2, D1, D1, D2]
[D2, D2, D2, D1, D2, D1]
[D2, D2, D2, D1, D2, D2]
[D2, D2, D2, D2, D1, D1]
[D2, D2, D2, D2, D1, D2]
[D2, D2, D2, D2, D2, D1]
[D2, D2, D2, D2, D2, D2] palindrome!
";

#[test]
fn palindrome_type() {
    test_examples("palindrome_type.cot", PALINDROME);
}

#[test]
fn palindrome_type_with_annotation() {
    test_test("palindrome_type_with_annotation.cot")
        .stdout(PALINDROME)
        .success();
}

#[test]
fn palindrome_type_fail1() {
    test_test("palindrome_type_fail1.cot").code(1);
}

#[test]
fn palindrome_type_fail2() {
    test_test("palindrome_type_fail2.cot").code(1);
}

#[test]
fn error_handling() {
    test_examples("error_handling.cot", "Err(Error1)\n");
}

#[test]
fn inf_implicit_req_fail() {
    test_test("inf_implicit_req_fail.cot").code(1);
}

#[test]
fn type_pattern() {
    test_examples("type_pattern.cot", "D1\nD2\n");
}

#[test]
fn type_pattern_primitive() {
    test_examples("type_pattern_primitive.cot", "2\n1 one\n");
}

#[test]
fn literal_pattern_fail() {
    test_test("literal_pattern_fail.cot").code(1);
}

#[test]
fn modules() {
    test_examples("modules.cot", "D1D1\n");
}

#[test]
fn modules2() {
    test_test("modules2.cot").stdout("D1D1\n").success();
}

#[test]
fn modules3() {
    test_test("modules3.cot")
        .stdout("HogeeeeeeHogeeeeee\nFugaaaaaaFugaaaaaa\n")
        .success();
}

#[test]
fn modules4() {
    test_test("modules4.cot").stdout("a\n").success();
}

#[test]
fn modules_fail() {
    test_test("modules_fail.cot").code(1);
}

#[test]
fn modules_fail2() {
    test_test("modules_fail2.cot").code(1);
}

#[test]
fn modules_fail3() {
    test_test("modules_fail3.cot").code(1);
}

#[test]
fn modules_fail4() {
    test_test("modules_fail4.cot").code(1);
}

#[test]
fn modules_fail5() {
    test_test("modules_fail5.cot").code(1);
}

#[test]
fn modules_fail6() {
    test_test("modules_fail6.cot").code(1);
}

#[test]
fn apply_pattern() {
    test_examples(
        "apply_pattern.cot",
        "n == 2\nn == 6, m == 8, m.fib == 21\nn == 7\n",
    );
}

#[test]
fn lambda_in_apply_pattern() {
    test_test("lambda_in_apply_pattern.cot")
        .stdout("2\n20!\n20\n")
        .success();
}

#[test]
fn field_accessor() {
    test_examples("field_accessor.cot", "1\n1\n1\n");
}

#[test]
fn bin_tree2() {
    test_test("bin_tree2.cot").stdout("ok\n").success();
}

#[test]
fn apply_pattern2() {
    test_test("apply_pattern2.cot").stdout("1\n").success();
}

#[test]
fn apply_pattern_fail() {
    test_test("apply_pattern_fail.cot").code(1);
}

#[test]
fn bin_tree_fail() {
    test_test("bin_tree_fail.cot").code(1);
}

#[test]
fn and_fail() {
    test_test("and_fail.cot").code(1);
}

#[test]
fn shadow_wildcard_import() {
    test_test("shadow_wildcard_import.cot")
        .stdout("[[a]]\n")
        .success();
}

#[test]
fn typed_field_fail() {
    test_test("typed_field_fail.cot").code(1);
}

#[test]
fn variance_fail() {
    test_test("variance_fail.cot").code(1);
}

#[test]
fn variance_fail2() {
    test_test("variance_fail2.cot").code(1);
}

#[test]
fn variance() {
    test_test("variance.cot").stdout("").success();
}

#[test]
fn pattern() {
    test_test("pattern.cot").stdout("").success();
}
