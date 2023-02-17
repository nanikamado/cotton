use crate::semantic_tokens_from_src;
use std::fs;
use tower_lsp::lsp_types::*;

#[test]
fn prime_local_type() {
    let src = fs::read_to_string("../tests/prime_union.cot").unwrap();
    let (_, hover_map) = semantic_tokens_from_src(&src).unwrap();
    if let HoverContents::Markup(c) =
        &hover_map[31][6].as_ref().unwrap().contents
    {
        assert_eq!(
            c.value,
            "```\nrec[..[I64] | Filter[d0, (I64 -> (True | False))]]\n```"
        )
    } else {
        panic!()
    };
    if let HoverContents::Markup(c) =
        &hover_map[22][10].as_ref().unwrap().contents
    {
        assert_eq!(
            c.value,
            "```\nrec[..[I64] | Filter[d0, (I64 -> (True | False))]]\n```"
        )
    } else {
        panic!()
    };
}

#[test]
fn red_black_tree_local_type() {
    let src = fs::read_to_string("../examples/red_black_tree.cot").unwrap();
    let (_, hover_map) = semantic_tokens_from_src(&src).unwrap();
    if let HoverContents::Markup(c) =
        &hover_map[26][14].as_ref().unwrap().contents
    {
        assert_eq!(c.value, "```\nE | T[I64]\n```")
    } else {
        panic!()
    };
    if let HoverContents::Markup(c) =
        &hover_map[23][24].as_ref().unwrap().contents
    {
        assert_eq!(c.value, "```\nE | T[I64]\n```")
    } else {
        panic!()
    };
}

const NODE: &str = "rec[∀[\
    E \
    | T[R, d0, (E | T[B, d0, d1[d0], d1[d0]]), (E | T[B, d0, d1[d0], d1[d0]])] \
    | T[B, d0, d1[d0], d1[d0]]]]";

#[test]
fn red_black_tree_strongly_typed_local_type() {
    let src =
        fs::read_to_string("../examples/red_black_tree_strongly_typed.cot")
            .unwrap();
    let (_, hover_map) = semantic_tokens_from_src(&src).unwrap();
    if let HoverContents::Markup(c) =
        &hover_map[43][14].as_ref().unwrap().contents
    {
        assert_eq!(
            c.value,
            format!(
                "```\nE \
                | T[\
                    R, \
                    I64, \
                    (E | T[B, I64, {NODE}[I64], {NODE}[I64]]), \
                    (E | T[B, I64, {NODE}[I64], {NODE}[I64]])\
                ] \
                | T[B, I64, {NODE}[I64], {NODE}[I64]]\n```"
            )
            .as_str()
        )
    } else {
        panic!()
    };
    if let HoverContents::Markup(c) =
        &hover_map[40][24].as_ref().unwrap().contents
    {
        assert_eq!(
            c.value,
            format!("```\nE | T[B, I64, {NODE}[I64], {NODE}[I64]]\n```")
                .as_str()
        )
    } else {
        panic!()
    };
}

#[test]
fn interface() {
    let src = fs::read_to_string("../examples/interface.cot").unwrap();
    semantic_tokens_from_src(&src).unwrap();
}
