use crate::semantic_tokens_from_src;
use std::fs;
use tower_lsp::lsp_types::*;

#[test]
fn prime_local_type() {
    let src = fs::read_to_string("../examples/prime.cot").unwrap();
    let (_, hover_map) = semantic_tokens_from_src(&src).unwrap();
    if let HoverContents::Markup(c) =
        &hover_map[40][6].as_ref().unwrap().contents
    {
        assert_eq!(
            c.value,
            "```\nrec[(I64 .. I64) | Filter[d0, (I64 -> (True | False))]]\n```"
        )
    } else {
        panic!()
    };
    if let HoverContents::Markup(c) =
        &hover_map[31][10].as_ref().unwrap().contents
    {
        assert_eq!(
            c.value,
            "```\nrec[(I64 .. I64) | Filter[d0, (I64 -> (True | False))]]\n```"
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
        &hover_map[40][14].as_ref().unwrap().contents
    {
        assert_eq!(
            c.value,
            "```\nE \
            | T[R, I64, (E | T[B, I64, \
            rec[fn[E | T[(R | B), d0, d1[d0], d1[d0]]]][I64], \
            rec[fn[E | T[(R | B), d0, d1[d0], d1[d0]]]][I64]]), \
            (E | T[B, I64, rec[fn[E | T[(R | B), d0, d1[d0], d1[d0]]]][I64], \
            rec[fn[E | T[(R | B), d0, d1[d0], d1[d0]]]][I64]])] | \
            T[B, I64, (E | T[(R | B), I64, \
            rec[fn[E | T[(R | B), d0, d1[d0], d1[d0]]]][I64], \
            rec[fn[E | T[(R | B), d0, d1[d0], d1[d0]]]][I64]]), \
            rec[fn[E | T[(R | B), d0, d1[d0], d1[d0]]]][I64]]\n```"
        )
    } else {
        panic!()
    };
    if let HoverContents::Markup(c) =
        &hover_map[37][24].as_ref().unwrap().contents
    {
        assert_eq!(
            c.value,
            "```\nE | T[B, I64, \
            rec[fn[E | T[(R | B), d0, d1[d0], d1[d0]]]][I64], \
            rec[fn[E | T[(R | B), d0, d1[d0], d1[d0]]]][I64]]\n```"
        )
    } else {
        panic!()
    };
}
