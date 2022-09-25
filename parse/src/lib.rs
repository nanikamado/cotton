mod lex;
mod parse;
pub mod token_id;

pub use self::parse::*;

pub fn parse(src: &str) -> Ast {
    let (tokens, src_len) = lex::lex(src);
    parse::parse(tokens, src, src_len)
}
