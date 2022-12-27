use std::cell::Cell;
use std::fmt::Display;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TokenId(u32);

impl TokenId {
    pub fn new() -> Self {
        IDENT_COUNT.with(|c| {
            let t = c.get();
            c.set(t + 1);
            TokenId(t)
        })
    }
}

thread_local! {
    static IDENT_COUNT: Cell<u32> = Cell::new(0);
}

impl Display for TokenId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Default for TokenId {
    fn default() -> Self {
        Self::new()
    }
}
