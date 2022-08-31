use std::{cell::Cell, fmt::Display};

#[derive(
    Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct IdentId(u32);

impl IdentId {
    pub fn new() -> Self {
        IDENT_COUNT.with(|c| {
            let t = c.get();
            c.set(t + 1);
            IdentId(t)
        })
    }
}

thread_local! {
    static IDENT_COUNT: Cell<u32> = Cell::new(0);
}

impl Display for IdentId {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Default for IdentId {
    fn default() -> Self {
        Self::new()
    }
}
