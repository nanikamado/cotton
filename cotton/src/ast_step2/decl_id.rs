use std::{cell::Cell, fmt::Display};

#[derive(
    Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct DeclId(u32);

impl DeclId {
    pub fn new() -> Self {
        DECL_COUNT.with(|c| {
            let t = c.get();
            c.set(t + 1);
            DeclId(t)
        })
    }
}

impl Default for DeclId {
    fn default() -> Self {
        Self::new()
    }
}

thread_local! {
    static DECL_COUNT: Cell<u32> = Cell::new(0);
}

impl Display for DeclId {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
