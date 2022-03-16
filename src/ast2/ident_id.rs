use std::{cell::Cell, fmt::Display};

#[derive(
    Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct IdentId(u32);

pub fn new_ident_id() -> IdentId {
    IDENT_COUNT.with(|c| {
        let t = c.get();
        c.set(t + 1);
        IdentId(t)
    })
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
