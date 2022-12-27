use std::fmt::Display;
use std::sync::Mutex;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct IdentId(u32);

impl IdentId {
    pub fn new() -> Self {
        let mut c = IDENT_COUNT.lock().unwrap();
        *c += 1;
        IdentId(*c - 1)
    }
}

static IDENT_COUNT: Mutex<u32> = Mutex::new(0);

impl Display for IdentId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Default for IdentId {
    fn default() -> Self {
        Self::new()
    }
}
