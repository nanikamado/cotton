use std::fmt::Display;
use std::sync::Mutex;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DeclId(u32);

impl DeclId {
    pub fn new() -> Self {
        let mut c = DECL_COUNT.lock().unwrap();
        *c += 1;
        DeclId(*c - 1)
    }
}

impl Default for DeclId {
    fn default() -> Self {
        Self::new()
    }
}

static DECL_COUNT: Mutex<u32> = Mutex::new(0);

impl Display for DeclId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
