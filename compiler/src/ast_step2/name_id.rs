use fxhash::FxHashMap;
use once_cell::sync::Lazy;
use std::fmt::{Debug, Display};
use tracing_mutex::stdsync::TracingRwLock as RwLock;

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Name(u32);

impl Name {
    fn new() -> Self {
        let mut c = NAME_COUNT.lock().unwrap();
        *c += 1;
        Name(*c - 1)
    }

    pub fn from_str(name: &str) -> Self {
        NAME_MAP.write().unwrap().get_name_id(name)
    }
}

static NAME_COUNT: std::sync::Mutex<u32> = std::sync::Mutex::new(0);

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(
            NAME_MAP
                .read()
                .unwrap()
                .from_name
                .get(self)
                .unwrap()
                .as_str(),
            f,
        )
    }
}

impl Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(
            NAME_MAP
                .read()
                .unwrap()
                .from_name
                .get(self)
                .unwrap()
                .as_str(),
            f,
        )
    }
}

impl Default for Name {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Default)]
pub struct NameMap {
    from_str: FxHashMap<String, Name>,
    from_name: FxHashMap<Name, String>,
}

impl NameMap {
    fn get_name_id(&mut self, name: &str) -> Name {
        if let Some(n) = self.from_str.get(name) {
            *n
        } else {
            let n = Name::new();
            self.from_str.insert(name.to_string(), n);
            self.from_name.insert(n, name.to_string());
            n
        }
    }
}

static NAME_MAP: Lazy<RwLock<NameMap>> =
    Lazy::new(|| RwLock::new(Default::default()));
