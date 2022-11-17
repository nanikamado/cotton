use fxhash::FxHashMap;
use once_cell::sync::Lazy;
use std::fmt::{Debug, Display};
use tracing_mutex::stdsync::TracingRwLock as RwLock;

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Name(u32);

fn new_name() -> Name {
    let mut c = NAME_COUNT.lock().unwrap();
    *c += 1;
    Name(*c - 1)
}

impl Name {
    pub fn from_str(name: &str) -> Self {
        NAME_MAP.write().unwrap().get_name_id(name)
    }

    pub fn get_unique() -> Self {
        NAME_MAP.write().unwrap().get_unique_name()
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
            let n = new_name();
            self.from_str.insert(name.to_string(), n);
            self.from_name.insert(n, name.to_string());
            n
        }
    }

    fn get_unique_name(&mut self) -> Name {
        let n = new_name();
        let name = format!("unique_name_{}", n.0);
        self.from_str.insert(name.to_string(), n);
        self.from_name.insert(n, name);
        n
    }
}

static NAME_MAP: Lazy<RwLock<NameMap>> =
    Lazy::new(|| RwLock::new(Default::default()));
