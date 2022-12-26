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
    pub fn root_module() -> Self {
        Name(0)
    }

    pub fn from_str(path: Self, name: &str) -> Self {
        NAME_MAP.write().unwrap().get_name_id(path, name)
    }

    pub fn from_str_intrinsic(name: &str) -> Self {
        let a = Name::from_str(Self::root_module(), "intrinsic");
        NAME_MAP.write().unwrap().get_name_id(a, name)
    }

    pub fn get_unique() -> Self {
        NAME_MAP.write().unwrap().get_unique_name()
    }

    fn is_root(self) -> bool {
        self.0 == 0
    }
}

static NAME_COUNT: std::sync::Mutex<u32> = std::sync::Mutex::new(1);

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(
            NAME_MAP
                .read()
                .unwrap()
                .from_name
                .get(self)
                .unwrap()
                .1
                .as_str(),
            f,
        )
    }
}

impl Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_root() {
            write!(f, "root")
        } else {
            let s = {
                let n = NAME_MAP.read().unwrap();
                n.from_name.get(self).unwrap().clone()
            };
            write!(f, "{:?}::{}", s.0, s.1)
        }
    }
}

#[derive(Debug, Default)]
pub struct NameMap {
    from_str: FxHashMap<(Name, String), Name>,
    from_name: FxHashMap<Name, (Name, String)>,
}

impl NameMap {
    fn get_name_id(&mut self, path: Name, name: &str) -> Name {
        let s = (path, name.to_string());
        if let Some(n) = self.from_str.get(&s) {
            *n
        } else {
            let n = new_name();
            self.from_str.insert(s.clone(), n);
            self.from_name.insert(n, s);
            n
        }
    }

    fn get_unique_name(&mut self) -> Name {
        let n = new_name();
        let name = (Name::root_module(), format!("unique_name_{}", n.0));
        self.from_str.insert(name.clone(), n);
        self.from_name.insert(n, name);
        n
    }
}

static NAME_MAP: Lazy<RwLock<NameMap>> =
    Lazy::new(|| RwLock::new(Default::default()));
