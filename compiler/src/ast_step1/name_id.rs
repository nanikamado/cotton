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
    pub fn root() -> Self {
        Name(0)
    }

    pub fn pkg_root() -> Self {
        Name::from_str(Self::root(), "pkgroot")
    }

    pub fn prelude() -> Self {
        Name::from_str(Self::root(), "prelude")
    }

    pub fn intrinsic() -> Self {
        Name::from_str(Self::root(), "intrinsic")
    }

    pub fn from_str(path: Self, name: &str) -> Self {
        NAME_MAP.write().unwrap().get_name_id(path, name)
    }

    pub fn from_str_intrinsic(name: &str) -> Self {
        let a = Name::from_str(Self::root(), "intrinsic");
        NAME_MAP.write().unwrap().get_name_id(a, name)
    }

    pub fn get_unique() -> Self {
        NAME_MAP.write().unwrap().get_unique_name()
    }

    pub fn is_root(self) -> bool {
        self.0 == 0
    }

    pub fn split(self) -> Option<(Name, String)> {
        if self.is_root() {
            None
        } else {
            let n = NAME_MAP.read().unwrap();
            Some(n.from_name.get(&self).unwrap().clone())
        }
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
        if let Some((path, name)) = self.split() {
            write!(f, "{:?}::{}", path, name)
        } else {
            write!(f, "root")
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
        let name = (Name::root(), format!("unique_name_{}", n.0));
        self.from_str.insert(name.clone(), n);
        self.from_name.insert(n, name);
        n
    }
}

static NAME_MAP: Lazy<RwLock<NameMap>> =
    Lazy::new(|| RwLock::new(Default::default()));
