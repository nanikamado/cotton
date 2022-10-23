use dashmap::{mapref, DashMap};
use fxhash::FxBuildHasher;
use once_cell::sync::Lazy;
use std::{
    fmt::{Debug, Display},
    sync::Mutex,
};

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Name(u32);

impl Name {
    fn new() -> Self {
        let mut c = NAME_COUNT.lock().unwrap();
        *c += 1;
        Name(*c - 1)
    }

    pub fn from_str(name: &str) -> Self {
        NAME_MAP.get_name_id(name)
    }

    pub fn as_str(
        self,
    ) -> mapref::one::Ref<'static, Name, String, FxBuildHasher> {
        NAME_MAP.from_name.get(&self).unwrap()
    }
}

static NAME_COUNT: Mutex<u32> = Mutex::new(0);

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(NAME_MAP.from_name.get(self).unwrap().as_str(), f)
    }
}

impl Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(NAME_MAP.from_name.get(self).unwrap().as_str(), f)
    }
}

impl Default for Name {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Default)]
pub struct NameMap {
    from_str: DashMap<String, Name, FxBuildHasher>,
    from_name: DashMap<Name, String, FxBuildHasher>,
}

impl NameMap {
    fn get_name_id(&self, name: &str) -> Name {
        if let Some(n) = self.from_str.get(name) {
            *n.value()
        } else {
            let n = Name::new();
            self.from_str.insert(name.to_string(), n);
            self.from_name.insert(n, name.to_string());
            n
        }
    }
}

pub static NAME_MAP: Lazy<NameMap> = Lazy::new(Default::default);
