use fxhash::FxHashMap;
use std::hash::Hash;

#[derive(Debug, Clone)]
pub struct Collector<T: Eq + Hash> {
    map: FxHashMap<T, usize>,
    len: usize,
}

impl<T: Eq + Hash> Collector<T> {
    pub fn get(&mut self, t: T) -> usize {
        self.len += 1;
        *self.map.entry(t).or_insert(self.len - 1)
    }

    pub fn get_empty_id(&mut self) -> usize {
        self.len += 1;
        self.len - 1
    }

    pub fn insert_with_id(&mut self, t: T, id: usize) {
        let o = self.map.insert(t, id);
        debug_assert!(o.is_none());
    }

    pub fn into_raw(self) -> FxHashMap<T, usize> {
        self.map
    }
}

impl<T: Eq + Hash> Default for Collector<T> {
    fn default() -> Self {
        Self {
            map: Default::default(),
            len: 0,
        }
    }
}
