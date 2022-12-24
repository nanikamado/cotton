use super::name_id::Name;
use fxhash::FxHashMap;
use std::iter::once;

#[derive(Debug, Eq, PartialEq, Default)]
pub struct Imports(FxHashMap<Name, Vec<Name>>);

impl Imports {
    pub fn insert(&mut self, from: Name, to: Name) {
        self.0.entry(from).or_default().push(to);
    }

    pub fn get_all_candidates(
        &self,
        name: Name,
    ) -> Box<dyn Iterator<Item = Name> + '_> {
        if let Some(names) = self.0.get(&name) {
            Box::new(
                names.iter().flat_map(|name| self.get_all_candidates(*name)),
            )
        } else {
            Box::new(once(name))
        }
    }
}
