use fxhash::FxHashMap;
use std::iter::{empty, once};
use strum::IntoEnumIterator;

use crate::{
    ast_step1::name_id::Name,
    intrinsics::{IntrinsicConstructor, IntrinsicVariable},
};

#[derive(Debug, Eq, PartialEq, Default)]
struct TrueNames {
    true_names: Vec<Name>,
    is_true_name: bool,
    is_public: bool,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Imports(FxHashMap<Name, TrueNames>);

impl Imports {
    pub fn add_true_name(&mut self, true_name: Name, is_public: bool) {
        let a = self.0.entry(true_name).or_default();
        a.is_true_name = true;
        a.is_public = is_public;
    }

    pub fn insert_name_alias(&mut self, from: Name, to: Name) {
        self.0.entry(from).or_default().true_names.push(to);
    }

    pub fn is_public(&self, name: Name) -> bool {
        self.0.get(&name).unwrap().is_public
    }

    pub fn exists(&self, name: Name) -> bool {
        self.0.contains_key(&name)
    }

    pub fn get_all_candidates(
        &self,
        name: Name,
    ) -> Box<dyn Iterator<Item = Name> + '_> {
        if let Some(names) = self.0.get(&name) {
            let ns = names
                .true_names
                .iter()
                .flat_map(|name| self.get_all_candidates(*name));
            if names.is_true_name {
                Box::new(ns.chain(once(name)))
            } else {
                Box::new(ns)
            }
        } else {
            Box::new(empty())
        }
    }
}

impl Default for Imports {
    fn default() -> Self {
        let mut imports = Imports(Default::default());
        for v in IntrinsicVariable::iter() {
            imports.add_true_name(Name::from_str_intrinsic(v.to_str()), true);
        }
        for v in IntrinsicConstructor::iter() {
            imports.add_true_name(Name::from_str_intrinsic(v.to_str()), true);
        }
        imports
    }
}
