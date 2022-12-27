use crate::ast_step1::name_id::Name;
use crate::errors::CompileError;
use crate::intrinsics::{
    IntrinsicConstructor, IntrinsicVariable, INTRINSIC_TYPES,
};
use fxhash::{FxHashMap, FxHashSet};
use parser::Span;
use std::iter::{empty, once};
use strum::IntoEnumIterator;

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

    pub fn set_public(&mut self, name: Name) {
        let a = self.0.entry(name).or_default();
        a.is_public = true;
    }

    pub fn insert_name_alias(
        &mut self,
        from: Name,
        to: Name,
        to_span: Option<Span>,
    ) -> Result<(), CompileError> {
        if self.reachable(to, from) {
            Err(CompileError::NotFound {
                path: to,
                span: to_span.unwrap(),
            })
        } else {
            self.0.entry(from).or_default().true_names.push(to);
            Ok(())
        }
    }

    fn reachable(&self, from: Name, to: Name) -> bool {
        from == to
            || self
                .0
                .get(&from)
                .map(|t| {
                    t.true_names.iter().any(|from| self.reachable(*from, to))
                })
                .unwrap_or(false)
    }

    pub fn is_public(&self, name: Name) -> bool {
        self.0.get(&name).unwrap().is_public
    }

    pub fn exists(&self, name: Name) -> bool {
        self.0.contains_key(&name)
    }

    fn get_all_candidates_rec(
        &self,
        name: Name,
    ) -> Box<dyn Iterator<Item = Name> + '_> {
        if let Some(names) = self.0.get(&name) {
            let ns = names
                .true_names
                .iter()
                .flat_map(|name| self.get_all_candidates_rec(*name));
            if names.is_true_name {
                Box::new(ns.chain(once(name)))
            } else {
                Box::new(ns)
            }
        } else {
            Box::new(empty())
        }
    }

    pub fn get_all_candidates(&self, name: Name) -> impl Iterator<Item = Name> {
        self.get_all_candidates_rec(name)
            .collect::<FxHashSet<_>>()
            .into_iter()
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
        for (name, _) in INTRINSIC_TYPES.iter() {
            imports.add_true_name(Name::from_str_intrinsic(name), true);
        }
        imports
    }
}
