use crate::ast_step1::name_id::Name;
use crate::ast_step1::token_map::{TokenMap, TokenMapEntry};
use crate::errors::CompileError;
use crate::intrinsics::{
    IntrinsicConstructor, IntrinsicVariable, INTRINSIC_TYPES,
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use parser::token_id::TokenId;
use parser::Span;
use std::iter::once;
use strum::IntoEnumIterator;

#[derive(Debug, Eq, PartialEq, Default)]
struct NameEntry {
    true_names: Vec<NameAliasEntry>,
    alias_computation: AliasComputation,
    is_true_name: bool,
    is_public: bool,
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct NameAliasEntry {
    alias: Vec<(String, Option<Span>, Option<TokenId>)>,
    base_path: Name,
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum AliasComputation {
    Unaliased(FxHashSet<Name>),
    NotUnaliased,
}

impl Default for AliasComputation {
    fn default() -> Self {
        AliasComputation::NotUnaliased
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct Imports {
    name_map: FxHashMap<Name, NameEntry>,
    public_names_of_each_module: FxHashMap<Name, Vec<Name>>,
}

impl Imports {
    pub fn add_true_name(&mut self, name: Name, is_public: bool) {
        let a = self.name_map.entry(name).or_default();
        a.is_true_name = true;
        a.is_public = is_public;
        if is_public {
            self.public_names_of_each_module
                .entry(name.split().unwrap().0)
                .or_default()
                .push(name);
        }
    }

    pub fn set_public(&mut self, name: Name) {
        let a = self.name_map.entry(name).or_default();
        a.is_public = true;
        self.public_names_of_each_module
            .entry(name.split().unwrap().0)
            .or_default()
            .push(name);
    }

    pub fn insert_name_alias(
        &mut self,
        from: Name,
        to_base_path: Name,
        to: Vec<(String, Option<Span>, Option<TokenId>)>,
    ) {
        self.name_map.entry(from).or_default().true_names.push(
            NameAliasEntry {
                alias: to,
                base_path: to_base_path,
            },
        );
    }

    pub fn is_public(&self, name: Name) -> bool {
        self.name_map.get(&name).unwrap().is_public
    }

    pub fn exists(&self, name: Name) -> bool {
        self.name_map.contains_key(&name)
    }

    pub fn get_true_names(
        &mut self,
        scope: Name,
        path: Name,
        name: &str,
        _token_id: Option<TokenId>,
        span: Option<Span>,
        token_map: &mut TokenMap,
    ) -> Result<impl Iterator<Item = Name>, CompileError> {
        Ok(self
            .get_true_names_rec(
                scope,
                path,
                name,
                _token_id,
                span,
                token_map,
                &FxHashSet::default(),
                true,
            )?
            .into_iter())
    }

    #[allow(clippy::too_many_arguments)]
    fn get_true_names_rec(
        &mut self,
        scope: Name,
        path: Name,
        name_str: &str,
        _token_id: Option<TokenId>,
        span: Option<Span>,
        token_map: &mut TokenMap,
        visited: &FxHashSet<Name>,
        check_existence_in_name_map: bool,
    ) -> Result<FxHashSet<Name>, CompileError> {
        let name = Name::from_str(path, name_str);
        if name_str == "Self" {
            return Ok(once(name).collect());
        }
        if self.exists(name)
            && !self.is_public(name)
            && !path.is_same_as_or_ancestor_of(scope)
        {
            return Err(CompileError::InaccessibleName {
                path: name,
                span: span.unwrap(),
            });
        }
        if visited.contains(&name) {
            return Err(CompileError::NotFound {
                path: name,
                span: span.unwrap(),
            });
        }
        let mut visited = visited.clone();
        visited.insert(name);
        if let Some(name_entry) = self.name_map.get_mut(&name) {
            match name_entry.alias_computation.clone() {
                AliasComputation::Unaliased(names) => Ok(names),
                AliasComputation::NotUnaliased => {
                    let mut ns: FxHashSet<_> = name_entry
                        .true_names
                        .clone()
                        .into_iter()
                        .map(|name_alias_entry| {
                            self.get_true_names_with_path_rec(
                                scope,
                                name_alias_entry.base_path,
                                &name_alias_entry
                                    .alias
                                    .iter()
                                    .map(|(s, span, token_id)| {
                                        (s.as_str(), span.clone(), *token_id)
                                    })
                                    .collect_vec(),
                                token_map,
                                &visited,
                                check_existence_in_name_map,
                            )
                            .map(|a| a.collect_vec())
                        })
                        .try_collect::<_, Vec<_>, _>()?
                        .into_iter()
                        .flatten()
                        .collect();
                    let name_entry = self.name_map.get_mut(&name).unwrap();
                    if name_entry.is_true_name {
                        ns.insert(name);
                    }
                    name_entry.alias_computation =
                        AliasComputation::Unaliased(ns.clone());
                    Ok(ns)
                }
            }
        } else if check_existence_in_name_map {
            Err(CompileError::NotFound {
                path: name,
                span: span.unwrap(),
            })
        } else {
            Ok(once(name).collect())
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn get_true_name(
        &mut self,
        scope: Name,
        base_path: Name,
        name: &str,
        token_id: Option<TokenId>,
        span: Option<Span>,
        token_map: &mut TokenMap,
        visited: &FxHashSet<Name>,
    ) -> Result<Name, CompileError> {
        let ns = self.get_true_names_rec(
            scope, base_path, name, token_id, span, token_map, visited, true,
        )?;
        debug_assert_eq!(ns.len(), 1);
        Ok(*ns.iter().next().unwrap())
    }

    pub fn get_true_names_with_path(
        &mut self,
        scope: Name,
        base_path: Name,
        path: &[(&str, Option<Span>, Option<TokenId>)],
        token_map: &mut TokenMap,
    ) -> Result<Box<dyn Iterator<Item = Name> + '_>, CompileError> {
        self.get_true_names_with_path_rec(
            scope,
            base_path,
            path,
            token_map,
            &FxHashSet::default(),
            true,
        )
    }

    fn get_true_names_with_path_unchecked(
        &mut self,
        scope: Name,
        base_path: Name,
        path: &[(&str, Option<Span>, Option<TokenId>)],
        token_map: &mut TokenMap,
    ) -> Result<Box<dyn Iterator<Item = Name> + '_>, CompileError> {
        self.get_true_names_with_path_rec(
            scope,
            base_path,
            path,
            token_map,
            &FxHashSet::default(),
            false,
        )
    }

    fn get_true_names_with_path_rec(
        &mut self,
        scope: Name,
        mut base_path: Name,
        mut path: &[(&str, Option<Span>, Option<TokenId>)],
        token_map: &mut TokenMap,
        visited: &FxHashSet<Name>,
        check_existence_in_name_map: bool,
    ) -> Result<Box<dyn Iterator<Item = Name> + '_>, CompileError> {
        if path.is_empty() {
            Ok(Box::new(once(base_path)))
        } else {
            if path[0].0 == "pkg" {
                token_map.insert(path[0].2, TokenMapEntry::KeyWord);
                base_path = Name::pkg_root();
                path = &path[1..];
            }
            for (name, span, token_id) in path.iter().take(path.len() - 1) {
                base_path = self.get_true_name(
                    scope,
                    base_path,
                    name,
                    *token_id,
                    span.clone(),
                    token_map,
                    visited,
                )?;
            }
            let (name, span, token_id) = path.last().unwrap();
            Ok(Box::new(
                self.get_true_names_rec(
                    scope,
                    base_path,
                    name,
                    *token_id,
                    span.clone(),
                    token_map,
                    visited,
                    check_existence_in_name_map,
                )?
                .into_iter(),
            ))
        }
    }

    pub fn get_true_name_with_path(
        &mut self,
        scope: Name,
        base_path: Name,
        path: &[(&str, Option<Span>, Option<TokenId>)],
        token_map: &mut TokenMap,
    ) -> Result<Name, CompileError> {
        let ns = self
            .get_true_names_with_path(scope, base_path, path, token_map)?
            .collect_vec();
        debug_assert_eq!(ns.len(), 1);
        Ok(ns[0])
    }

    pub fn get_true_name_with_path_unchecked(
        &mut self,
        scope: Name,
        base_path: Name,
        path: &[(&str, Option<Span>, Option<TokenId>)],
        token_map: &mut TokenMap,
    ) -> Result<Name, CompileError> {
        let ns = self
            .get_true_names_with_path_unchecked(
                scope, base_path, path, token_map,
            )?
            .collect_vec();
        debug_assert_eq!(ns.len(), 1);
        Ok(ns[0])
    }

    pub fn public_names_in_module(&mut self, module: Name) -> &Vec<Name> {
        self.public_names_of_each_module.entry(module).or_default()
    }
}

impl Default for Imports {
    fn default() -> Self {
        let mut imports = Imports {
            name_map: Default::default(),
            public_names_of_each_module: Default::default(),
        };
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
