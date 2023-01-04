use super::{ConstructorId, TypeId};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::name_id::Name;
use crate::ast_step1::token_map::{TokenMap, TokenMapEntry};
use crate::ast_step3::VariableId;
use crate::errors::CompileError;
use crate::intrinsics::{
    IntrinsicConstructor, IntrinsicVariable, INTRINSIC_TYPES,
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use parser::token_id::TokenId;
use parser::Span;
use strum::IntoEnumIterator;

#[derive(Debug, Eq, PartialEq, Default)]
struct NameEntry {
    true_names: Vec<NameAliasEntry>,
    variables: Vec<VariableDecl>,
    data: Option<DataDecl>,
    type_: Option<TypeDecl>,
    module: Option<ModuleDecl>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum NameKind {
    Variable(VariableId),
    Data(ConstructorId),
    Type(ConstOrAlias),
    Module(Name),
}

#[derive(Debug)]
struct NameResult {
    variables: Vec<VariableId>,
    data: Option<ConstructorId>,
    type_: Option<ConstOrAlias>,
    module: Option<Name>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum ConstOrAlias {
    Const(TypeId),
    Alias(Name),
}

#[derive(Debug, Eq, PartialEq)]
struct VariableDecl {
    variable_id: VariableId,
    is_public: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct DataDecl {
    constructor_id: ConstructorId,
    is_public: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct TypeDecl {
    const_or_alias: ConstOrAlias,
    is_public: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct ModuleDecl {
    is_public: bool,
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct NameAliasEntry {
    alias: Vec<(String, Option<Span>, Option<TokenId>)>,
    base_path: Name,
    is_public: bool,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Imports {
    name_map: FxHashMap<Name, NameEntry>,
    wilde_card_imports: FxHashMap<Name, Vec<NameAliasEntry>>,
}

impl Imports {
    pub fn add_variable(
        &mut self,
        name: Name,
        variable_id: VariableId,
        is_public: bool,
    ) {
        let a = self.name_map.entry(name).or_default();
        a.variables.push(VariableDecl {
            variable_id,
            is_public,
        });
    }

    pub fn add_data(
        &mut self,
        name: Name,
        constructor_id: ConstructorId,
        is_public: bool,
    ) {
        let a = self.name_map.entry(name).or_default();
        if a.data.is_some() {
            panic!("Data with the same name cannot be declared more than once.")
        }
        a.data = Some(DataDecl {
            constructor_id,
            is_public,
        });
    }

    pub fn add_type(&mut self, name: Name, type_id: TypeId, is_public: bool) {
        let a = self.name_map.entry(name).or_default();
        if a.type_.is_some() {
            panic!("Type with the same name cannot be declared more than once.")
        }
        a.type_ = Some(TypeDecl {
            is_public,
            const_or_alias: ConstOrAlias::Const(type_id),
        });
    }

    pub fn add_type_alias(&mut self, name: Name, is_public: bool) {
        let a = self.name_map.entry(name).or_default();
        if a.type_.is_some() {
            panic!("Type with the same name cannot be declared more than once.")
        }
        a.type_ = Some(TypeDecl {
            is_public,
            const_or_alias: ConstOrAlias::Alias(name),
        });
    }

    pub fn add_module(&mut self, name: Name, is_public: bool) {
        let a = self.name_map.entry(name).or_default();
        if a.module.is_some() {
            panic!(
                "Module with the same name cannot be declared more than once."
            )
        }
        a.module = Some(ModuleDecl { is_public });
    }

    pub fn insert_name_alias(
        &mut self,
        from: Name,
        to_base_path: Name,
        to: Vec<(String, Option<Span>, Option<TokenId>)>,
        is_public: bool,
    ) {
        self.name_map.entry(from).or_default().true_names.push(
            NameAliasEntry {
                alias: to,
                base_path: to_base_path,
                is_public,
            },
        );
    }

    pub fn insert_wild_card_import(
        &mut self,
        from: Name,
        to_base_path: Name,
        to: Vec<(String, Option<Span>, Option<TokenId>)>,
        is_public: bool,
    ) {
        self.wilde_card_imports
            .entry(from)
            .or_default()
            .push(NameAliasEntry {
                alias: to,
                base_path: to_base_path,
                is_public,
            });
    }

    pub fn exists(&self, name: Name) -> bool {
        self.name_map.contains_key(&name)
    }

    #[allow(clippy::too_many_arguments)]
    fn get_true_names_rec(
        &mut self,
        scope: Name,
        path: Name,
        name_str: &str,
        span: Option<Span>,
        token_map: &mut TokenMap,
        visited: &FxHashSet<Name>,
        check_existence_in_name_map: bool,
        true_names: &mut FxHashSet<NameKind>,
    ) -> Result<(), CompileError> {
        let name = Name::from_str(path, name_str);
        if visited.contains(&name) {
            return Err(CompileError::NotFound {
                path: name,
                span: span.unwrap(),
            });
        }
        let mut visited = visited.clone();
        visited.insert(name);
        let mut ns = Default::default();
        for a in self
            .wilde_card_imports
            .get(&path)
            .cloned()
            .into_iter()
            .flatten()
        {
            if a.is_public || path.is_same_as_or_ancestor_of(scope) {
                let m = self.get_module_with_path(
                    scope,
                    a.base_path,
                    &a.alias
                        .iter()
                        .map(|(a, b, c)| (a.as_str(), b.clone(), *c))
                        .collect_vec(),
                    token_map,
                    &visited,
                )?;
                self.get_true_names_rec(
                    scope,
                    m,
                    name_str,
                    span.clone(),
                    token_map,
                    &visited,
                    check_existence_in_name_map,
                    &mut ns,
                )?;
            }
        }
        if let Some(name_entry) = self.name_map.get_mut(&name) {
            for name_alias_entry in name_entry.true_names.clone().into_iter() {
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
                    &mut ns,
                )?;
            }
            let name_entry = self.name_map.get_mut(&name).unwrap();
            for v in &name_entry.variables {
                if v.is_public || path.is_same_as_or_ancestor_of(scope) {
                    ns.insert(NameKind::Variable(v.variable_id));
                }
            }
            if let Some(d) = &name_entry.data {
                if d.is_public || path.is_same_as_or_ancestor_of(scope) {
                    ns.insert(NameKind::Data(d.constructor_id));
                }
            }
            if let Some(d) = &name_entry.type_ {
                if d.is_public || path.is_same_as_or_ancestor_of(scope) {
                    ns.insert(NameKind::Type(d.const_or_alias));
                }
            }
            if let Some(d) = &name_entry.module {
                if d.is_public || path.is_same_as_or_ancestor_of(scope) {
                    ns.insert(NameKind::Module(name));
                }
            }
        }
        true_names.extend(ns);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn get_module(
        &mut self,
        scope: Name,
        base_path: Name,
        name: &str,
        _token_id: Option<TokenId>,
        span: Option<Span>,
        token_map: &mut TokenMap,
        visited: &FxHashSet<Name>,
    ) -> Result<Name, CompileError> {
        let mut ns = Default::default();
        self.get_true_names_rec(
            scope,
            base_path,
            name,
            span.clone(),
            token_map,
            visited,
            true,
            &mut ns,
        )?;
        let n = collect_name_kinds(ns);
        n.module.map(Ok).unwrap_or_else(|| {
            Err(CompileError::NotFound {
                path: Name::from_str(base_path, name),
                span: span.unwrap(),
            })
        })
    }

    pub fn get_module_with_path(
        &mut self,
        scope: Name,
        mut base_path: Name,
        mut path: &[(&str, Option<Span>, Option<TokenId>)],
        token_map: &mut TokenMap,
        visited: &FxHashSet<Name>,
    ) -> Result<Name, CompileError> {
        if path.is_empty() {
            Ok(base_path)
        } else {
            if path[0].0 == "pkg" {
                token_map.insert(path[0].2, TokenMapEntry::KeyWord);
                base_path = Name::pkg_root();
                path = &path[1..];
            }
            for (name, span, token_id) in path {
                base_path = self.get_module(
                    scope,
                    base_path,
                    name,
                    *token_id,
                    span.clone(),
                    token_map,
                    visited,
                )?;
            }
            Ok(base_path)
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn get_true_names_with_path_rec(
        &mut self,
        scope: Name,
        mut base_path: Name,
        mut path: &[(&str, Option<Span>, Option<TokenId>)],
        token_map: &mut TokenMap,
        visited: &FxHashSet<Name>,
        check_existence_in_name_map: bool,
        true_names: &mut FxHashSet<NameKind>,
    ) -> Result<(), CompileError> {
        if path.is_empty() {
            true_names.insert(NameKind::Module(base_path));
            Ok(())
        } else {
            if path[0].0 == "pkg" {
                token_map.insert(path[0].2, TokenMapEntry::KeyWord);
                base_path = Name::pkg_root();
                path = &path[1..];
            }
            for (name, span, token_id) in path.iter().take(path.len() - 1) {
                base_path = self.get_module(
                    scope,
                    base_path,
                    name,
                    *token_id,
                    span.clone(),
                    token_map,
                    visited,
                )?;
            }
            let (name, span, _token_id) = path.last().unwrap();
            self.get_true_names_rec(
                scope,
                base_path,
                name,
                span.clone(),
                token_map,
                visited,
                check_existence_in_name_map,
                true_names,
            )?;
            Ok(())
        }
    }

    fn get_names(
        &mut self,
        scope: Name,
        base_path: Name,
        path: &[(&str, Option<Span>, Option<TokenId>)],
        token_map: &mut TokenMap,
    ) -> Result<(NameResult, Name, Option<Span>), CompileError> {
        let visited = Default::default();
        let base_path = self.get_module_with_path(
            scope,
            base_path,
            &path[..path.len() - 1],
            token_map,
            &visited,
        )?;
        let (name, span, _token_id) = path.last().unwrap();
        let mut ns = Default::default();
        self.get_true_names_rec(
            scope,
            base_path,
            name,
            span.clone(),
            token_map,
            &FxHashSet::default(),
            true,
            &mut ns,
        )?;
        Ok((
            collect_name_kinds(ns),
            Name::from_str(base_path, name),
            span.clone(),
        ))
    }

    pub fn get_constructor(
        &mut self,
        scope: Name,
        base_path: Name,
        path: &[(&str, Option<Span>, Option<TokenId>)],
        token_map: &mut TokenMap,
    ) -> Result<(Name, ConstructorId), CompileError> {
        let (n, path, span) =
            self.get_names(scope, base_path, path, token_map)?;
        n.data
            .map(|id| (path, id))
            .ok_or_else(|| CompileError::NotFound {
                path,
                span: span.unwrap(),
            })
    }

    pub fn get_type(
        &mut self,
        scope: Name,
        base_path: Name,
        name: &str,
        span: Option<Span>,
        token_map: &mut TokenMap,
    ) -> Result<ConstOrAlias, CompileError> {
        let mut ns = Default::default();
        self.get_true_names_rec(
            scope,
            base_path,
            name,
            span.clone(),
            token_map,
            &FxHashSet::default(),
            true,
            &mut ns,
        )?;
        let n = collect_name_kinds(ns);
        n.type_.ok_or_else(|| CompileError::NotFound {
            path: Name::from_str(base_path, name),
            span: span.unwrap(),
        })
    }

    pub fn get_variables(
        &mut self,
        scope: Name,
        path: Name,
        name: &str,
        span: Option<Span>,
        token_map: &mut TokenMap,
        candidates_from_implicit_parameters: &FxHashMap<&str, Vec<DeclId>>,
    ) -> Result<Vec<VariableId>, CompileError> {
        let mut ns = Default::default();
        self.get_true_names_rec(
            scope,
            path,
            name,
            span.clone(),
            token_map,
            &FxHashSet::default(),
            true,
            &mut ns,
        )?;
        let n = collect_name_kinds(ns);
        let mut names = n.variables;
        names.extend(
            candidates_from_implicit_parameters
                .get(name)
                .into_iter()
                .flatten()
                .map(|d| VariableId::Decl(*d)),
        );
        if names.is_empty() {
            Err(CompileError::NotFound {
                path: Name::from_str(path, name),
                span: span.unwrap(),
            })
        } else {
            Ok(names)
        }
    }

    pub fn get_variables_with_path(
        &mut self,
        scope: Name,
        base_path: Name,
        path: &[(&str, Option<Span>, Option<TokenId>)],
        token_map: &mut TokenMap,
        candidates_from_implicit_parameters: &FxHashMap<&str, Vec<DeclId>>,
    ) -> Result<Vec<VariableId>, CompileError> {
        let (n, p, span) = self.get_names(scope, base_path, path, token_map)?;
        let mut names = n.variables;
        if path.len() == 1 {
            let n = path.last().unwrap().0;
            names.extend(
                candidates_from_implicit_parameters
                    .get(n)
                    .into_iter()
                    .flatten()
                    .map(|d| VariableId::Decl(*d)),
            );
        }
        if names.is_empty() {
            Err(CompileError::NotFound {
                path: p,
                span: span.unwrap(),
            })
        } else {
            Ok(names)
        }
    }
}

fn collect_name_kinds(names: FxHashSet<NameKind>) -> NameResult {
    let mut variables = Vec::new();
    let mut data = None;
    let mut type_ = None;
    let mut module = None;
    for n in names {
        match n {
            NameKind::Variable(v) => variables.push(v),
            NameKind::Data(d) => {
                debug_assert!(data.is_none());
                data = Some(d);
            }
            NameKind::Type(n) => {
                debug_assert!(type_.is_none());
                type_ = Some(n);
            }
            NameKind::Module(m) => {
                debug_assert!(module.is_none());
                module = Some(m);
            }
        }
    }
    NameResult {
        variables,
        data,
        type_,
        module,
    }
}

impl Default for Imports {
    fn default() -> Self {
        let mut imports = Imports {
            name_map: Default::default(),
            wilde_card_imports: Default::default(),
        };

        for v in IntrinsicVariable::iter() {
            imports.add_variable(
                Name::from_str_intrinsic(v.to_str()),
                VariableId::IntrinsicVariable(v),
                true,
            );
        }
        for v in IntrinsicConstructor::iter() {
            imports.add_data(
                Name::from_str_intrinsic(v.to_str()),
                ConstructorId::Intrinsic(v),
                true,
            );
            imports.add_variable(
                Name::from_str_intrinsic(v.to_str()),
                VariableId::IntrinsicConstructor(v),
                true,
            );
        }
        for (name, id) in INTRINSIC_TYPES.iter() {
            imports.add_type(
                Name::from_str_intrinsic(name),
                TypeId::Intrinsic(*id),
                true,
            );
        }
        imports
    }
}
