use super::{ConstructorId, TypeId};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::name_id::Path;
use crate::ast_step1::token_map::{TokenMap, TokenMapEntry};
use crate::ast_step3::{VariableId, VariableIdInScope};
use crate::errors::CompileError;
use crate::intrinsics::{
    IntrinsicConstructor, IntrinsicVariable, INTRINSIC_TYPES, OP_PRECEDENCE,
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use parser::token_id::TokenId;
use parser::{Associativity, Span};
use strum::IntoEnumIterator;

#[derive(Debug, Eq, PartialEq, Default)]
struct NameEntry {
    true_names: Vec<NameAliasEntry>,
    variables: Vec<VariableDecl>,
    accessors: Vec<AccessorDecl>,
    op_precedence: Option<OpPrecedenceDecl>,
    data: Option<DataDecl>,
    type_: Option<TypeDecl>,
    interface: Option<InterfaceDecl>,
    module: Option<ModuleDecl>,
}

#[derive(Debug, Default)]
struct NameResult {
    variables: FxHashSet<VariableId>,
    variables_imported_by_wild_card: FxHashSet<VariableId>,
    accessors: FxHashSet<(DeclId, usize)>,
    data: Option<(ConstructorId, bool /* imported_by_wild_card */)>,
    type_: Option<ConstOrAlias>,
    interface: Option<Path>,
    module: Option<Path>,
    op_precedence: Option<(Associativity, i32)>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum ConstOrAlias {
    Const(TypeId, usize),
    Alias(Path),
}

#[derive(Debug, Eq, PartialEq)]
struct VariableDecl {
    variable_id: VariableId,
    is_public: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct AccessorDecl {
    constructor: DeclId,
    field: usize,
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
struct InterfaceDecl {
    is_public: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct ModuleDecl {
    is_public: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct OpPrecedenceDecl {
    associativity: Associativity,
    precedence: i32,
    is_public: bool,
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct NameAliasEntry {
    alias: Vec<parser::StringWithId>,
    base_path: Path,
    scope: Path,
    is_public: bool,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Imports {
    name_map: FxHashMap<Path, NameEntry>,
    wild_card_imports: FxHashMap<Path, Vec<NameAliasEntry>>,
    type_id_to_name: FxHashMap<TypeId, Path>,
}

impl Imports {
    pub fn add_variable(
        &mut self,
        name: Path,
        variable_id: VariableId,
        is_public: bool,
    ) {
        let a = self.name_map.entry(name).or_default();
        a.variables.push(VariableDecl {
            variable_id,
            is_public,
        });
    }

    pub fn add_accessor(
        &mut self,
        name: Path,
        constructor: DeclId,
        field: usize,
        is_public: bool,
    ) {
        let a = self.name_map.entry(name).or_default();
        a.accessors.push(AccessorDecl {
            constructor,
            field,
            is_public,
        });
    }

    pub fn add_op_precedence(
        &mut self,
        name: Path,
        associativity: Associativity,
        precedence: i32,
        is_public: bool,
    ) {
        let a = self.name_map.entry(name).or_default();
        if a.op_precedence.is_some() {
            panic!("Multiple precedence declarations for operators with the same name.")
        }
        a.op_precedence = Some(OpPrecedenceDecl {
            associativity,
            precedence,
            is_public,
        });
    }

    pub fn add_data(
        &mut self,
        name: Path,
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

    pub fn add_type(
        &mut self,
        name: Path,
        type_id: TypeId,
        is_public: bool,
        parameter_len: usize,
    ) {
        let a = self.name_map.entry(name).or_default();
        if a.type_.is_some() {
            panic!("Type with the same name cannot be declared more than once.")
        }
        self.type_id_to_name.insert(type_id, name);
        a.type_ = Some(TypeDecl {
            is_public,
            const_or_alias: ConstOrAlias::Const(type_id, parameter_len),
        });
    }

    pub fn add_type_alias(&mut self, name: Path, is_public: bool) {
        let a = self.name_map.entry(name).or_default();
        if a.type_.is_some() {
            panic!("Type with the same name cannot be declared more than once.")
        }
        a.type_ = Some(TypeDecl {
            is_public,
            const_or_alias: ConstOrAlias::Alias(name),
        });
    }

    pub fn add_interface(&mut self, name: Path, is_public: bool) {
        let a = self.name_map.entry(name).or_default();
        if a.type_.is_some() {
            panic!("Type with the same name cannot be declared more than once.")
        }
        a.interface = Some(InterfaceDecl { is_public });
    }

    pub fn add_module(&mut self, name: Path, is_public: bool) {
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
        scope: Path,
        from: Path,
        to_base_path: Path,
        to: Vec<parser::StringWithId>,
        is_public: bool,
    ) {
        self.name_map.entry(from).or_default().true_names.push(
            NameAliasEntry {
                alias: to,
                base_path: to_base_path,
                is_public,
                scope,
            },
        );
    }

    pub fn insert_wild_card_import(
        &mut self,
        from: Path,
        to_base_path: Path,
        to: Vec<parser::StringWithId>,
        is_public: bool,
    ) {
        self.wild_card_imports
            .entry(from)
            .or_default()
            .push(NameAliasEntry {
                alias: to,
                base_path: to_base_path,
                is_public,
                scope: from,
            });
    }

    pub fn exists(&self, name: Path) -> bool {
        self.name_map.contains_key(&name)
    }

    #[allow(clippy::too_many_arguments)]
    fn get_true_names_rec(
        &mut self,
        scope: Path,
        path: Path,
        name_str: &str,
        span: Option<Span>,
        token_map: &mut TokenMap,
        visited: &FxHashSet<Path>,
        true_names: &mut NameResult,
    ) -> Result<(), CompileError> {
        let name = Path::from_str(path, name_str);
        if visited.contains(&name) {
            return Err(CompileError::NotFound {
                path: name,
                span: span.unwrap(),
            });
        }
        let mut visited = visited.clone();
        visited.insert(name);
        let mut ns_from_wild_cards = Default::default();
        for a in self
            .wild_card_imports
            .get(&path)
            .cloned()
            .into_iter()
            .flatten()
        {
            if a.is_public || path.is_same_as_or_ancestor_of(scope) {
                let m = self.get_module_with_path(
                    a.scope,
                    a.base_path,
                    &a.alias,
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
                    &mut ns_from_wild_cards,
                )?;
            }
        }
        let mut ns = Default::default();
        if let Some(name_entry) = self.name_map.get(&name) {
            for name_alias_entry in name_entry.true_names.clone().into_iter() {
                if name_alias_entry.is_public
                    || path.is_same_as_or_ancestor_of(scope)
                {
                    self.get_true_names_with_path_rec(
                        name_alias_entry.scope,
                        name_alias_entry.base_path,
                        &name_alias_entry.alias,
                        token_map,
                        &visited,
                        &mut ns,
                    )?;
                }
            }
            let name_entry = self.name_map.get(&name).unwrap();
            for v in &name_entry.variables {
                if v.is_public || path.is_same_as_or_ancestor_of(scope) {
                    ns.variables.insert(v.variable_id);
                }
            }
            for v in &name_entry.accessors {
                if v.is_public || path.is_same_as_or_ancestor_of(scope) {
                    ns.accessors.insert((v.constructor, v.field));
                }
            }
            if let Some(d) = &name_entry.data {
                if d.is_public || path.is_same_as_or_ancestor_of(scope) {
                    debug_assert!(ns.data.is_none());
                    ns.data = Some((d.constructor_id, true));
                }
            }
            if let Some(d) = &name_entry.type_ {
                if d.is_public || path.is_same_as_or_ancestor_of(scope) {
                    debug_assert!(ns.type_.is_none());
                    ns.type_ = Some(d.const_or_alias);
                }
            }
            if let Some(d) = &name_entry.interface {
                if d.is_public || path.is_same_as_or_ancestor_of(scope) {
                    debug_assert!(ns.interface.is_none());
                    ns.interface = Some(name);
                }
            }
            if let Some(d) = &name_entry.module {
                if d.is_public || path.is_same_as_or_ancestor_of(scope) {
                    debug_assert!(ns.module.is_none());
                    ns.module = Some(name);
                }
            }
            if let Some(d) = &name_entry.op_precedence {
                if d.is_public || path.is_same_as_or_ancestor_of(scope) {
                    debug_assert!(ns.op_precedence.is_none());
                    ns.op_precedence = Some((d.associativity, d.precedence));
                }
            }
        }
        ns.variables_imported_by_wild_card
            .extend(ns_from_wild_cards.variables);
        ns.variables_imported_by_wild_card
            .extend(ns_from_wild_cards.variables_imported_by_wild_card);
        ns.accessors.extend(ns_from_wild_cards.accessors);
        ns.data.set_if_none(ns_from_wild_cards.data);
        ns.type_.set_if_none(ns_from_wild_cards.type_);
        ns.interface.set_if_none(ns_from_wild_cards.interface);
        ns.module.set_if_none(ns_from_wild_cards.module);
        ns.op_precedence
            .set_if_none(ns_from_wild_cards.op_precedence);
        true_names.variables.extend(ns.variables);
        true_names
            .variables_imported_by_wild_card
            .extend(ns.variables_imported_by_wild_card);
        true_names.accessors.extend(ns.accessors);
        true_names.data.set(ns.data);
        true_names.type_.set(ns.type_);
        true_names.interface.set(ns.interface);
        true_names.module.set(ns.module);
        true_names.op_precedence.set(ns.op_precedence);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn get_module(
        &mut self,
        scope: Path,
        base_path: Path,
        name: &str,
        _token_id: Option<TokenId>,
        span: Option<Span>,
        token_map: &mut TokenMap,
        visited: &FxHashSet<Path>,
    ) -> Result<Path, CompileError> {
        let mut ns = Default::default();
        self.get_true_names_rec(
            scope,
            base_path,
            name,
            span.clone(),
            token_map,
            visited,
            &mut ns,
        )?;
        ns.module.map(Ok).unwrap_or_else(|| {
            Err(CompileError::NotFound {
                path: Path::from_str(base_path, name),
                span: span.unwrap(),
            })
        })
    }

    pub fn get_module_with_path(
        &mut self,
        scope: Path,
        mut base_path: Path,
        mut path: &[parser::StringWithId],
        token_map: &mut TokenMap,
        visited: &FxHashSet<Path>,
    ) -> Result<Path, CompileError> {
        if path.is_empty() {
            Ok(base_path)
        } else {
            if scope == base_path && path[0].0 == "prelude" {
                base_path = Path::prelude();
                path = &path[1..];
            } else if scope == base_path && path[0].0 == "intrinsic" {
                base_path = Path::intrinsic();
                path = &path[1..];
            } else if path[0].0 == "super" {
                token_map.insert(path[0].2, TokenMapEntry::KeyWord);
                base_path = base_path
                    .split()
                    .ok_or(CompileError::TooManySuper {
                        span: path[0].1.clone().unwrap(),
                    })?
                    .0;
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
        scope: Path,
        base_path: Path,
        path: &[parser::StringWithId],
        token_map: &mut TokenMap,
        visited: &FxHashSet<Path>,
        true_names: &mut NameResult,
    ) -> Result<(), CompileError> {
        let base_path = self.get_module_with_path(
            scope,
            base_path,
            &path[..path.len() - 1],
            token_map,
            visited,
        )?;
        let (name, span, token_id) = path.last().unwrap();
        self.get_true_names_rec(
            scope,
            base_path,
            name,
            span.clone(),
            token_map,
            visited,
            true_names,
        )?;
        if let Some(t) = &true_names.type_ {
            match t {
                ConstOrAlias::Const(t, _) => {
                    token_map.insert(*token_id, TokenMapEntry::TypeId(*t));
                }
                ConstOrAlias::Alias(_) => {
                    token_map.insert(*token_id, TokenMapEntry::TypeAlias);
                }
            }
        } else if !true_names.variables.is_empty() {
            token_map.insert(
                *token_id,
                TokenMapEntry::ResolvedIdent(
                    *true_names.variables.iter().next().unwrap(),
                ),
            );
        }
        Ok(())
    }

    fn get_names(
        &mut self,
        scope: Path,
        base_path: Path,
        path: &[parser::StringWithId],
        token_map: &mut TokenMap,
    ) -> Result<(NameResult, Path, Option<Span>, Option<TokenId>), CompileError>
    {
        let visited = Default::default();
        let base_path = self.get_module_with_path(
            scope,
            base_path,
            &path[..path.len() - 1],
            token_map,
            &visited,
        )?;
        let (name, span, token_id) = path.last().unwrap();
        let mut ns = Default::default();
        self.get_true_names_rec(
            scope,
            base_path,
            name,
            span.clone(),
            token_map,
            &FxHashSet::default(),
            &mut ns,
        )?;
        Ok((ns, Path::from_str(base_path, name), span.clone(), *token_id))
    }

    pub fn get_constructor(
        &mut self,
        scope: Path,
        base_path: Path,
        path: &[parser::StringWithId],
        token_map: &mut TokenMap,
    ) -> Result<(Path, ConstructorId), CompileError> {
        let (n, path, span, token_id) =
            self.get_names(scope, base_path, path, token_map)?;
        n.data
            .map(|(id, _)| {
                token_map.insert(token_id, TokenMapEntry::Constructor(id));
                (path, id)
            })
            .ok_or_else(|| CompileError::NotFound {
                path,
                span: span.unwrap(),
            })
    }

    pub fn get_type(
        &mut self,
        scope: Path,
        base_path: Path,
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
            &mut ns,
        )?;
        ns.type_.ok_or_else(|| CompileError::NotFound {
            path: Path::from_str(base_path, name),
            span: span.unwrap(),
        })
    }

    pub fn get_interface(
        &mut self,
        scope: Path,
        base_path: Path,
        path: &[parser::StringWithId],
        token_map: &mut TokenMap,
    ) -> Result<Path, CompileError> {
        let (n, path, span, token_id) =
            self.get_names(scope, base_path, path, token_map)?;
        n.interface
            .map(|a| {
                token_map.insert(token_id, TokenMapEntry::Interface);
                a
            })
            .ok_or_else(|| CompileError::NotFound {
                path,
                span: span.unwrap(),
            })
    }

    pub fn get_op_precedence(
        &mut self,
        scope: Path,
        base_path: Path,
        name: &str,
        span: Option<Span>,
        token_map: &mut TokenMap,
    ) -> Result<(Associativity, i32), CompileError> {
        if name == "|" {
            return Ok(OP_PRECEDENCE["|"]);
        } else if name == "->" {
            return Ok(OP_PRECEDENCE["->"]);
        }
        let mut ns = Default::default();
        self.get_true_names_rec(
            scope,
            base_path,
            name,
            span.clone(),
            token_map,
            &FxHashSet::default(),
            &mut ns,
        )?;
        ns.op_precedence.ok_or_else(|| {
            Path::from_str(base_path, name);
            CompileError::NoOpPrecedenceDecl {
                path: Path::from_str(base_path, name),
                span: span.unwrap(),
            }
        })
    }

    pub fn get_variables(
        &mut self,
        scope: Path,
        path: Path,
        name: &str,
        span: Option<Span>,
        token_map: &mut TokenMap,
        candidates_from_implicit_parameters: &FxHashMap<&str, Vec<DeclId>>,
    ) -> Result<Vec<VariableIdInScope>, CompileError> {
        let mut ns = Default::default();
        self.get_true_names_rec(
            scope,
            path,
            name,
            span.clone(),
            token_map,
            &FxHashSet::default(),
            &mut ns,
        )?;
        let mut names: FxHashSet<VariableIdInScope> = ns
            .variables
            .into_iter()
            .map(|v| VariableIdInScope {
                variable_id: v,
                imported_by_wild_card: false,
            })
            .chain(ns.variables_imported_by_wild_card.into_iter().map(|v| {
                VariableIdInScope {
                    variable_id: v,
                    imported_by_wild_card: true,
                }
            }))
            .collect();
        if let Some((a, imported_by_wild_card)) = ns.data {
            let a = match a {
                ConstructorId::DeclId(d) => VariableId::Constructor(d),
                ConstructorId::Intrinsic(d) => {
                    VariableId::IntrinsicConstructor(d)
                }
            };
            names.insert(VariableIdInScope {
                variable_id: a,
                imported_by_wild_card,
            });
        }
        if scope == path {
            names.extend(
                candidates_from_implicit_parameters
                    .get(name)
                    .into_iter()
                    .flatten()
                    .map(|d| VariableIdInScope {
                        variable_id: VariableId::Local(*d),
                        imported_by_wild_card: false,
                    }),
            );
        }
        if names.is_empty() {
            Err(CompileError::NotFound {
                path: Path::from_str(path, name),
                span: span.unwrap(),
            })
        } else {
            Ok(names.into_iter().collect())
        }
    }

    pub fn get_variables_with_path(
        &mut self,
        scope: Path,
        base_path: Path,
        path: &[parser::StringWithId],
        token_map: &mut TokenMap,
        candidates_from_implicit_parameters: &FxHashMap<&str, Vec<DeclId>>,
    ) -> Result<Vec<VariableIdInScope>, CompileError> {
        let base_path = self.get_module_with_path(
            scope,
            base_path,
            &path[..path.len() - 1],
            token_map,
            &Default::default(),
        )?;
        let (name, span, _token_id) = path.last().unwrap();
        self.get_variables(
            scope,
            base_path,
            name,
            span.clone(),
            token_map,
            candidates_from_implicit_parameters,
        )
    }

    pub fn get_accessor_with_path(
        &mut self,
        scope: Path,
        base_path: Path,
        path: &[parser::StringWithId],
        constructor_id: DeclId,
        token_map: &mut TokenMap,
    ) -> Result<Option<usize>, CompileError> {
        let (n, _, _, _) = self.get_names(scope, base_path, path, token_map)?;
        let names = n
            .accessors
            .into_iter()
            .filter(|(c, _)| *c == constructor_id)
            .collect_vec();
        Ok(if names.is_empty() {
            None
        } else {
            debug_assert_eq!(names.len(), 1);
            Some(names[0].1)
        })
    }

    pub fn get_op_precedence_from_type_id(
        &self,
        type_id: TypeId,
    ) -> Option<(Associativity, i32)> {
        let p = self
            .name_map
            .get(self.type_id_to_name.get(&type_id)?)?
            .op_precedence
            .as_ref()?;
        Some((p.associativity, p.precedence))
    }
}

trait SetOnce {
    fn set(&mut self, other: Self);
    fn set_if_none(&mut self, other: Self);
}

impl<T> SetOnce for Option<T> {
    fn set(&mut self, other: Self) {
        if other.is_some() {
            debug_assert!(self.is_none());
            *self = other;
        }
    }

    fn set_if_none(&mut self, other: Self) {
        if self.is_none() {
            *self = other;
        }
    }
}

impl Default for Imports {
    fn default() -> Self {
        let mut imports = Imports {
            name_map: Default::default(),
            wild_card_imports: Default::default(),
            type_id_to_name: Default::default(),
        };
        for v in IntrinsicVariable::iter() {
            imports.add_variable(
                Path::from_str_intrinsic(v.to_str()),
                VariableId::IntrinsicVariable(v),
                true,
            );
        }
        for v in IntrinsicConstructor::iter() {
            imports.add_data(
                Path::from_str_intrinsic(v.to_str()),
                ConstructorId::Intrinsic(v),
                true,
            );
        }
        for (name, id) in INTRINSIC_TYPES.iter() {
            imports.add_type(
                Path::from_str_intrinsic(name),
                TypeId::Intrinsic(*id),
                true,
                id.parameter_len(),
            );
        }
        for (name, (associativity, precedence)) in OP_PRECEDENCE.iter() {
            imports.add_op_precedence(
                Path::from_str_intrinsic(name),
                *associativity,
                *precedence,
                true,
            );
        }
        imports
    }
}
