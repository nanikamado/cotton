use super::imports::Imports;
use super::types::{Type, TypeUnit, TypeVariable};
use super::{Env, ModulePath};
use crate::ast_step1::name_id::Name;
use crate::ast_step1::token_map::{TokenMap, TokenMapEntry};
use crate::ast_step1::{self, TypeAliasDecl};
use crate::ast_step2::type_to_type;
use crate::ast_step2::types::TypeConstructor;
use crate::errors::CompileError;
use fxhash::FxHashMap;
use itertools::Itertools;
use parser::token_id::TokenId;

#[derive(Debug, Clone)]
enum AliasComputation {
    Unaliased(Type),
    NotUnaliased,
}

#[derive(Debug, Clone, Default)]
pub struct TypeAliasMap<'a>(FxHashMap<Name, AliasEntry<'a>>);

#[derive(Debug, Clone)]
struct AliasEntry<'a> {
    type_: ast_step1::Type<'a>,
    type_variables: ast_step1::Forall<'a>,
    alias_computation: AliasComputation,
    base_path: Name,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchMode {
    Normal,
    Alias,
    AliasSub,
}

impl<'a> Env<'a, '_> {
    pub fn get_type_from_alias(
        &mut self,
        name: (Name, Option<TokenId>),
        type_variable_names: &FxHashMap<Name, TypeVariable>,
        search_type: SearchMode,
    ) -> Result<Option<Type>, CompileError> {
        if let Some(t) = type_variable_names.get(&name.0) {
            self.token_map.insert(name.1, TokenMapEntry::TypeAlias);
            return Ok(Some(TypeUnit::Variable(*t).into()));
        }
        let Some(alias) = self.type_alias_map.0.get(&name.0).cloned() else {
            return Ok(None);
        };
        Ok(match (alias.alias_computation, search_type) {
            (AliasComputation::Unaliased(t), SearchMode::Alias) => {
                self.token_map.insert(name.1, TokenMapEntry::TypeAlias);
                Some(t)
            }
            (_, _) => {
                let mut type_variable_names: FxHashMap<Name, TypeVariable> =
                    type_variable_names
                        .clone()
                        .into_iter()
                        .map(|(s, v)| {
                            (
                                s,
                                v.increment_recursive_index(
                                    1 + alias
                                        .type_variables
                                        .type_variables
                                        .len()
                                        as i32,
                                ),
                            )
                        })
                        .collect();
                type_variable_names.insert(
                    name.0,
                    TypeVariable::RecursiveIndex(
                        alias.type_variables.type_variables.len(),
                    ),
                );
                let forall = alias
                    .type_variables
                    .type_variables
                    .iter()
                    .map(|(s, interfaces)| {
                        let v = TypeVariable::new();
                        self.token_map.insert(s.2, TokenMapEntry::TypeVariable);
                        for (_, _, id) in interfaces {
                            self.token_map
                                .insert(*id, TokenMapEntry::Interface);
                        }
                        type_variable_names
                            .insert(Name::from_str(alias.base_path, s.0), v);
                        v
                    })
                    .collect_vec();
                let mut t = type_to_type(
                    &alias.type_,
                    alias.base_path,
                    &type_variable_names,
                    search_type,
                    self,
                )?;
                self.token_map.insert(name.1, TokenMapEntry::TypeAlias);
                for v in forall.into_iter().rev() {
                    t = TypeUnit::TypeLevelFn(
                        t.replace_num(
                            v,
                            &TypeUnit::Variable(TypeVariable::RecursiveIndex(
                                0,
                            ))
                            .into(),
                        ),
                    )
                    .into();
                }
                let t = if t.contains_variable(TypeVariable::RecursiveIndex(0))
                {
                    TypeUnit::RecursiveAlias { body: t }.into()
                } else {
                    t.increment_recursive_index(0, -1)
                };
                if search_type == SearchMode::Alias {
                    self.type_alias_map
                        .0
                        .get_mut(&name.0)
                        .unwrap()
                        .alias_computation =
                        AliasComputation::Unaliased(t.clone());
                }
                Some(t)
            }
        })
    }
}

impl<'a> TypeAliasMap<'a> {
    pub fn add_decls(
        &mut self,
        type_alias_decls: &[TypeAliasDecl<'a>],
        token_map: &mut TokenMap,
        module_path: ModulePath,
        imports: &mut Imports,
    ) {
        self.0.extend(type_alias_decls.iter().map(|a| {
            token_map.insert(a.name.2, TokenMapEntry::TypeAlias);
            let name = Name::from_str(module_path, a.name.0);
            imports.add_type_alias(name, a.is_public);
            (
                name,
                AliasEntry {
                    type_: a.body.0.clone(),
                    type_variables: a.body.1.clone(),
                    alias_computation: AliasComputation::NotUnaliased,
                    base_path: module_path,
                },
            )
        }));
    }
}
