use super::imports::Imports;
use super::types::{Type, TypeUnit, TypeVariable};
use super::{Env, ModulePath};
use crate::ast_step1::name_id::Path;
use crate::ast_step1::token_map::{TokenMap, TokenMapEntry};
use crate::ast_step1::{self, TypeAliasDecl};
use crate::ast_step2::type_to_type;
use crate::ast_step2::types::TypeConstructor;
use crate::errors::CompileError;
use fxhash::FxHashMap;
use parser::token_id::TokenId;

#[derive(Debug, Clone)]
enum AliasComputation {
    Unaliased(Type),
    NotUnaliased,
}

#[derive(Debug, Clone, Default)]
pub struct TypeAliasMap<'a>(FxHashMap<Path, AliasEntry<'a>>);

#[derive(Debug, Clone)]
struct AliasEntry<'a> {
    type_: ast_step1::Type<'a>,
    alias_computation: AliasComputation,
    base_path: Path,
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
        name: (Path, Option<TokenId>),
        type_variable_names: &FxHashMap<Path, TypeVariable>,
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
                let mut type_variable_names = type_variable_names.clone();
                let v = TypeVariable::new();
                type_variable_names.insert(name.0, v);
                let t = type_to_type(
                    &alias.type_,
                    alias.base_path,
                    &type_variable_names,
                    search_type,
                    self,
                )?;
                self.token_map.insert(name.1, TokenMapEntry::TypeAlias);
                let t = if t.contains_variable(v) {
                    TypeUnit::RecursiveAlias {
                        body: t.replace_num(
                            v,
                            &TypeUnit::Variable(TypeVariable::RecursiveIndex(
                                0,
                            ))
                            .into(),
                        ),
                    }
                    .into()
                } else {
                    t
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
            let name = Path::from_str(module_path, a.name.0);
            imports.add_type_alias(name, a.is_public);
            (
                name,
                AliasEntry {
                    type_: a.body.clone(),
                    alias_computation: AliasComputation::NotUnaliased,
                    base_path: module_path,
                },
            )
        }));
    }
}
