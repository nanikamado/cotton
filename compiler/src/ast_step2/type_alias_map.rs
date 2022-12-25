use super::{
    types::{Type, TypeUnit, TypeVariable},
    ModulePath,
};
use crate::{
    ast_step1::{
        self,
        decl_id::DeclId,
        name_id::Name,
        token_map::{TokenMap, TokenMapEntry},
        TypeAliasDecl,
    },
    ast_step2::{type_to_type, types::TypeConstructor},
};
use fxhash::FxHashMap;
use itertools::Itertools;
use parser::token_id::TokenId;

#[derive(Debug, Clone)]
enum AliasComputation {
    Unaliased(Type),
    NotUnaliased,
}

#[derive(Debug, Clone, Default)]
pub struct TypeAliasMap<'a>(
    FxHashMap<
        Name,
        (
            (ast_step1::Type<'a>, ast_step1::Forall<'a>),
            AliasComputation,
        ),
    >,
);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchMode {
    Normal,
    Alias,
    AliasSub,
}

impl<'a> TypeAliasMap<'a> {
    pub fn get(
        &mut self,
        name: (Name, Option<TokenId>),
        data_decl_map: &FxHashMap<Name, DeclId>,
        type_variable_names: &FxHashMap<Name, TypeVariable>,
        search_type: SearchMode,
        token_map: &mut TokenMap,
    ) -> Option<Type> {
        debug_assert_ne!(search_type, SearchMode::Normal);
        if let Some(t) = type_variable_names.get(&name.0) {
            token_map.insert(name.1, TokenMapEntry::TypeAlias);
            return Some(TypeUnit::Variable(*t).into());
        }
        let alias = self.0.get(&name.0)?;
        Some(match (alias, search_type) {
            ((_, AliasComputation::Unaliased(t)), SearchMode::Alias) => {
                token_map.insert(name.1, TokenMapEntry::TypeAlias);
                t.clone()
            }
            ((t, _), _) => {
                let mut type_variable_names: FxHashMap<Name, TypeVariable> =
                    type_variable_names
                        .clone()
                        .into_iter()
                        .map(|(s, v)| {
                            (
                                s,
                                v.increment_recursive_index(
                                    1 + t.1.type_variables.len() as i32,
                                ),
                            )
                        })
                        .collect();
                type_variable_names.insert(
                    name.0,
                    TypeVariable::RecursiveIndex(t.1.type_variables.len()),
                );
                let forall = t
                    .1
                    .clone()
                    .type_variables
                    .into_iter()
                    .map(|(s, interfaces)| {
                        let v = TypeVariable::new();
                        token_map.insert(s.1, TokenMapEntry::TypeVariable);
                        for (_, id) in interfaces {
                            token_map.insert(id, TokenMapEntry::Interface);
                        }
                        type_variable_names.insert(Name::from_str_type(s.0), v);
                        v
                    })
                    .collect_vec();
                let mut t = type_to_type(
                    &t.0.clone(),
                    data_decl_map,
                    &type_variable_names,
                    self,
                    search_type,
                    token_map,
                );
                token_map.insert(name.1, TokenMapEntry::TypeAlias);
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
                    self.0.get_mut(&name.0).unwrap().1 =
                        AliasComputation::Unaliased(t.clone());
                }
                t
            }
        })
    }

    pub fn add_decls(
        &mut self,
        type_alias_decls: &[TypeAliasDecl<'a>],
        token_map: &mut TokenMap,
        module_path: ModulePath,
    ) {
        self.0.extend(type_alias_decls.iter().map(|a| {
            token_map.insert(a.name.1, TokenMapEntry::TypeAlias);
            (
                Name::from_str(module_path, a.name.0),
                (a.body.clone(), AliasComputation::NotUnaliased),
            )
        }));
    }
}
