use crate::{
    ast1::TypeIdent,
    ast2::{decl_id::DeclId, types::Type, Ast, DataDecl},
    type_check::intrinsics::INTRINSIC_TYPES,
};
use fxhash::FxHashMap;

pub fn resolve_type_names(mut ast: Ast) -> Ast {
    let data_decl_map = mk_data_decl_map(&ast.data_decl);
    ast.variable_decl = ast
        .variable_decl
        .into_iter()
        .map(|mut v| {
            if let Some(mut t) = v.type_annotation {
                t.constructor =
                    type_resolve(t.constructor, &data_decl_map);
                t.requirements.variable_requirements = t
                    .requirements
                    .variable_requirements
                    .into_iter()
                    .map(|(name, t, ident_id)| {
                        (
                            name,
                            type_resolve(t, &data_decl_map),
                            ident_id,
                        )
                    })
                    .collect();
                t.requirements.subtype_relation = t
                    .requirements
                    .subtype_relation
                    .into_iter()
                    .map(|(t1, t2)| {
                        (
                            type_resolve(t1, &data_decl_map),
                            type_resolve(t2, &data_decl_map),
                        )
                    })
                    .collect();
                v.type_annotation = Some(t)
            };
            v
        })
        .collect();
    ast
}

fn mk_data_decl_map<'a>(
    data_decls: &'a [DataDecl],
) -> FxHashMap<&'a str, DeclId> {
    let mut m = FxHashMap::default();
    for decl in data_decls {
        m.insert(&decl.name[..], decl.decl_id);
    }
    m
}

fn get_type_id(
    name: &str,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> TypeIdent {
    if let Some(id) = data_decl_map.get(name) {
        TypeIdent::DeclId(*id, name.to_string())
    } else if let Some(i) = INTRINSIC_TYPES.get(name) {
        TypeIdent::Intrinsic(*i)
    } else {
        panic!("{:?} not fould", name)
    }
}

pub fn type_resolve(
    t: Type,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> Type {
    t.into_iter()
        .map(|t| {
            use crate::ast2::types::TypeUnit::*;
            match t {
                Normal { name, args, .. } => {
                    let id = get_type_id(&name[..], data_decl_map);
                    Normal { name, args, id }
                }
                Fn(t1, t2) => Fn(
                    type_resolve(t1, data_decl_map),
                    type_resolve(t2, data_decl_map),
                ),
                RecursiveAlias { alias, body } => RecursiveAlias {
                    alias,
                    body: type_resolve(body, data_decl_map),
                },
                v => v,
            }
        })
        .collect()
}
