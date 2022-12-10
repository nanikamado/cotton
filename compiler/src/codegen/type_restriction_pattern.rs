use crate::{
    ast_step2::{
        collect_tuple_rev,
        types::{self, merge_vec, TypeVariable},
    },
    codegen::convert_name,
};
use itertools::Itertools;

pub const IS_INSTANCE_OF: &str = r#"const util = require('util');
    let is_instance_of = (v, t, call_stack) =>
      Array.isArray(t)
         ? t.some((a) => is_instance_of(v, a, call_stack))
         : is_instance_of_unit(v, t, call_stack);
    let is_instance_of_unit = (v, t, call_stack) => {
      if (t.type == "normal") {
        return (
          t[0] == 'I64' && typeof v == 'number' ||
          t[0] == 'String' && typeof v == 'string' ||
          t[0] == v.name &&
          [...t[1].keys()].every((i) =>
            is_instance_of(v[i], t[1][i], call_stack)
          )
        );
      } else if (t.type == "type_level_apply") {
        return is_instance_of(v, t[0], call_stack.concat([t[1]]));
      } else if (t.type == "argument") {
        return is_instance_of(v, call_stack[call_stack.length - 1 - t[0]], call_stack.slice(0, -1));
      } else {
        $$unexpected();
      }
    };"#;

impl types::Type {
    pub fn type_to_js_obj(&self) -> (String, Vec<Vec<Vec<u8>>>) {
        fn add_all(recursive_point_accessor: &mut [Vec<Vec<u8>>], s: u8) {
            for acs in recursive_point_accessor.iter_mut() {
                for ac in acs.iter_mut() {
                    ac.push(s);
                }
            }
        }

        fn merge_recursive_point_accessors(
            a: Vec<Vec<Vec<u8>>>,
            b: Vec<Vec<Vec<u8>>>,
        ) -> Vec<Vec<Vec<u8>>> {
            a.into_iter()
                .zip_longest(b)
                .map(|ab| match ab {
                    itertools::EitherOrBoth::Both(a, b) => merge_vec(a, b),
                    itertools::EitherOrBoth::Left(a)
                    | itertools::EitherOrBoth::Right(a) => a,
                })
                .collect()
        }

        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum IndexableEntityKind {
            RecursiveAlias,
            TypeLevelFn,
        }

        fn type_to_js_obj_rec(
            t: &types::Type,
            indexable_entries: &Vec<IndexableEntityKind>,
        ) -> (String, Vec<Vec<Vec<u8>>>) {
            let mut recursive_point_accessor = Vec::new();
            let mut cs = Vec::new();
            for t in t.iter() {
                match &**t {
                    types::TypeUnit::Fn(a, b) => {
                        let (a, mut r1) =
                            type_to_js_obj_rec(a, indexable_entries);
                        add_all(&mut r1, 0);
                        let (b, mut r2) =
                            type_to_js_obj_rec(b, indexable_entries);
                        add_all(&mut r2, 1);
                        let mut r = merge_recursive_point_accessors(r1, r2);
                        let c = format!(r#"{{type:"fn",0:{},1:{}}}"#, a, b);
                        add_all(&mut r, cs.len() as u8);
                        recursive_point_accessor =
                            merge_recursive_point_accessors(
                                recursive_point_accessor,
                                r,
                            );
                        cs.push(c);
                    }
                    types::TypeUnit::Variable(TypeVariable::Normal(v)) => {
                        let c = format!(
                            r#"{{type:"variable",0:{}}}"#,
                            TypeVariable::Normal(*v)
                        );
                        cs.push(c);
                    }
                    types::TypeUnit::Variable(
                        TypeVariable::RecursiveIndex(n),
                    ) => {
                        recursive_point_accessor.resize(n + 1, Vec::new());
                        recursive_point_accessor[*n].push(vec![cs.len() as u8]);
                        let c = match indexable_entries
                            [indexable_entries.len() - *n - 1]
                        {
                            IndexableEntityKind::RecursiveAlias => {
                                format!(r#""should be replaced ({})""#, n)
                            }
                            IndexableEntityKind::TypeLevelFn => {
                                let count = indexable_entries
                                    [indexable_entries.len() - *n..]
                                    .iter()
                                    .filter(|a| {
                                        **a == IndexableEntityKind::TypeLevelFn
                                    })
                                    .count();
                                format!(r#"{{type:"argument",0:{}}}"#, count)
                            }
                        };
                        cs.push(c);
                    }
                    types::TypeUnit::RecursiveAlias { body } => {
                        let mut indexable_entries = indexable_entries.clone();
                        indexable_entries
                            .push(IndexableEntityKind::RecursiveAlias);
                        let (body, mut r) =
                            type_to_js_obj_rec(body, &indexable_entries);
                        let c = format!(
                            "(()=>{{const a = {};\
                            {};return a}})()",
                            body,
                            r[0].iter().format_with("", |a, f| f(
                                &format_args!(
                                    "a{} = a;",
                                    a.iter().rev().format_with("", |a, f| f(
                                        &format_args!("[{a}]")
                                    ))
                                )
                            ))
                        );
                        r.remove(0);
                        add_all(&mut r, cs.len() as u8);
                        recursive_point_accessor =
                            merge_recursive_point_accessors(
                                recursive_point_accessor,
                                r,
                            );
                        cs.push(c);
                    }
                    types::TypeUnit::TypeLevelFn(body) => {
                        let mut indexable_entries = indexable_entries.clone();
                        indexable_entries
                            .push(IndexableEntityKind::TypeLevelFn);
                        let (body, mut r) =
                            type_to_js_obj_rec(body, &indexable_entries);
                        if !r.is_empty() {
                            r.remove(0);
                        }
                        add_all(&mut r, cs.len() as u8);
                        recursive_point_accessor =
                            merge_recursive_point_accessors(
                                recursive_point_accessor,
                                r,
                            );
                        cs.push(body.to_string());
                    }
                    types::TypeUnit::TypeLevelApply { f, a } => {
                        let (f, mut r1) =
                            type_to_js_obj_rec(f, indexable_entries);
                        add_all(&mut r1, 0);
                        let (a, mut r2) =
                            type_to_js_obj_rec(a, indexable_entries);
                        add_all(&mut r2, 1);
                        let mut r = merge_recursive_point_accessors(r1, r2);
                        add_all(&mut r, cs.len() as u8);
                        recursive_point_accessor =
                            merge_recursive_point_accessors(
                                recursive_point_accessor,
                                r,
                            );
                        cs.push(format!(
                            r#"{{type:"type_level_apply",0:{},1:{}}}"#,
                            f, a
                        ));
                    }
                    types::TypeUnit::Restrictions { .. } => {
                        unimplemented!()
                    }
                    types::TypeUnit::Const { .. } => panic!(),
                    types::TypeUnit::Tuple(a, ts) => {
                        let types::TypeMatchableRef::Const { id } = a.matchable_ref()
                    else {
                        panic!()
                    };
                        use crate::ast_step2::TypeId::*;
                        let a = match id {
                            DeclId(decl_id) => {
                                format!(
                                    r#""${}${}""#,
                                    decl_id,
                                    convert_name(&id.to_string())
                                )
                            }
                            Intrinsic(_) => {
                                format!(r#""{}""#, id)
                            }
                            FixedVariable(_) => unimplemented!(),
                        };
                        let ts = collect_tuple_rev(ts);
                        for tail_rev in ts {
                            let mut tail_new =
                                Vec::with_capacity(tail_rev.len());
                            let mut r_out = Vec::new();
                            for (i, t) in tail_rev.iter().rev().enumerate() {
                                let (a, mut r_in) =
                                    type_to_js_obj_rec(t, indexable_entries);
                                add_all(&mut r_in, i as u8);
                                r_out = merge_recursive_point_accessors(
                                    r_out, r_in,
                                );
                                tail_new.push(a);
                            }
                            let c = format!(
                                r#"{{type:"normal",0:{},1:[{}]}}"#,
                                a,
                                tail_new.iter().format(",")
                            );
                            add_all(&mut r_out, 1);
                            add_all(&mut r_out, cs.len() as u8);
                            recursive_point_accessor =
                                merge_recursive_point_accessors(
                                    recursive_point_accessor,
                                    r_out,
                                );
                            cs.push(c);
                        }
                    }
                }
            }
            (
                format!("[{}]", cs.iter().format(", ")),
                recursive_point_accessor,
            )
        }

        type_to_js_obj_rec(self, &Vec::new())
    }
}
