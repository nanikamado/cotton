use self::unhashable_type::UnhashableTypeMemo;
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::name_id::Path;
use crate::ast_step2::{types, ConstructorId, TypeId};
use crate::ast_step3::{BasicFunction, DataDecl};
use crate::ast_step4::{
    self, PaddedTypeMap, ReplaceMap, TypeForHash, TypePointer, VariableId,
};
use crate::intrinsics::IntrinsicType;
use fxhash::FxHashMap;
use itertools::Itertools;
use smallvec::{smallvec, SmallVec};
use std::collections::BTreeSet;
use std::fmt::Display;
use std::iter::once;

#[derive(Debug)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: LambdaId,
    pub functions: Vec<Function>,
    pub variable_names: FxHashMap<VariableId, String>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub name: Path,
    pub value: ExprWithType,
    pub decl_id: DeclId,
}

pub type ExprWithType = (Expr, Type);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Default, Clone)]
pub struct Type(BTreeSet<TypeUnit>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum TypeUnit {
    Normal { id: TypeId, args: Vec<Type> },
    Fn(BTreeSet<LambdaId>, Type, Type),
    RecursionPoint(u32),
    Recursive(Type),
}

impl From<TypeUnit> for Type {
    fn from(value: TypeUnit) -> Self {
        Type(once(value).collect())
    }
}

impl FromIterator<TypeUnit> for Type {
    fn from_iter<T: IntoIterator<Item = TypeUnit>>(iter: T) -> Self {
        Type(iter.into_iter().collect())
    }
}

impl Type {
    pub fn iter(&self) -> impl Iterator<Item = &TypeUnit> {
        self.0.iter()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda {
        lambda_id: LambdaId,
        context: Vec<DeclId>,
    },
    Match {
        arms: Vec<FnArm>,
        arguments: Vec<DeclId>,
    },
    Number(String),
    StrLiteral(String),
    Ident {
        variable_id: VariableId,
    },
    Call {
        possible_functions: Vec<LambdaId>,
        f: Box<ExprWithType>,
        a: Box<ExprWithType>,
    },
    DoBlock(Vec<ExprWithType>),
    BasicCall {
        args: Vec<ExprWithType>,
        id: BasicFunction,
    },
    Upcast {
        tag: u32,
        value: Box<Expr>,
    },
    Downcast {
        tag: u32,
        value: Box<Expr>,
    },
}

/// Represents a multi-case pattern which matches if any of the `PatternUnit` in it matches.
/// It should have at least one `PatternUnit`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Pattern {
    pub patterns: Vec<PatternUnit>,
    pub type_: Type,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit {
    I64(String),
    Str(String),
    Constructor {
        id: ConstructorId,
    },
    Binder(DeclId),
    Underscore,
    TypeRestriction(Pattern, types::Type),
    Apply {
        pre_pattern: Pattern,
        function: ExprWithType,
        possible_functions: Vec<LambdaId>,
        post_pattern: Pattern,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm {
    pub pattern: Vec<Pattern>,
    pub expr: ExprWithType,
}

impl Ast {
    pub fn from(ast: ast_step4::Ast) -> Self {
        let mut memo = VariableMemo::new(ast.variable_decl, ast.type_map);
        memo.monomorphize_decl_rec(
            ast.entry_point,
            ast.type_of_entry_point,
            &mut Default::default(),
        );
        let mut variable_names: FxHashMap<_, _> = ast.variable_names;
        for v in &memo.monomorphized_variables {
            variable_names
                .insert(VariableId::Global(v.decl_id), v.name.to_string());
        }
        let v = &memo.monomorphized_variables.last().unwrap().value.0;
        let v = if let Expr::Upcast { tag: _, value } = v {
            value
        } else {
            v
        };
        let lambda_id = if let Expr::Lambda { lambda_id, .. } = v {
            *lambda_id
        } else {
            panic!()
        };
        Self {
            variable_decl: memo.monomorphized_variables,
            data_decl: ast.data_decl,
            entry_point: lambda_id,
            functions: memo
                .functions
                .into_values()
                .map(|f| match f {
                    FunctionEntry::Placeholder(_) => panic!(),
                    FunctionEntry::Function(f) => f,
                })
                .collect(),
            variable_names,
        }
    }
}

pub struct VariableMemo {
    variable_decls: FxHashMap<DeclId, ast_step4::VariableDecl<TypePointer>>,
    monomorphized_variable_map: FxHashMap<(DeclId, TypeForHash), DeclId>,
    monomorphized_variables: Vec<VariableDecl>,
    map: PaddedTypeMap,
    functions: FxHashMap<(u32, TypeForHash), FunctionEntry>,
    unhashable_type_memo: UnhashableTypeMemo,
}

#[derive(Debug)]
pub enum FunctionEntry {
    Placeholder(LambdaId),
    Function(Function),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    pub parameter: DeclId,
    pub parameter_type: Type,
    pub body: ExprWithType,
    pub id: LambdaId,
    pub original_id: u32,
    pub origin_type: TypeForHash,
    pub context: Vec<DeclId>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct LambdaId(pub u32);

impl VariableMemo {
    pub fn new(
        variable_decls: Vec<ast_step4::VariableDecl<TypePointer>>,
        map: PaddedTypeMap,
    ) -> Self {
        VariableMemo {
            variable_decls: variable_decls
                .into_iter()
                .map(|d| (d.decl_id, d))
                .collect(),
            monomorphized_variable_map: Default::default(),
            monomorphized_variables: Default::default(),
            map,
            functions: FxHashMap::default(),
            unhashable_type_memo: UnhashableTypeMemo::default(),
        }
    }

    fn monomorphize_decl_rec(
        &mut self,
        decl_id: DeclId,
        p: TypePointer,
        replace_map: &mut ReplaceMap,
    ) -> DeclId {
        let t = self.map.get_type_with_replace_map(p, replace_map);
        let decl_id_t = (decl_id, t);
        if let Some(d) = self.monomorphized_variable_map.get(&decl_id_t) {
            *d
        } else {
            let (_, t) = decl_id_t;
            let new_decl_id = DeclId::new();
            let d = &self.variable_decls[&decl_id];
            let mut local_variable_replace_map = FxHashMap::default();
            self.monomorphized_variable_map
                .insert((decl_id, t.clone()), new_decl_id);
            let d = VariableDecl {
                name: d.name,
                value: self.expr(
                    d.value.clone(),
                    &t,
                    replace_map,
                    &mut local_variable_replace_map,
                ),
                decl_id: new_decl_id,
            };
            self.monomorphized_variables.push(d);
            new_decl_id
        }
    }

    fn expr(
        &mut self,
        (e, t): ast_step4::ExprWithType,
        global_variable_type: &TypeForHash,
        replace_map: &mut ReplaceMap,
        local_variable_map: &mut FxHashMap<DeclId, DeclId>,
    ) -> ExprWithType {
        debug_assert_ne!(global_variable_type.len(), 0);
        use Expr::*;
        let fixed_t = self.get_type_unhashable_with_replace_map(t, replace_map);
        let e = match e {
            ast_step4::Expr::Lambda {
                lambda_number,
                context,
                parameter,
                parameter_type,
                body,
            } => {
                let parameter =
                    replace_local_decl(parameter, local_variable_map);
                let context = context
                    .into_iter()
                    .map(|d| replace_local_decl(d, local_variable_map))
                    .collect_vec();
                let possible_functions =
                    self.get_possible_functions(t, replace_map);
                let parameter_type = self.get_type_unhashable_with_replace_map(
                    parameter_type,
                    replace_map,
                );
                let f = Function {
                    parameter,
                    parameter_type,
                    body: self.expr(
                        *body,
                        global_variable_type,
                        replace_map,
                        local_variable_map,
                    ),
                    id: LambdaId(0),
                    context: context.clone(),
                    original_id: lambda_number,
                    origin_type: global_variable_type.clone(),
                };
                let e = self
                    .functions
                    .get_mut(&(lambda_number, global_variable_type.clone()))
                    .unwrap();
                let FunctionEntry::Placeholder(id) = *e else {
                    panic!()
                };
                *e = FunctionEntry::Function(Function { id, ..f });
                let lambda_id = id;
                Upcast {
                    tag: possible_functions.binary_search(&lambda_id).unwrap()
                        as u32,
                    value: Box::new(Lambda { context, lambda_id }),
                }
            }
            ast_step4::Expr::Match { arms, arguments } => Match {
                arms: arms
                    .into_iter()
                    .map(|arm| {
                        self.monomorphize_fn_arm(
                            arm,
                            replace_map,
                            global_variable_type,
                            local_variable_map,
                        )
                    })
                    .collect(),
                arguments: arguments
                    .into_iter()
                    .map(|d| replace_local_decl(d, local_variable_map))
                    .collect(),
            },
            ast_step4::Expr::Ident { variable_id } => Ident {
                variable_id: VariableId::Local(replace_local_decl(
                    variable_id,
                    local_variable_map,
                )),
            },
            ast_step4::Expr::GlobalVariable {
                decl_id,
                replace_map: r,
            } => Ident {
                variable_id: VariableId::Global(self.monomorphize_decl_rec(
                    decl_id,
                    t,
                    &mut replace_map.clone().merge(r),
                )),
            },
            ast_step4::Expr::Call(f, a) => {
                let possible_functions: Vec<_> =
                    self.get_possible_functions(f.1, replace_map);
                Call {
                    f: Box::new(self.expr(
                        *f,
                        global_variable_type,
                        replace_map,
                        local_variable_map,
                    )),
                    a: Box::new(self.expr(
                        *a,
                        global_variable_type,
                        replace_map,
                        local_variable_map,
                    )),
                    possible_functions,
                }
            }
            ast_step4::Expr::DoBlock(es) => DoBlock(
                es.into_iter()
                    .map(|e| {
                        self.expr(
                            e,
                            global_variable_type,
                            replace_map,
                            local_variable_map,
                        )
                    })
                    .collect(),
            ),
            ast_step4::Expr::IntrinsicCall {
                args,
                id: BasicFunction::Intrinsic(id),
            } => {
                let rt = id.runtime_return_type();
                assert_eq!(fixed_t, rt);
                let v = BasicCall {
                    args: args
                        .into_iter()
                        .map(|a| {
                            self.expr(
                                a,
                                global_variable_type,
                                replace_map,
                                local_variable_map,
                            )
                        })
                        .collect(),
                    id: BasicFunction::Intrinsic(id),
                };
                if rt.0.len() == 1 {
                    Upcast {
                        tag: 0,
                        value: Box::new(v),
                    }
                } else {
                    v
                }
            }
            ast_step4::Expr::IntrinsicCall {
                args,
                id: BasicFunction::Construction(id),
            } => BasicCall {
                args: args
                    .into_iter()
                    .map(|a| {
                        self.expr(
                            a,
                            global_variable_type,
                            replace_map,
                            local_variable_map,
                        )
                    })
                    .collect(),
                id: BasicFunction::Construction(id),
            }
            .add_tags(&fixed_t, TypeId::from(id)),
            ast_step4::Expr::IntrinsicCall {
                args,
                id:
                    id @ BasicFunction::FieldAccessor {
                        constructor,
                        field: _,
                    },
            } => {
                let a = args.into_iter().next().unwrap();
                let a = self.expr(
                    a,
                    global_variable_type,
                    replace_map,
                    local_variable_map,
                );
                let t = a.1;
                let tags =
                    get_tag_normal(&t, TypeId::DeclId(constructor)).unwrap();
                let a = tags.iter().fold(a.0, |acc, tag| Downcast {
                    tag: *tag,
                    value: Box::new(acc),
                });
                BasicCall {
                    args: vec![(a, t)],
                    id,
                }
            }
            ast_step4::Expr::Number(a) => Number(a)
                .add_tags(&fixed_t, TypeId::Intrinsic(IntrinsicType::I64)),
            ast_step4::Expr::StrLiteral(a) => StrLiteral(a)
                .add_tags(&fixed_t, TypeId::Intrinsic(IntrinsicType::String)),
        };
        (e, fixed_t)
    }

    fn get_possible_functions(
        &mut self,
        p: TypePointer,
        replace_map: &mut ReplaceMap,
    ) -> Vec<LambdaId> {
        let (_, _, fn_id) = self.map.get_fn(p);
        self.map
            .get_lambda_id(fn_id, replace_map)
            .clone()
            .into_iter()
            .map(|id| {
                let t = self.map.get_type_with_replace_map(id.1, replace_map);
                let len = self.functions.len() as u32;
                let e = self
                    .functions
                    .entry((id.0, t))
                    .or_insert(FunctionEntry::Placeholder(LambdaId(len)));
                match e {
                    FunctionEntry::Placeholder(id) => *id,
                    FunctionEntry::Function(f) => f.id,
                }
            })
            .sorted_unstable()
            .collect()
    }

    fn monomorphize_fn_arm(
        &mut self,
        arm: ast_step4::FnArm,
        replace_map: &mut ReplaceMap,
        global_variable_type: &TypeForHash,
        local_variable_replace_map: &mut FxHashMap<DeclId, DeclId>,
    ) -> FnArm {
        FnArm {
            pattern: arm
                .pattern
                .into_iter()
                .map(|p| {
                    self.monomorphize_pattern(
                        p,
                        replace_map,
                        global_variable_type,
                        local_variable_replace_map,
                    )
                })
                .collect(),
            expr: self.expr(
                arm.expr,
                global_variable_type,
                replace_map,
                local_variable_replace_map,
            ),
        }
    }

    fn monomorphize_pattern(
        &mut self,
        pattern: ast_step4::Pattern,
        replace_map: &mut ReplaceMap,
        global_variable_type: &TypeForHash,
        local_variable_map: &mut FxHashMap<DeclId, DeclId>,
    ) -> Pattern {
        let patterns = pattern
            .patterns
            .into_iter()
            .map(|p| {
                use self::PatternUnit::*;
                use ast_step4::PatternUnit;
                match p {
                    PatternUnit::Constructor { id } => Constructor { id },
                    PatternUnit::I64(a) => I64(a),
                    PatternUnit::Str(a) => Str(a),
                    PatternUnit::Binder(id) => {
                        Binder(replace_local_decl(id, local_variable_map))
                    }
                    PatternUnit::Underscore => Underscore,
                    PatternUnit::TypeRestriction(p, t) => TypeRestriction(
                        self.monomorphize_pattern(
                            p,
                            replace_map,
                            global_variable_type,
                            local_variable_map,
                        ),
                        t,
                    ),
                    PatternUnit::Apply {
                        pre_pattern,
                        function,
                        post_pattern,
                    } => {
                        let p = function.1;
                        Apply {
                            pre_pattern: self.monomorphize_pattern(
                                pre_pattern,
                                replace_map,
                                global_variable_type,
                                local_variable_map,
                            ),
                            function: self.expr(
                                function,
                                global_variable_type,
                                replace_map,
                                local_variable_map,
                            ),
                            post_pattern: self.monomorphize_pattern(
                                post_pattern,
                                replace_map,
                                global_variable_type,
                                local_variable_map,
                            ),
                            possible_functions: self
                                .get_possible_functions(p, replace_map),
                        }
                    }
                }
            })
            .collect();
        Pattern {
            patterns,
            type_: self.get_type_unhashable_with_replace_map(
                pattern.type_,
                replace_map,
            ),
        }
    }

    fn get_type_unhashable_with_replace_map(
        &mut self,
        p: TypePointer,
        replace_map: &mut ReplaceMap,
    ) -> Type {
        self.unhashable_type_memo
            .get_type_unhashable_with_replace_map(
                p,
                replace_map,
                &mut self.functions,
                &mut self.map,
            )
    }
}

impl Expr {
    fn add_tags(self, t: &Type, id: TypeId) -> Self {
        get_tag_normal(t, id)
            .unwrap()
            .into_iter()
            .rev()
            .fold(self, |acc, i| Expr::Upcast {
                tag: i,
                value: Box::new(acc),
            })
    }
}

fn replace_local_decl(
    d: DeclId,
    local_variable_replace_map: &mut FxHashMap<DeclId, DeclId>,
) -> DeclId {
    if let Some(d) = local_variable_replace_map.get(&d) {
        *d
    } else {
        let new_d = DeclId::new();
        local_variable_replace_map.insert(d, new_d);
        new_d
    }
}

pub fn get_tag_normal(
    ot: &Type,
    type_id: TypeId,
) -> Option<SmallVec<[u32; 2]>> {
    let mut tag = 0;
    for t in ot.0.iter() {
        use TypeUnit::*;
        match t {
            Normal { id, args: _ } => {
                if *id == type_id {
                    return Some(smallvec![tag]);
                } else {
                    tag += 1;
                }
            }
            Fn(id, _, _) => tag += id.len() as u32,
            RecursionPoint(_) => panic!(),
            Recursive(t) => {
                if let Some(mut in_tag) = get_tag_normal(t, type_id) {
                    in_tag.insert(0, tag);
                    return Some(in_tag);
                } else {
                    tag += 1;
                }
            }
        }
    }
    None
}

impl Display for LambdaId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "la{}", self.0)
    }
}

mod unhashable_type {
    use super::{FunctionEntry, LambdaId};
    use crate::ast_step2::TypeId;
    use crate::ast_step4::{
        PaddedTypeMap, ReplaceMap, Terminal, TypeForHash, TypePointer,
    };
    use crate::ast_step5::{Type, TypeUnit};
    use crate::intrinsics::IntrinsicType;
    use fxhash::{FxHashMap, FxHashSet};
    use std::collections::BTreeSet;
    use std::iter::once;

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Clone)]
    struct LinkedTypeUnhashable {
        ts: BTreeSet<LinkedTypeUnitUnhashable>,
        recursive: bool,
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
    enum LinkedTypeUnitUnhashable {
        Normal {
            id: TypeId,
            args: Vec<LinkedTypeUnhashable>,
        },
        RecursionPoint(u32),
        Pointer(TypePointer),
        LambdaId(super::LambdaId),
    }

    pub struct ReplacePointerResult {
        t: LinkedTypeUnhashable,
        replaced: bool,
        contains_pointer: bool,
    }

    impl LinkedTypeUnhashable {
        fn replace_pointer(
            self,
            from: TypePointer,
            depth: u32,
        ) -> ReplacePointerResult {
            let depth = self.recursive as u32 + depth;
            let mut t = BTreeSet::default();
            let mut replaced = false;
            let mut contains_pointer = false;
            use LinkedTypeUnitUnhashable::*;
            for u in self.ts {
                match u {
                    Pointer(p) if p == from => {
                        t.insert(RecursionPoint(depth));
                        replaced = true;
                        contains_pointer = true;
                    }
                    Pointer(_) => {
                        contains_pointer = true;
                        t.insert(u);
                    }
                    Normal { id, args } => {
                        let args = args
                            .into_iter()
                            .map(|arg| {
                                let r = arg.replace_pointer(from, depth);
                                replaced |= r.replaced;
                                contains_pointer |= r.contains_pointer;
                                r.t
                            })
                            .collect();
                        t.insert(Normal { id, args });
                    }
                    LambdaId(id) => {
                        t.insert(LambdaId(id));
                    }
                    RecursionPoint(_) => {
                        t.insert(u);
                    }
                }
            }
            ReplacePointerResult {
                t: LinkedTypeUnhashable {
                    ts: t,
                    recursive: self.recursive,
                },
                replaced,
                contains_pointer,
            }
        }
    }

    impl From<LinkedTypeUnhashable> for Type {
        fn from(value: LinkedTypeUnhashable) -> Self {
            use TypeUnit::*;
            let t = value
                .ts
                .into_iter()
                .map(|t| match t {
                    LinkedTypeUnitUnhashable::Normal {
                        id: TypeId::Intrinsic(IntrinsicType::Fn),
                        args,
                    } => {
                        debug_assert_eq!(args.len(), 3);
                        let mut args = args.into_iter();
                        let a = args.next().unwrap().into();
                        let b = args.next().unwrap().into();
                        let lambda_t = args.next().unwrap();
                        debug_assert!(!lambda_t.recursive);
                        let lambda_id = lambda_t
                            .ts
                            .into_iter()
                            .map(|id| {
                                if let LinkedTypeUnitUnhashable::LambdaId(
                                    lambda_id,
                                ) = id
                                {
                                    lambda_id
                                } else {
                                    panic!()
                                }
                            })
                            .collect::<BTreeSet<_>>();
                        Fn(lambda_id, a, b)
                    }
                    LinkedTypeUnitUnhashable::Normal { id, args } => {
                        let args = args.into_iter().map(Type::from).collect();
                        Normal { id, args }
                    }
                    LinkedTypeUnitUnhashable::RecursionPoint(d) => {
                        RecursionPoint(d)
                    }
                    LinkedTypeUnitUnhashable::Pointer(_) => panic!(),
                    LinkedTypeUnitUnhashable::LambdaId(_) => panic!(),
                })
                .collect();
            if value.recursive {
                Recursive(t).into()
            } else {
                t
            }
        }
    }

    #[derive(Debug, Default)]
    pub struct UnhashableTypeMemo {
        get_type_memo: FxHashMap<TypePointer, LinkedTypeUnhashable>,
    }

    impl UnhashableTypeMemo {
        pub fn get_type_unhashable_with_replace_map(
            &mut self,
            p: TypePointer,
            replace_map: &mut ReplaceMap,
            function_map: &mut FxHashMap<(u32, TypeForHash), FunctionEntry>,
            map: &mut PaddedTypeMap,
        ) -> Type {
            let p = map.clone_pointer(p, replace_map);
            self.get_type_unhashable(
                p,
                Default::default(),
                replace_map,
                function_map,
                map,
            )
            .into()
        }

        fn get_type_unhashable(
            &mut self,
            p: TypePointer,
            mut trace: FxHashSet<TypePointer>,
            replace_map: &mut ReplaceMap,
            function_map: &mut FxHashMap<(u32, TypeForHash), FunctionEntry>,
            map: &mut PaddedTypeMap,
        ) -> LinkedTypeUnhashable {
            map.dereference_without_find(p);
            if let Some(t) = self.get_type_memo.get(&p) {
                return t.clone();
            }
            if trace.contains(&p) {
                return LinkedTypeUnhashable {
                    ts: once(LinkedTypeUnitUnhashable::Pointer(p)).collect(),
                    recursive: false,
                };
            }
            trace.insert(p);
            let t = match &map.dereference_without_find(p) {
                Terminal::TypeMap(type_map) => {
                    let mut t = Vec::default();
                    for (type_id, normal_type) in &type_map.normals {
                        t.push((*type_id, normal_type.clone()));
                    }
                    LinkedTypeUnhashable {
                        ts: t
                            .into_iter()
                            .map(|(id, args)| {
                                LinkedTypeUnitUnhashable::Normal {
                                    id,
                                    args: args
                                        .into_iter()
                                        .map(|t| {
                                            self.get_type_unhashable(
                                                t,
                                                trace.clone(),
                                                replace_map,
                                                function_map,
                                                map,
                                            )
                                        })
                                        .collect(),
                                }
                            })
                            .collect(),
                        recursive: false,
                    }
                }
                Terminal::LambdaId(ids) => {
                    let mut new_ids = BTreeSet::new();
                    for id in ids.clone() {
                        let t =
                            map.get_type_with_replace_map(id.1, replace_map);
                        let len = function_map.len() as u32;
                        let e = function_map.entry((id.0, t)).or_insert(
                            FunctionEntry::Placeholder(LambdaId(len)),
                        );
                        let id = match e {
                            FunctionEntry::Placeholder(id) => *id,
                            FunctionEntry::Function(f) => f.id,
                        };
                        new_ids.insert(LinkedTypeUnitUnhashable::LambdaId(id));
                    }
                    LinkedTypeUnhashable {
                        ts: new_ids,
                        recursive: false,
                    }
                }
            };
            let r = t.replace_pointer(p, 0);
            let mut t = r.t;
            if r.replaced {
                t.recursive = true;
            };
            if !r.contains_pointer {
                let o = self.get_type_memo.insert(p, t.clone());
                debug_assert!(o.is_none());
            }
            t
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0.len() {
            0 => write!(f, "∅"),
            1 => write!(f, "{}", self.0.iter().next().unwrap()),
            _ => write!(f, "{{{}}}", self.0.iter().format(" | ")),
        }?;
        Ok(())
    }
}

impl Display for TypeUnit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeUnit::*;
        match self {
            Normal { args, id } => {
                debug_assert_ne!(*id, TypeId::Intrinsic(IntrinsicType::Fn));
                if args.is_empty() {
                    write!(f, "{id}")
                } else {
                    write!(f, "{}[{}]", id, args.iter().format(", "))
                }
            }
            RecursionPoint(d) => write!(f, "d{d}"),
            Fn(id, a, b) => {
                let paren = a.0.len() == 1
                    && matches!(a.0.iter().next().unwrap(), Fn(_, _, _));
                let id_paren = id.len() >= 2;
                write!(
                    f,
                    "{}{}{} -{}{}{}-> {b}",
                    if paren { "(" } else { "" },
                    a,
                    if paren { ")" } else { "" },
                    if id_paren { "(" } else { "" },
                    id.iter()
                        .format_with(" | ", |a, f| f(&format_args!("{}", a))),
                    if id_paren { ")" } else { "" },
                )
            }
            Recursive(t) => {
                write!(f, "rec[{}]", t)
            }
        }
    }
}
