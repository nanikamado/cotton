use crate::ast_step1::decl_id::DeclId;
use crate::ast_step2::types::{Type, TypeUnit};
use crate::ast_step2::{self, ApplyPattern, ConstructorId, PatternUnit};
use crate::ast_step3::{self, unwrap_recursive_alias, BasicFunction, FnArm};
use doki::intrinsics::IntrinsicType;
use doki::{self, Block, GlobalVariable, LocalVariable, TypeId, VariableDecl};
use fxhash::FxHashMap;
use itertools::Itertools;

#[derive(Debug, Default)]
struct Env {
    local_variable_map: FxHashMap<DeclId, LocalVariable>,
    global_variable_map: FxHashMap<DeclId, GlobalVariable>,
    data_decl_map: FxHashMap<DeclId, doki::ConstructorId>,
    type_check_fns: FxHashMap<Type, GlobalVariable>,
    build_env: doki::Env,
}

pub fn codegen(ast: ast_step3::Ast) -> String {
    let mut env = Env::default();
    for d in &ast.data_decl {
        let id = env
            .build_env
            .new_constructor(d.field_len, d.name.to_string());
        env.data_decl_map.insert(d.decl_id, id);
    }
    for d in &ast.variable_decls {
        let gid = env.build_env.new_global_variable();
        env.global_variable_map.insert(d.decl_id, gid);
    }
    for d in ast.variable_decls {
        let ret = env.build_env.new_local_variable();
        let mut block = env.build_env.new_block();
        env.expr(d.value, ret, &mut block);
        let d = VariableDecl {
            value: block,
            ret,
            decl_id: env.global_variable_map[&d.decl_id],
            name: d.name.to_string(),
        };
        env.build_env.set_global_variable(d);
    }
    let entry_point = ast
        .entry_point
        .unwrap_or_else(|| panic!("entry point not found"));
    let entry_point = env.global_variable_map[&entry_point];
    env.build_env.gen_c(entry_point)
}

impl Env {
    fn pattern(
        &mut self,
        p: ast_step3::Pattern,
        operand: LocalVariable,
        block: &mut Block,
    ) {
        let mut p = p.0.into_iter();
        let mut b = Block::default();
        self.pattern_unit(p.next().unwrap(), operand, &mut b);
        for p in p {
            let mut b2 = Block::default();
            self.pattern_unit(p, operand, &mut b2);
            b = b.try_catch(b2);
        }
        block.append(b);
    }

    fn pattern_unit(
        &mut self,
        p: PatternUnit<(), ast_step3::Expr>,
        operand: LocalVariable,
        block: &mut Block,
    ) {
        match p {
            PatternUnit::I64(s) => {
                block.test_number(operand, s.to_string());
            }
            PatternUnit::Str(s) => {
                block.test_string(operand, s.to_string());
            }
            PatternUnit::Constructor { id, args } => {
                match id {
                    ConstructorId::DeclId(d) => {
                        block.test_constructor(
                            operand,
                            TypeId::UserDefined(self.data_decl_map[&d]),
                        );
                    }
                    ConstructorId::Intrinsic(d) => {
                        block.test_constructor(
                            operand,
                            TypeId::Intrinsic(d.into()),
                        );
                    }
                }
                if !args.is_empty() {
                    let constructor = if let ConstructorId::DeclId(id) = id {
                        id
                    } else {
                        panic!()
                    };
                    for (field, (a, _)) in args.into_iter().enumerate() {
                        let d = self.build_env.new_local_variable();
                        self.build_env.field_access(
                            d,
                            operand,
                            self.data_decl_map[&constructor],
                            field,
                            block,
                        );
                        self.pattern(a, d, block);
                    }
                }
            }
            PatternUnit::Binder(_, d, _)
            | PatternUnit::ResolvedBinder(d, _) => {
                self.local_variable_map.insert(d, operand);
            }
            PatternUnit::Underscore => (),
            PatternUnit::TypeRestriction(p, t) => {
                let f = self.type_check_fn(&t);
                let fl = self.build_env.new_local_variable();
                self.build_env.global_variable(fl, f, block);
                let v = self.build_env.new_local_variable();
                self.build_env.call(fl, operand, v, block);
                block.test_constructor(
                    v,
                    TypeId::Intrinsic(IntrinsicType::True),
                );
                self.pattern(p, operand, block);
            }
            PatternUnit::Apply(pre_pattern, applications) => {
                self.pattern(*pre_pattern, operand, block);
                for ApplyPattern {
                    function,
                    post_pattern,
                } in applications
                {
                    let f = self.build_env.new_local_variable();
                    self.expr(function, f, block);
                    let o = self.build_env.new_local_variable();
                    self.build_env.call(f, operand, o, block);
                    self.pattern(post_pattern, o, block);
                }
            }
        }
    }

    pub fn fn_arm(
        &mut self,
        arm: FnArm,
        ret: LocalVariable,
        args: &[LocalVariable],
        block: &mut Block,
    ) {
        for (p, operand) in arm.pattern.into_iter().zip_eq(args) {
            self.pattern(p, *operand, block)
        }
        self.expr(arm.expr, ret, block);
    }

    fn expr(
        &mut self,
        e: ast_step3::Expr,
        ret: LocalVariable,
        block: &mut Block,
    ) {
        match e {
            ast_step3::Expr::Lambda(arms) => {
                let param_len = arms[0].pattern.len();
                let mut block = block;
                let mut args = Vec::new();
                let mut ret = ret;
                for _ in 0..param_len {
                    let l = self.build_env.lambda(block, ret);
                    block = l.body;
                    args.push(l.parameter);
                    ret = l.ret;
                }
                if arms.len() == 1 {
                    let arm = arms.into_iter().next().unwrap();
                    self.fn_arm(arm, ret, &args, block);
                } else {
                    let b = arms
                        .into_iter()
                        .map(|arm| {
                            let mut b = Block::default();
                            self.fn_arm(arm, ret, &args, &mut b);
                            b
                        })
                        .reduce(|a, b| a.try_catch(b))
                        .unwrap();
                    block.append(b);
                };
            }
            ast_step3::Expr::Number(s) => {
                self.build_env.i64(ret, s.to_string(), block);
            }
            ast_step3::Expr::StrLiteral(s) => {
                self.build_env.string(ret, s.to_string(), block);
            }
            ast_step3::Expr::Ident {
                name: _,
                variable_id: ast_step3::VariableId::Local(d),
            } => {
                let d = self.local_variable_map[&d];
                self.build_env.local_variable(ret, d, block);
            }
            ast_step3::Expr::Ident {
                name: _,
                variable_id: ast_step3::VariableId::Global(d),
            } => self.build_env.global_variable(
                ret,
                self.global_variable_map[&d],
                block,
            ),
            ast_step3::Expr::Ident {
                name: _,
                variable_id:
                    ast_step3::VariableId::IntrinsicVariable(_)
                    | ast_step3::VariableId::IntrinsicConstructor(_)
                    | ast_step3::VariableId::Constructor(_)
                    | ast_step3::VariableId::FieldAccessor { .. },
            } => {
                panic!()
            }
            ast_step3::Expr::Call(f, a) => {
                let fv = self.build_env.new_local_variable();
                let av = self.build_env.new_local_variable();
                self.expr(*f, fv, block);
                self.expr(*a, av, block);
                self.build_env.call(fv, av, ret, block);
            }
            ast_step3::Expr::DoBlock(mut es) => {
                let e = es.pop().unwrap();
                for e in es {
                    let v = self.build_env.new_local_variable();
                    self.expr(e, v, block);
                }
                self.expr(e, ret, block);
            }
            ast_step3::Expr::IntrinsicCall {
                args,
                id: BasicFunction::Intrinsic(i),
            } => {
                let args = args
                    .into_iter()
                    .map(|a| {
                        let v = self.build_env.new_local_variable();
                        self.expr(a, v, block);
                        v
                    })
                    .collect();
                self.build_env.intrinsic_call(ret, args, i, block);
            }
            ast_step3::Expr::IntrinsicCall {
                args,
                id: BasicFunction::Construction(i),
            } => {
                let args = args
                    .into_iter()
                    .map(|a| {
                        let v = self.build_env.new_local_variable();
                        self.expr(a, v, block);
                        v
                    })
                    .collect();
                match i {
                    ConstructorId::DeclId(id) => {
                        self.build_env.construction(
                            ret,
                            args,
                            self.data_decl_map[&id],
                            block,
                        );
                    }
                    ConstructorId::Intrinsic(id) => {
                        debug_assert!(args.is_empty());
                        self.build_env.intrinsic_construction(ret, id, block);
                    }
                }
            }
            ast_step3::Expr::IntrinsicCall {
                args,
                id: BasicFunction::FieldAccessor { constructor, field },
            } => {
                debug_assert_eq!(args.len(), 1);
                let a = args.into_iter().next().unwrap();
                let arg = self.build_env.new_local_variable();
                self.expr(a, arg, block);
                self.build_env.field_access(
                    ret,
                    arg,
                    self.data_decl_map[&constructor],
                    field,
                    block,
                );
            }
        }
    }

    fn type_check_fn(&mut self, t: &Type) -> GlobalVariable {
        if let Some(v) = self.type_check_fns.get(t) {
            *v
        } else {
            let v = self.build_env.new_global_variable();
            self.type_check_fns.insert(t.clone(), v);
            let ret = self.build_env.new_local_variable();
            let mut block = self.build_env.new_block();
            let l = self.build_env.lambda(&mut block, ret);
            let parameter = l.parameter;
            let body = l.body;
            let fn_ret = l.ret;
            let mut branch = self.build_env.new_block();
            self.build_env.intrinsic_construction(
                fn_ret,
                doki::intrinsics::IntrinsicConstructor::False,
                &mut branch,
            );
            for t in t.iter() {
                match &**t {
                    TypeUnit::Variable(_)
                    | TypeUnit::TypeLevelFn(_)
                    | TypeUnit::TypeLevelApply { .. }
                    | TypeUnit::Restrictions { .. }
                    | TypeUnit::Variance(_, _)
                    | TypeUnit::Const { .. } => panic!(),
                    TypeUnit::RecursiveAlias { body: t } => {
                        let mut prev_branch = self.build_env.new_block();
                        let t = unwrap_recursive_alias(t.clone());
                        let f = self.type_check_fn(&t);
                        let fl = self.build_env.new_local_variable();
                        self.build_env.global_variable(fl, f, &mut prev_branch);
                        let check_result = self.build_env.new_local_variable();
                        self.build_env.call(
                            fl,
                            parameter,
                            check_result,
                            &mut prev_branch,
                        );
                        body.test_constructor(
                            check_result,
                            TypeId::Intrinsic(IntrinsicType::True),
                        );
                        self.build_env.intrinsic_construction(
                            fn_ret,
                            doki::intrinsics::IntrinsicConstructor::True,
                            &mut prev_branch,
                        );
                        branch = prev_branch.try_catch(branch);
                    }
                    TypeUnit::Tuple(a, b) => {
                        let field_types = b.arguments_from_argument_tuple_ref();
                        for id in a.iter() {
                            if let TypeUnit::Const { id } = &**id {
                                let mut prev_branch =
                                    self.build_env.new_block();
                                self.type_check_normal(
                                    parameter,
                                    &mut prev_branch,
                                    *id,
                                    &field_types,
                                );
                                self.build_env.intrinsic_construction(
                                    fn_ret,
                                    doki::intrinsics::IntrinsicConstructor::True,
                                    &mut prev_branch,
                                );
                                branch = prev_branch.try_catch(branch);
                            } else {
                                panic!()
                            }
                        }
                    }
                    TypeUnit::Any => (),
                }
            }
            body.append(branch);
            let d = VariableDecl {
                value: block,
                ret,
                decl_id: v,
                name: "type_check_fn".to_string(),
            };
            self.build_env.set_global_variable(d);
            v
        }
    }

    fn type_check_normal(
        &mut self,
        parameter: LocalVariable,
        block: &mut Block,
        type_id: ast_step2::TypeId,
        field_types: &[&Type],
    ) {
        match type_id {
            ast_step2::TypeId::DeclId(d) => {
                let id = self.data_decl_map[&d];
                block.test_constructor(parameter, TypeId::UserDefined(id));
                for (i, ft) in field_types.iter().enumerate() {
                    let field = self.build_env.new_local_variable();
                    self.build_env.field_access(field, parameter, id, i, block);
                    let checker_g = self.type_check_fn(ft);
                    let checker = self.build_env.new_local_variable();
                    self.build_env.global_variable(checker, checker_g, block);
                    let check_result = self.build_env.new_local_variable();
                    self.build_env.call(checker, field, check_result, block);
                    block.test_constructor(
                        check_result,
                        TypeId::Intrinsic(IntrinsicType::True),
                    );
                }
            }
            ast_step2::TypeId::Intrinsic(d) => {
                debug_assert!(field_types.is_empty());
                block.test_constructor(parameter, TypeId::Intrinsic(d));
            }
            ast_step2::TypeId::FixedVariable(_) => {
                panic!()
            }
        };
    }
}
