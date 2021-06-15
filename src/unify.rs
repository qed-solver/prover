use scopeguard::defer;
use z3::ast::*;
use z3::*;

use crate::evaluate::normal::Application;
use crate::evaluate::shared::{Entry, Env, Expr, Predicate};
use crate::evaluate::stable;

fn trans_expr<'a>(ctx: &'a Context, expr: Expr, env: &'a Env<Dynamic>) -> Int<'a> {
	match expr {
		Expr::Var(v) => env.get(v).as_int().unwrap(),
		Expr::Op(op, args) => {
			if args.is_empty() {
				let num = op.parse().unwrap();
				Int::from_i64(ctx, num)
			} else {
				let args: Vec<_> = args.into_iter().map(|arg| trans_expr(ctx, arg, env)).collect();
				match op.as_str() {
					"+" => Int::add(ctx, args.iter().collect::<Vec<_>>().as_slice()),
					"-" => Int::sub(ctx, args.iter().collect::<Vec<_>>().as_slice()),
					"*" => Int::mul(ctx, args.iter().collect::<Vec<_>>().as_slice()),
					"/" => args[0].div(&args[1]),
					"%" => args[0].modulo(&args[1]),
					op => {
						let domain: Vec<_> = args.iter().map(|_| Sort::int(ctx)).collect();
						let args: Vec<_> = args.iter().map(|int| Dynamic::from_ast(int)).collect();
						let f = FuncDecl::new(
							ctx,
							op,
							domain.iter().collect::<Vec<_>>().as_slice(),
							&Sort::int(ctx),
						);
						f.apply(args.iter().collect::<Vec<_>>().as_slice()).as_int().unwrap()
					},
				}
			}
		},
	}
}

fn trans_pred<'a>(ctx: &'a Context, pred: Predicate, env: &'a Env<Dynamic>) -> Bool<'a> {
	match pred {
		Predicate::Eq(e1, e2) => trans_expr(ctx, e1, env)._eq(&trans_expr(ctx, e2, env)),
		Predicate::Pred(pred, args) => {
			let args: Vec<_> = args.into_iter().map(|arg| trans_expr(ctx, arg, env)).collect();
			match pred.as_str() {
				">" => args[0].gt(&args[1]),
				"<" => args[0].lt(&args[1]),
				">=" => args[0].ge(&args[1]),
				"<=" => args[0].le(&args[1]),
				"=" => args[0]._eq(&args[1]),
				pred => {
					let domain: Vec<_> = args.iter().map(|_| Sort::int(ctx)).collect();
					let args: Vec<_> = args.iter().map(|int| Dynamic::from_ast(int)).collect();
					let f = FuncDecl::new(
						ctx,
						pred,
						&domain.iter().collect::<Vec<_>>(),
						&Sort::bool(ctx),
					);
					f.apply(&args.iter().collect::<Vec<_>>()).as_bool().unwrap()
				},
			}
		},
		_ => Bool::from_bool(ctx, true),
	}
}

fn trans_preds<'a>(ctx: &'a Context, preds: &[Predicate], env: &'a Env<Dynamic>) -> Bool<'a> {
	let preds: Vec<_> = preds.iter().map(|pred| trans_pred(ctx, pred.clone(), env)).collect();
	Bool::and(ctx, &preds.iter().collect::<Vec<_>>())
}

fn trans_apps<'a>(ctx: &'a Context, apps: &[Application], env: &'a Env<Dynamic>) -> Int<'a> {
	if apps.is_empty() {
		return Int::from_i64(ctx, 1);
	}
	let apps: Vec<_> = apps
		.iter()
		.map(|app| {
			let domain: Vec<_> = app.args.iter().map(|_| Sort::int(ctx)).collect();
			let args: Vec<_> = app.args.iter().map(|v| env.get(*v)).collect();
			let f = FuncDecl::new(
				ctx,
				app.table.0.to_string(),
				&domain.iter().collect::<Vec<_>>(),
				&Sort::int(ctx),
			);
			f.apply(&args).as_int().unwrap()
		})
		.collect();
	Int::mul(ctx, &apps.iter().collect::<Vec<_>>())
}

fn trans_apps_squashed<'a>(
	ctx: &'a Context,
	apps: &[Application],
	env: &'a Env<Dynamic>,
) -> Bool<'a> {
	if apps.is_empty() {
		return Bool::from_bool(ctx, true);
	}
	let apps: Vec<_> = apps
		.iter()
		.map(|app| {
			let domain: Vec<_> = app.args.iter().map(|_| Sort::int(ctx)).collect();
			let args: Vec<_> = app.args.iter().map(|v| env.get(*v)).collect();
			let f = FuncDecl::new(
				ctx,
				app.table.0.to_string(),
				&domain.iter().collect::<Vec<_>>(),
				&Sort::bool(ctx),
			);
			f.apply(&args).as_bool().unwrap()
		})
		.collect();
	Bool::and(ctx, &apps.iter().collect::<Vec<_>>())
}

fn include<'a>(
	solver: &'a Solver,
	t1: &stable::Term,
	t2: &stable::Term,
	env1: &'a Env<Dynamic>,
	env2: &'a Env<Dynamic>,
) -> bool {
	solver.push();
	defer!(solver.pop(1));
	let ctx = solver.get_context();
	let mut env1 = env1.clone();
	env1.extend(t1.scopes.iter().map(|ty| Int::fresh_const(ctx, "v").into()));
	let mut env2 = env2.clone();
	env2.extend(t2.scopes.iter().map(|ty| Int::fresh_const(ctx, "v").into()));
	let preds1 = trans_preds(ctx, &t1.preds, &env1);
	let preds2 = trans_preds(ctx, &t2.preds, &env2);
	solver.assert(&preds2.implies(&preds1).not());
	if solver.check() != SatResult::Unsat {
		return false;
	}
	let apps1 = trans_apps_squashed(ctx, &t1.apps, &env1);
	let apps2 = trans_apps_squashed(ctx, &t2.apps, &env2);
	solver.assert(&apps2.implies(&apps1).not());
	if solver.check() != SatResult::Unsat {
		return false;
	}
	match (&t1.not, &t2.not) {
		(Some(n1), Some(n2)) if !unify_impl(solver, n1, n2, &env1, &env2, true) => return false,
		(None, Some(_)) => return false,
		_ => {},
	}
	match (&t1.squash, &t2.squash) {
		(Some(n1), Some(n2)) if !unify_impl(solver, n1, n2, &env1, &env2, true) => return false,
		(None, Some(_)) => return false,
		_ => {},
	}
	true
}

fn min_squash<'a>(
	solver: &'a Solver,
	uexp: &stable::UExpr,
	env: &'a Env<Dynamic>,
) -> stable::UExpr {
	for t1 in &uexp.0 {
		if uexp.0.iter().all(|t2| include(solver, t1, t2, env, env)) {
			return stable::UExpr(vec![t1.clone()]);
		}
	}
	uexp.clone()
}

pub fn unify(exp1: &stable::UExpr, exp2: &stable::UExpr, env: &Env<Entry>) -> bool {
	let cfg = Config::new();
	let ctx = Context::new(&cfg);
	let env = Env::new(
		env.entries
			.iter()
			.map(|entry| match entry {
				Entry::Value(v, ty) => Int::fresh_const(&ctx, "v").into(),
				Entry::Table(v, sch) => Int::from_i64(&ctx, 0).into(),
			})
			.collect(),
	);
	let solver = Solver::new(&ctx);
	unify_impl(&solver, exp1, exp2, &env, &env, false)
}

fn unify_impl(
	solver: &Solver,
	exp1: &stable::UExpr,
	exp2: &stable::UExpr,
	env1: &Env<Dynamic>,
	env2: &Env<Dynamic>,
	squashed: bool,
) -> bool {
	let terms1 = exp1.0.clone();
	let mut terms2 = exp2.0.clone();
	terms1.iter().all(|t1| {
		(0..terms2.len()).any(|i| {
			let t2 = &terms2[i];
			let unifies = unify_term(solver, t1, t2, env1, env2, squashed);
			if unifies {
				terms2.swap_remove(i);
			}
			unifies
		})
	})
}

fn unify_term(
	solver: &Solver,
	t1: &stable::Term,
	t2: &stable::Term,
	env1: &Env<Dynamic>,
	env2: &Env<Dynamic>,
	squashed: bool,
) -> bool {
	solver.push();
	defer!(solver.pop(1));
	let ctx = solver.get_context();
	let mut env1 = env1.clone();
	env1.extend(t1.scopes.iter().map(|ty| Int::fresh_const(ctx, "v").into()));
	let mut env2 = env2.clone();
	env2.extend(t2.scopes.iter().map(|ty| Int::fresh_const(ctx, "v").into()));
	let preds1 = trans_preds(ctx, &t1.preds, &env1);
	let preds2 = trans_preds(ctx, &t2.preds, &env2);
	solver.assert(&preds1.iff(&preds2).not());
	if solver.check() != SatResult::Unsat {
		return false;
	}
	if squashed {
		let apps1 = trans_apps_squashed(ctx, &t1.apps, &env1);
		let apps2 = trans_apps_squashed(ctx, &t2.apps, &env2);
		solver.assert(&apps1.iff(&apps2).not());
	} else {
		let apps1 = trans_apps(ctx, &t1.apps, &env1);
		let apps2 = trans_apps(ctx, &t2.apps, &env2);
		solver.assert(&apps1._eq(&apps2).not());
	}
	if solver.check() != SatResult::Unsat {
		return false;
	}
	match (&t1.not, &t2.not) {
		(Some(n1), Some(n2)) if unify_impl(solver, n1, n2, &env1, &env2, squashed) => (),
		(None, None) => (),
		_ => return false,
	}
	match (&t1.squash, &t2.squash) {
		(Some(n1), Some(n2)) => {
			if !unify_impl(
				solver,
				&min_squash(solver, n1, &env1),
				&min_squash(solver, n2, &env2),
				&env1,
				&env2,
				true,
			) {
				return false;
			}
		},
		(None, None) => (),
		_ => return false,
	}
	true
}
