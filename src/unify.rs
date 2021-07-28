use itertools::{Either, Itertools};
use scopeguard::defer;
use z3::ast::*;
use z3::*;

use crate::evaluate::normal::Application;
use crate::evaluate::shared::{Entry, Env, Expr, Predicate};
use crate::evaluate::stable;

fn trans_expr<'a>(ctx: &'a Context, expr: Expr, env: &Env<Dynamic<'a>>) -> Int<'a> {
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

fn trans_pred<'a>(ctx: &'a Context, pred: Predicate, env: &Env<Dynamic<'a>>) -> Bool<'a> {
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

fn trans_preds<'a>(ctx: &'a Context, preds: &[Predicate], env: &Env<Dynamic<'a>>) -> Bool<'a> {
	let preds: Vec<_> = preds.iter().map(|pred| trans_pred(ctx, pred.clone(), env)).collect();
	Bool::and(ctx, &preds.iter().collect::<Vec<_>>())
}

fn trans_apps<'a>(ctx: &'a Context, apps: &[Application], env: &Env<Dynamic<'a>>) -> Int<'a> {
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
	env: &Env<Dynamic<'a>>,
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

fn trans_squashed_term<'a>(
	ctx: &'a Context,
	term: &stable::Term,
	env: &Env<Dynamic<'a>>,
) -> Bool<'a> {
	let vars = term.scopes.iter().map(|ty| Int::fresh_const(ctx, "v").into()).collect_vec();
	let env = env.append(vars.clone());
	let preds = trans_preds(ctx, &term.preds, &env);
	let apps = trans_apps_squashed(ctx, &term.apps, &env);
	let not = term
		.not
		.as_ref()
		.map_or(Bool::from_bool(ctx, true), |n| trans_squashed(ctx, n, &env).not());
	let body = Bool::and(ctx, &[&preds, &apps, &not]);
	exists_const(ctx, &vars.iter().collect_vec(), &[], &body).as_bool().unwrap()
}

fn trans_squashed<'a>(ctx: &'a Context, exp: &stable::UExpr, env: &Env<Dynamic<'a>>) -> Bool<'a> {
	let terms =
		exp.0.iter().enumerate().map(|(i, term)| trans_squashed_term(ctx, term, env)).collect_vec();
	Bool::or(ctx, &terms.iter().collect_vec())
}

pub fn unify(exp1: &stable::UExpr, exp2: &stable::UExpr, env: &Env<Entry>) -> bool {
	let cfg = Config::new();
	let ctx = Context::new(&cfg);
	let env = Env::new(env.entries.iter().map(|entry| match entry {
		Entry::Value(v, ty) => Int::fresh_const(&ctx, "v").into(),
		Entry::Table(v, sch) => Int::from_i64(&ctx, 0).into(),
	}));
	let solver = Solver::new(&ctx);
	println!("{:?}\n{:?}", exp1, exp2);
	unify_impl(&solver, exp1, exp2, &env, &env)
}

fn unify_impl(
	solver: &Solver,
	exp1: &stable::UExpr,
	exp2: &stable::UExpr,
	env1: &Env<Dynamic>,
	env2: &Env<Dynamic>,
) -> bool {
	let terms1 = exp1.0.clone();
	let mut terms2 = exp2.0.clone();
	let paired = terms1.iter().all(|t1| {
		(0..terms2.len()).any(|i| {
			let t2 = &terms2[i];
			let unifies = unify_term(solver, t1, t2, env1, env2);
			if unifies {
				terms2.swap_remove(i);
			}
			unifies
		})
	});
	paired && terms2.is_empty()
}

fn perm_equiv<T: Ord + PartialEq + Clone>(v1: &[T], v2: &[T]) -> bool {
	if v1.len() == v2.len() {
		let mut v1 = v2.to_vec();
		let mut v2 = v2.to_vec();
		v1.sort();
		v2.sort();
		v1 == v2
	} else {
		false
	}
}

fn perms<T, V>(types: Vec<T>, vars: Vec<V>) -> impl Iterator<Item = Vec<V>>
where
	T: Ord + PartialEq + Clone,
	V: Clone,
{
	let sort_perm = permutation::sort(types.as_slice());
	let sorted_scopes = sort_perm.apply_slice(types.as_slice());
	let groups = sorted_scopes.iter().group_by(|a| *a);
	let group_lengths = if types.is_empty() {
		Either::Left(std::iter::once(0))
	} else {
		Either::Right(groups.into_iter().map(|(_, group)| group.count()))
	};
	let mut level = 0;
	let inv_sort_perm = sort_perm.inverse();
	group_lengths
		.map(|length| {
			let perms = (level..level + length).permutations(length);
			level += length;
			perms
		})
		.multi_cartesian_product()
		.map(move |perms| {
			let perm_vec = perms.into_iter().flatten().collect_vec();
			let permute = &inv_sort_perm * &permutation::Permutation::from_vec(perm_vec);
			permute.apply_slice(vars.as_slice())
		})
}

fn unify_term(
	solver: &Solver,
	t1: &stable::Term,
	t2: &stable::Term,
	env1: &Env<Dynamic>,
	env2: &Env<Dynamic>,
) -> bool {
	solver.push();
	defer!(solver.pop(1));
	if !perm_equiv(&t1.scopes, &t2.scopes) {
		return false;
	}
	let perm1 = permutation::sort(t1.scopes.as_slice());
	let ctx = solver.get_context();
	let vars1 = t1.scopes.iter().map(|ty| Int::fresh_const(ctx, "v").into()).collect_vec();
	let vars = perm1.apply_slice(vars1.as_slice());
	let env1 = env1.append(vars1);
	perms(t1.scopes.clone(), vars.clone()).any(|vars2| {
		println!("{:?}", vars2);
		solver.push();
		defer!(solver.pop(1));
		let env2 = env2.append(vars2);
		let preds1 = trans_preds(ctx, &t1.preds, &env1);
		let preds2 = trans_preds(ctx, &t2.preds, &env2);
		let preds_equiv = preds1.iff(&preds2);
		let apps1 = trans_apps(ctx, &t1.apps, &env1);
		let apps2 = trans_apps(ctx, &t2.apps, &env2);
		let apps_equiv = apps1._eq(&apps2);
		let equiv = Bool::and(ctx, &[&preds_equiv, &apps_equiv]);
		if solver.check_assumptions(&[equiv.not()]) == SatResult::Unsat {
			solver.assert(&equiv);
		} else {
			return false;
		}
		match (&t1.squash, &t2.squash) {
			(Some(s1), Some(s2)) => {
				let sq1 = trans_squashed(ctx, &s1, &env1);
				let sq2 = trans_squashed(ctx, &s2, &env2);
				if solver.check_assumptions(&[sq1.iff(&sq2).not()]) != SatResult::Unsat {
					return false;
				}
			},
			(None, None) => (),
			_ => return false,
		}
		match (&t1.not, &t2.not) {
			(Some(n1), Some(n2)) if unify_impl(solver, n1, n2, &env1, &env2) => (),
			(None, None) => (),
			_ => return false,
		}
		true
	})
}
