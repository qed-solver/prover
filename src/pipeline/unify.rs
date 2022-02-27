use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::fs::File;
use std::io::Write;
use std::ops::Deref;
use std::process::Command;

use imbl::Vector;
use itertools::{Either, Itertools};
use z3::ast::{exists_const, forall_const, Ast, Bool, Dynamic};
use z3::{Context, SatResult, Solver};

use crate::pipeline::normal::{BiScoped, Expr, HOpMap, Inner, Relation, Scoped, UExpr, Z3Env};
use crate::pipeline::shared;
use crate::pipeline::shared::{var, Eval};

pub trait Unify<T> {
	fn unify(self, t1: T, t2: T) -> bool;
}

#[derive(Copy, Clone)]
pub struct UnifyEnv<'e, 'c>(&'e Solver<'c>, &'e Vector<Dynamic<'c>>, &'e Vector<Dynamic<'c>>);

impl<'e, 'c> UnifyEnv<'e, 'c> {
	pub fn new(
		solver: &'e Solver<'c>,
		subst1: &'e Vector<Dynamic<'c>>,
		subst2: &'e Vector<Dynamic<'c>>,
	) -> Self {
		UnifyEnv(solver, subst1, subst2)
	}
}

impl<'e, 'c> Unify<&Relation> for UnifyEnv<'e, 'c> {
	fn unify(self, rel1: &Relation, rel2: &Relation) -> bool {
		let (shared::Relation(tys1, uexpr1), shared::Relation(tys2, uexpr2)) = (rel1, rel2);
		if tys1 != tys2 {
			return false;
		}
		let UnifyEnv(solver, subst1, subst2) = self;
		let ctx = solver.get_context();
		let vars = tys1.iter().map(|ty| var(ctx, ty.clone(), "v")).collect();
		let subst1 = subst1 + &vars;
		let subst2 = subst2 + &vars;
		UnifyEnv(solver, &subst1, &subst2).unify(uexpr1.as_ref(), uexpr2.as_ref())
	}
}

impl<'e, 'c> Unify<&UExpr> for UnifyEnv<'e, 'c> {
	fn unify(self, u1: &UExpr, u2: &UExpr) -> bool {
		let mut terms2 = u2.0.clone();
		u1.0.len() == u2.0.len()
			&& u1.iter().all(|t1| {
				(0..terms2.len()).any(|i| {
					let unifies = self.unify(t1, &terms2[i]);
					if unifies {
						terms2.remove(i);
					}
					unifies
				})
			})
	}
}

impl<'e, 'c> Unify<&Expr> for UnifyEnv<'e, 'c> {
	fn unify(self, t1: &Expr, t2: &Expr) -> bool {
		let UnifyEnv(solver, subst1, subst2) = self;
		let h_ops = &RefCell::new(HashMap::new());
		let rel_h_ops = &RefCell::new(HashMap::new());
		let env1 = Z3Env::new(solver, subst1, h_ops, rel_h_ops);
		let env2 = Z3Env::new(solver, subst2, h_ops, rel_h_ops);
		let e1 = env1.eval(t1);
		let e2 = env2.eval(t2);
		let h_ops_equiv = extract_equiv(solver, h_ops.borrow().deref());
		cvc5(solver.get_context(), h_ops_equiv.implies(&e1._eq(&e2)))
	}
}

impl<'e, 'c> Unify<&Vec<Expr>> for UnifyEnv<'e, 'c> {
	fn unify(self, ts1: &Vec<Expr>, ts2: &Vec<Expr>) -> bool {
		ts1.len() == ts2.len() && ts1.iter().zip(ts2).all(|(t1, t2)| self.unify(t1, t2))
	}
}

fn extract_equiv<'c>(solver: &Solver<'c>, h_ops: &HOpMap<'c>) -> Bool<'c> {
	let h_ops_eqs = h_ops
		.iter()
		.tuple_combinations()
		.filter_map(|(((op1, args1, rel1, env1), v1), ((op2, args2, rel2, env2), v2))| {
			let env = UnifyEnv(solver, env1, env2);
			(op1 == op2 && env.unify(args1, args2) && env.unify(rel1, rel2)).then(|| v1._eq(v2))
		})
		.collect_vec();
	Bool::and(solver.get_context(), &h_ops_eqs.iter().collect_vec())
}

fn perm_equiv<T: Ord + Clone>(v1: &Vector<T>, v2: &Vector<T>) -> bool {
	v1.len() == v2.len() && {
		let mut v1 = v1.clone();
		let mut v2 = v2.clone();
		v1.sort();
		v2.sort();
		v1 == v2
	}
}

fn perms<T, V>(types: &Vector<T>, vars: Vec<V>) -> impl Iterator<Item = Vec<V>>
where
	T: Ord + PartialEq + Clone + Debug,
	V: Clone + Debug,
{
	log::info!("{:?}", types);
	log::info!("{:?}", vars);
	let types = types.clone().into_iter().collect_vec();
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

impl<'e, 'c> Unify<&BiScoped<Inner>> for UnifyEnv<'e, 'c> {
	fn unify(self, t1: &BiScoped<Inner>, t2: &BiScoped<Inner>) -> bool {
		if !perm_equiv(&t1.keys, &t2.keys) {
			return false;
		}
		log::info!("Unifying\n{}\n{}", t1, t2);
		let UnifyEnv(solver, subst1, subst2) = self;
		let ctx = solver.get_context();
		let perm1 = permutation::sort(t1.keys.clone().into_iter().collect_vec());
		let keys1 = t1.keys.iter().map(|ty| var(ctx, ty.clone(), "v")).collect_vec();
		let keys = perm1.apply_slice(keys1.as_slice());
		let deps1: Vector<_> = t1.deps.iter().map(|ty| var(ctx, ty.clone(), "v")).collect();
		let deps_inner1: Vector<_> = t1.deps.iter().map(|ty| var(ctx, ty.clone(), "v")).collect();
		let deps2: Vector<_> = t2.deps.iter().map(|ty| var(ctx, ty.clone(), "v")).collect();
		let deps_inner2: Vector<_> = t2.deps.iter().map(|ty| var(ctx, ty.clone(), "v")).collect();
		let body_subst1 = subst1 + &keys1.clone().into() + deps1.clone();
		perms(&t2.keys, keys).take(50).any(|keys2| {
			log::info!("Permutation: {:?}", keys2);
			let body_subst2 = subst2 + &keys2.clone().into() + deps2.clone();
			let h_ops = &RefCell::new(HashMap::new());
			let rel_h_ops = &RefCell::new(HashMap::new());
			let env1 = Z3Env::new(solver, &body_subst1, h_ops, rel_h_ops);
			let env2 = Z3Env::new(solver, &body_subst2, h_ops, rel_h_ops);
			let (logic1, apps1) = env1.eval(&t1.inner);
			let (logic2, apps2) = env2.eval(&t2.inner);
			let apps_equiv = apps1._eq(&apps2);
			let inner_subst1 = subst1 + &keys1.clone().into() + deps_inner1.clone();
			let inner_env1 = Z3Env::new(solver, &inner_subst1, h_ops, rel_h_ops);
			let inner_logic1: Bool = inner_env1.eval(&t1.inner);
			let inner_eqs1 = deps1.iter().zip(&deps_inner1).map(|(e, v)| e._eq(v)).collect_vec();
			let inner_eqs1 = Bool::and(ctx, &inner_eqs1.iter().collect_vec());
			let inner1 = forall_const(
				ctx,
				&deps_inner1.iter().map(|v| v as &dyn Ast).collect_vec(),
				&[],
				&inner_logic1.implies(&inner_eqs1),
			);
			let inner_subst2 = subst2 + &keys2.clone().into() + deps_inner2.clone();
			let inner_env2 = Z3Env::new(solver, &inner_subst2, h_ops, rel_h_ops);
			let inner_logic2: Bool = inner_env2.eval(&t2.inner);
			let inner_eqs2 = deps2.iter().zip(&deps_inner2).map(|(e, v)| e._eq(v)).collect_vec();
			let inner_eqs2 = Bool::and(ctx, &inner_eqs2.iter().collect_vec());
			let inner2 = forall_const(
				ctx,
				&deps_inner2.iter().map(|v| v as &dyn Ast).collect_vec(),
				&[],
				&inner_logic2.implies(&inner_eqs2),
			);
			let equiv = Bool::and(ctx, &[&logic1.iff(&logic2), &apps_equiv, &inner1, &inner2]);
			let equiv =
				exists_const(ctx, &deps1.iter().map(|v| v as &dyn Ast).collect_vec(), &[], &equiv);
			let equiv =
				exists_const(ctx, &deps2.iter().map(|v| v as &dyn Ast).collect_vec(), &[], &equiv);
			let equiv =
				forall_const(ctx, &keys2.iter().map(|v| v as &dyn Ast).collect_vec(), &[], &equiv);
			solver.push();
			// solver.assert(&logic1);
			// solver.assert(&logic2);
			let h_ops_equiv = extract_equiv(solver, h_ops.borrow().deref());
			solver.pop(1);
			log::info!("{}", equiv);
			log::info!("{}", h_ops_equiv);
			cvc5(ctx, h_ops_equiv.implies(&equiv))
		})
	}
}

pub(crate) fn cvc5<'c>(ctx: &'c Context, pred: Bool<'c>) -> bool {
	let tmp = "tmp.smt2";
	let smt = ctx
		.dump_smtlib(pred.not())
		.replace(" and", " true")
		.replace(" or", " false")
		.replace("(* ", "(* 1 ")
		.replace("(+ ", "(+ 0 ");
	let smt = smt.strip_prefix("; \n(set-info :status )").unwrap_or(smt.as_str());
	let mut file = File::create(tmp).unwrap();
	file.write_all("(set-logic HO_ALL)\n(set-option :full-saturate-quant true)".as_bytes());
	file.write_all(smt.as_bytes());
	let output = Command::new("./cvc5").args([tmp, "--tlimit=1000"]).output().unwrap();
	let result = String::from_utf8(output.stdout).unwrap();
	result.ends_with("unsat\n")
}
