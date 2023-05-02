use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{Read, Write};
use std::ops::Deref;
use std::process::{Command, Stdio};
use std::rc::Rc;

use imbl::Vector;
use itertools::Itertools;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::SatResult;

use super::normal::Term;
use super::shared::{self, Ctx};
use crate::pipeline::normal::{Expr, HOpMap, RelHOpMap, Relation, UExpr, Z3Env};
use crate::pipeline::shared::{DataType, Eval};

pub trait Unify<T> {
	fn unify(self, t1: T, t2: T) -> bool;
}

#[derive(Clone)]
pub struct UnifyEnv<'c>(pub Rc<Ctx<'c>>, pub Vector<Dynamic<'c>>, pub Vector<Dynamic<'c>>);

impl<'c> Unify<&Relation> for &UnifyEnv<'c> {
	fn unify(self, rel1: &Relation, rel2: &Relation) -> bool {
		let (shared::Lambda(tys1, uexpr1), shared::Lambda(tys2, uexpr2)) = (rel1, rel2);
		if tys1 != tys2 {
			return false;
		}
		let UnifyEnv(ctx, subst1, subst2) = self;
		let vars = &tys1.iter().map(|ty| ctx.var(ty, "v")).collect();
		UnifyEnv(ctx.clone(), subst1 + vars, subst2 + vars).unify(uexpr1, uexpr2)
	}
}

impl<'c> Unify<&UExpr> for &UnifyEnv<'c> {
	fn unify(self, u1: &UExpr, u2: &UExpr) -> bool {
		let mut terms2 = u2.0.clone();
		u1.0.len() == u2.0.len()
			&& u1.iter().all(|t1| {
				(0..terms2.len())
					.any(|i| self.unify(t1, &terms2[i]).then(|| terms2.remove(i)).is_some())
			})
	}
}

impl<'c> Unify<&Expr> for &UnifyEnv<'c> {
	fn unify(self, t1: &Expr, t2: &Expr) -> bool {
		let UnifyEnv(ctx, subst1, subst2) = self;
		let h_ops = Rc::new(RefCell::new(HashMap::new()));
		let rel_h_ops = Rc::new(RefCell::new(HashMap::new()));
		let env1 = &Z3Env(ctx.clone(), subst1.clone(), h_ops.clone(), rel_h_ops.clone());
		let env2 = &Z3Env(ctx.clone(), subst2.clone(), h_ops.clone(), rel_h_ops.clone());
		let e1 = env1.eval(t1);
		let e2 = env2.eval(t2);
		let h_ops_equiv =
			extract_equiv(ctx.clone(), h_ops.borrow().deref(), rel_h_ops.borrow().deref());
		ctx.solver.check_assumptions(&[h_ops_equiv, e1._eq(&e2).not()]) == SatResult::Unsat
	}
}

impl<'c> Unify<&Vec<Expr>> for &UnifyEnv<'c> {
	fn unify(self, ts1: &Vec<Expr>, ts2: &Vec<Expr>) -> bool {
		ts1.len() == ts2.len() && ts1.iter().zip(ts2).all(|(t1, t2)| self.unify(t1, t2))
	}
}

fn extract_equiv<'c>(ctx: Rc<Ctx<'c>>, h_ops: &HOpMap<'c>, rel_h_ops: &RelHOpMap<'c>) -> Bool<'c> {
	let expr_eqs = h_ops
		.iter()
		.tuple_combinations()
		.filter_map(|(((op1, args1, rel1, env1), v1), ((op2, args2, rel2, env2), v2))| {
			let env = &UnifyEnv(ctx.clone(), env1.clone(), env2.clone());
			(op1 == op2 && env.unify(args1, args2) && env.unify(rel1, rel2)).then(|| v1._eq(v2))
		})
		.collect_vec();
	let rel_eqs = rel_h_ops
		.iter()
		.tuple_combinations()
		.filter_map(
			|(
				((op1, args1, rel1, env1, sq1), (n1, dom1)),
				((op2, args2, rel2, env2, sq2), (n2, dom2)),
			)| {
				let env = UnifyEnv(ctx.clone(), env1.clone(), env2.clone());
				(op1 == op2
					&& sq1 == sq2 && dom1 == dom2
					&& env.unify(args1, args2)
					&& env.unify(rel1, rel2))
				.then(|| {
					let vars = dom1.iter().map(|ty| ctx.var(ty, "t")).collect_vec();
					let vars = vars.iter().collect_vec();
					let target = if *sq1 { DataType::Boolean } else { DataType::Integer };
					let l = &ctx.app(n1, &vars, &target, false);
					let r = &ctx.app(n2, &vars, &target, false);
					let vars = vars.iter().map(|&v| v as &dyn Ast).collect_vec();
					z3::ast::forall_const(ctx.z3_ctx(), &vars, &[], &l._eq(r))
				})
			},
		)
		.collect_vec();
	Bool::and(ctx.z3_ctx(), &expr_eqs.iter().chain(rel_eqs.iter()).collect_vec())
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

fn perms<T, V>(types: Vec<T>, vars: Vec<V>) -> impl Iterator<Item = Vec<V>>
where
	T: Ord + PartialEq + Clone,
	V: Clone,
{
	use itertools::Either;
	let sort_perm = permutation::sort(types.as_slice());
	let sorted_scopes = sort_perm.apply_slice(types.as_slice());
	let sorted_vars = sort_perm.apply_slice(vars.as_slice());
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
			permute.apply_slice(sorted_vars.as_slice())
		})
}

impl<'c> Unify<&Term> for &UnifyEnv<'c> {
	fn unify(self, t1: &Term, t2: &Term) -> bool {
		if !perm_equiv(&t1.scope, &t2.scope) {
			return false;
		}
		log::info!("Unifying\n{}\n{}", t1, t2);
		let UnifyEnv(ctx, subst1, subst2) = self;
		let z3_ctx = ctx.z3_ctx();
		let vars1 = t1.scope.iter().map(|ty| ctx.var(ty, "v")).collect();
		let subst1 = subst1 + &vars1;
		perms(t1.scope.iter().cloned().collect(), vars1.into_iter().collect()).take(24).any(
			|vars2| {
				assert_eq!(vars2.len(), t2.scope.len());
				log::info!("Permutation: {:?}", vars2);
				let subst2 = subst2 + &vars2.into();
				let h_ops = Rc::new(RefCell::new(HashMap::new()));
				let rel_h_ops = Rc::new(RefCell::new(HashMap::new()));
				let env1 = &Z3Env(ctx.clone(), subst1.clone(), h_ops.clone(), rel_h_ops.clone());
				let env2 = &Z3Env(ctx.clone(), subst2.clone(), h_ops.clone(), rel_h_ops.clone());
				let (logic1, apps1): (_, Int<'c>) = (env1.eval(&t1.logic), env1.eval(&t1.apps));
				let (logic2, apps2) = (env2.eval(&t2.logic), env2.eval(&t2.apps));
				let equiv = logic1
					.ite(&apps1, &Int::from_i64(z3_ctx, 0))
					._eq(&logic2.ite(&apps2, &Int::from_i64(z3_ctx, 0)));
				let solver = &ctx.solver;
				solver.push();
				solver.assert(&Bool::or(z3_ctx, &[&logic1, &logic2]));
				let h_ops_equiv =
					extract_equiv(ctx.clone(), h_ops.borrow().deref(), rel_h_ops.borrow().deref());
				solver.pop(1);
				log::info!("{}", equiv);
				log::info!("{}", h_ops_equiv);
				smt(solver, h_ops_equiv.implies(&equiv))
			},
		)
	}
}

pub(crate) fn smt<'c>(solver: &'c z3::Solver, pred: Bool<'c>) -> bool {
	let smt: String = solver
		.dump_smtlib(pred.not())
		.replace(" and", " true")
		.replace(" or", " false")
		.replace(")and", ") true")
		.replace(")or", ") false")
		.replace("(* ", "(* 1 ")
		.replace("(+ ", "(+ 0 ");
	let smt = smt.strip_prefix("; \n(set-info :status )").unwrap_or(smt.as_str());
	let res = crossbeam::atomic::AtomicCell::new(false);
	crossbeam::thread::scope(|s| {
		let res = &res;
		let p = crossbeam::sync::Parker::new();
		let u1 = p.unparker().clone();
		let u2 = p.unparker().clone();
		let mut z3_cmd = Command::new("z3")
			.args(["-in"])
			.stdin(Stdio::piped())
			.stdout(Stdio::piped())
			.spawn()
			.expect("Failed to spawn child process for z3.");
		let mut z3_in = z3_cmd.stdin.take().expect("Failed to open stdin.");
		let mut z3_out = z3_cmd.stdout.take().expect("Failed to read stdout");
		let mut cvc5_cmd = Command::new("cvc5")
			.args(["--strings-exp"])
			.stdin(Stdio::piped())
			.stdout(Stdio::piped())
			.spawn()
			.expect("Failed to spawn child process for cvc5.");
		let mut cvc5_in = cvc5_cmd.stdin.take().expect("Failed to open stdin.");
		let mut cvc5_out = cvc5_cmd.stdout.take().expect("Failed to capture stdout");
		s.spawn(move |_| {
			z3_in.write_all(smt.as_bytes()).unwrap();
			drop(z3_in);
			let mut result = String::new();
			z3_out.read_to_string(&mut result).expect("Failed to read stdout.");
			let provable = dbg!(&result).starts_with("unsat\n");
			res.fetch_or(provable);
			if !result.starts_with("unknown\n") {
				u1.unpark();
			}
		});
		s.spawn(move |_| {
			cvc5_in.write_all("(set-logic ALL)".as_bytes()).unwrap();
			cvc5_in.write_all(smt.as_bytes()).unwrap();
			drop(cvc5_in);
			let mut result = String::new();
			cvc5_out.read_to_string(&mut result).expect("Failed to read stdout.");
			let provable = dbg!(&result).ends_with("unsat\n");
			res.fetch_or(provable);
			if !result.ends_with("unknown\n") {
				u2.unpark();
			}
		});
		p.park_timeout(Ctx::timeout());
		z3_cmd.kill().unwrap();
		z3_cmd.wait().unwrap();
		cvc5_cmd.kill().unwrap();
		cvc5_cmd.wait().unwrap();
		res.load()
	})
	.unwrap()
}
