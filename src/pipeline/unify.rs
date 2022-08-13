use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Write;
use std::ops::Deref;
use std::process::{Command, Stdio};
use std::rc::Rc;

use imbl::Vector;
use isoperm::wrapper::Isoperm;
use itertools::Itertools;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::SatResult;

use super::normal::Term;
use super::shared::{self, Ctx};
use crate::pipeline::normal::{Expr, HOpMap, RelHOpMap, Relation, UExpr, Z3Env};
use crate::pipeline::shared::{DataType, Eval, Head, VL};

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

impl<'c> Unify<&Term> for &UnifyEnv<'c> {
	fn unify(self, t1: &Term, t2: &Term) -> bool {
		if !perm_equiv(&t1.scope, &t2.scope) {
			return false;
		}
		log::info!("Unifying\n{}\n{}", t1, t2);
		let UnifyEnv(ctx, subst1, subst2) = self;
		type Var<'e, 'c> = isoperm::wrapper::Var<usize, &'e Dynamic<'c>, &'e Expr>;
		fn extract<'v, 'c>(
			t: &'v Term,
			subst: &'v Vector<Dynamic<'c>>,
		) -> (Vec<(usize, Vec<Var<'v, 'c>>)>, HashMap<Var<'v, 'c>, DataType>) {
			let scope = subst.len()..subst.len() + t.scope.len();
			let mut args: HashMap<_, _> =
				scope.clone().map(Var::Local).zip(t.scope.clone()).collect();
			let constraints = t
				.apps
				.iter()
				.filter_map(|app| {
					let translate = |arg: &'v Expr| match arg {
						Expr::Var(VL(l), _) if scope.contains(l) => Var::Local(*l),
						Expr::Var(VL(l), ty) => {
							let v = &subst[*l];
							args.insert(Var::Global(v), ty.clone());
							Var::Global(v)
						},
						arg => {
							args.insert(Var::Expr(arg), arg.ty());
							Var::Expr(arg)
						},
					};
					match &app.head {
						&Head::Var(VL(t)) => Some((t, app.args.iter().map(translate).collect())),
						Head::HOp(_, _, _) => None,
					}
				})
				.collect();
			(constraints, args)
		}
		let (constraints1, args1) = extract(t1, subst1);
		let (constraints2, args2) = extract(t2, subst2);
		let z3_ctx = ctx.z3_ctx();
		let vars1 = t1.scope.iter().map(|ty| ctx.var(ty, "v")).collect_vec();
		let subst1 = subst1 + &vars1.into();
		Isoperm::new(constraints1, args1, constraints2, args2)
			.unwrap()
			.result()
			.map(|bij| {
				bij.into_iter()
					.filter_map(|(v1, v2)| match (v1, v2) {
						(&Var::Local(l1), &Var::Local(l2)) => Some((l2, subst1[l1].clone())),
						_ => None,
					})
					.sorted_by_key(|(l, _)| *l)
					.map(|(_, v)| v)
					.collect_vec()
			})
			.take(24)
			.any(|vars2| {
				assert_eq!(vars2.len(), t2.scope.len());
				log::info!("Permutation: {:?}", vars2);
				let subst2 = subst2 + &vars2.into();
				let h_ops = Rc::new(RefCell::new(HashMap::new()));
				let rel_h_ops = Rc::new(RefCell::new(HashMap::new()));
				let env1 = &Z3Env(ctx.clone(), subst1.clone(), h_ops.clone(), rel_h_ops.clone());
				let env2 = &Z3Env(ctx.clone(), subst2.clone(), h_ops.clone(), rel_h_ops.clone());
				let (logic1, apps1): (_, Int<'c>) = (env1.eval(&t1.logic), env1.eval(&t1.apps));
				let (logic2, apps2) = (env2.eval(&t2.logic), env2.eval(&t2.apps));
				let apps_equiv = apps1._eq(&apps2);
				let equiv = Bool::and(z3_ctx, &[&logic1.iff(&logic2), &apps_equiv]);
				let solver = &ctx.solver;
				solver.push();
				solver.assert(&logic1);
				solver.assert(&logic2);
				let h_ops_equiv =
					extract_equiv(ctx.clone(), h_ops.borrow().deref(), rel_h_ops.borrow().deref());
				solver.pop(1);
				log::info!("{}", equiv);
				log::info!("{}", h_ops_equiv);
				smt(solver, h_ops_equiv.implies(&equiv))
			})
	}
}

pub(crate) fn smt<'c>(solver: &'c z3::Solver, pred: Bool<'c>) -> bool {
	let smt: String = solver
		.dump_smtlib(pred.not())
		.replace(" and", " true")
		.replace(" or", " false")
		.replace("(* ", "(* 1 ")
		.replace("(+ ", "(+ 0 ");
	let smt = smt.strip_prefix("; \n(set-info :status )").unwrap_or(smt.as_str());
	let mut child = Command::new("cvc5")
		.args(["--tlimit=5000", "--strings-exp"])
		.stdin(Stdio::piped())
		.stdout(Stdio::piped())
		.spawn()
		.expect("Failed to spawn child process");
	let mut stdin = child.stdin.take().expect("Failed to open stdin");
	stdin.write_all("(set-logic ALL)".as_bytes()).unwrap();
	stdin.write_all(smt.as_bytes()).unwrap();
	drop(stdin);
	let output = child.wait_with_output().expect("Failed to read stdout");
	let result = String::from_utf8(output.stdout).unwrap();
	dbg!(result).ends_with("unsat\n")
}
