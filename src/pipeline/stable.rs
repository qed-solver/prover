use std::cell::RefCell;
use std::iter::once;

use imbl::{vector, Vector};
use itertools::{Either, Itertools};
use scopeguard::defer;
use z3::ast::{exists_const, forall_const, Ast, Bool, Dynamic};
use z3::{SatResult, Solver};

use crate::pipeline::normal::{
	BiScoped, Expr, HOpMap, Inner, RelHOpMap, Relation, SInner, Scoped, UExpr, Z3Env,
};
use crate::pipeline::shared::{DataType, Eval, Terms, VL};
use crate::pipeline::unify::cvc5;
use crate::pipeline::{normal, shared};

#[derive(Copy, Clone)]
pub struct Env<'e, 'c>(&'e Vector<Expr>, Z3Env<'e, 'c>);

impl<'e, 'c> Env<'e, 'c> {
	pub fn new(
		subst: &'e Vector<Expr>,
		solver: &'e Solver<'c>,
		z3_subst: &'e Vector<Dynamic<'c>>,
		h_ops: &'e RefCell<HOpMap<'c>>,
		rel_h_ops: &'e RefCell<RelHOpMap<'c>>,
	) -> Self {
		Env(subst, Z3Env::new(solver, z3_subst, h_ops, rel_h_ops))
	}

	fn append(self, scopes: Vector<DataType>) -> (Vector<Expr>, Vector<Dynamic<'c>>) {
		let (uexpr_vars, z3_vars) = self.extend(scopes);
		(self.0 + &uexpr_vars, self.1.substs() + &z3_vars)
	}

	// fn extend(self, new_subst: &'e Vector<Expr>, new_z3_subst: &'e Vector<Dynamic<'c>>) -> (Vector<Expr>, Vector<Dynamic<'c>>) {
	// 	(self.0 + new_subst, self.1.substs() + new_z3_subst)
	// }

	fn extend(self, scopes: Vector<DataType>) -> (Vector<Expr>, Vector<Dynamic<'c>>) {
		let exprs = scopes
			.iter()
			.cloned()
			.enumerate()
			.map(|(l, ty)| Expr::Var(VL(self.0.len() + l), ty))
			.collect();
		(exprs, self.1.extend(scopes))
	}

	fn update(self, subst: &'e Vector<Expr>, z3_subst: &'e Vector<Dynamic<'c>>) -> Self {
		Env(subst, self.1.update(z3_subst))
	}
}

impl Eval<BiScoped<Inner>, Option<BiScoped<Inner>>> for Env<'_, '_> {
	fn eval(self, source: BiScoped<Inner>) -> Option<BiScoped<Inner>> {
		let Env(subst, z3_env) = self;
		let lvl = subst.len();
		let solver = z3_env.solver();
		let ctx = solver.get_context();
		let scopes = source.keys;
		solver.push();
		defer!(solver.pop(1));
		let (mut vars, mut z3_vars) = self.extend(scopes);
		let z3_subst = z3_env.substs() + &z3_vars;
		let logical: Bool = z3_env.update(&z3_subst).eval(&source.inner);
		if let SatResult::Unsat = solver.check_assumptions(&[logical.clone()]) {
			return None;
		}
		let (mut key_vars, mut dep_vars) = (vec![], vec![]);
		let (mut keys, mut deps) = (vector![], vector![]);
		let mut new_subst = vector![];
		while let (Some(Expr::Var(l, ty)), Some(z3_var)) = (vars.pop_front(), z3_vars.pop_front()) {
			let e = shared::var(ctx, ty.clone(), "w");
			let body = logical.implies(&z3_var._eq(&e));
			let z3_asts = z3_vars.iter().map(|v| v as &dyn Ast).collect_vec();
			let dep_asts = dep_vars.iter().map(|v| v as &dyn Ast).collect_vec();
			let p = forall_const(ctx, &dep_asts, &[], &body);
			let p = forall_const(ctx, &[&z3_var], &[], &p);
			let p = exists_const(ctx, &[&e], &[], &p);
			let p = forall_const(ctx, &z3_asts, &[], &p);
			let p =
				forall_const(ctx, &key_vars.iter().map(|v| v as &dyn Ast).collect_vec(), &[], &p);
			let (dep, key) = (deps.len(), keys.len());
			let (grp_vars, grp, expr) = match cvc5(solver.get_context(), p) {
				true => {
					println!("{} is eliminated", l);
					(&mut dep_vars, &mut deps, Either::Right((VL(lvl + dep), ty.clone())))
				},
				false => (&mut key_vars, &mut keys, Either::Left((VL(lvl + key), ty.clone()))),
			};
			grp_vars.push(z3_var);
			grp.push_back(ty);
			new_subst.push_back(expr);
		}
		let new_subst: Vector<_> = new_subst
			.into_iter()
			.map(|v| {
				v.either(
					|(vl, ty)| Expr::Var(vl, ty),
					|(VL(l), ty)| Expr::Var(VL(l + keys.len()), ty),
				)
			})
			.collect();
		let subst = subst + &new_subst;
		let inner = self.update(&subst, &z3_subst).eval(source.inner);
		Some(BiScoped { keys, deps, inner })
	}
}

impl<'e, 'c> Eval<Scoped<SInner>, Scoped<SInner>> for Env<'e, 'c> {
	fn eval(self, source: Scoped<SInner>) -> Scoped<SInner> {
		let (ref subst, ref z3_subst) = self.append(source.scopes.clone());
		Scoped { inner: self.update(subst, z3_subst).eval(source.inner), ..source }
	}
}

impl<'e, 'c> Eval<Inner, Inner> for Env<'e, 'c> {
	fn eval(self, source: Inner) -> Inner {
		let preds = self.eval(source.preds);
		let squash = self.eval(source.squash);
		let not = self.eval(source.not);
		let apps = self.eval(source.apps);
		Inner { preds, squash, not, apps }
	}
}

impl<'e, 'c> Eval<SInner, SInner> for Env<'e, 'c> {
	fn eval(self, source: SInner) -> SInner {
		let preds = self.eval(source.preds);
		let not = self.eval(source.not);
		let apps = self.eval(source.apps);
		SInner { preds, not, apps }
	}
}

impl<'e, 'c> Eval<(VL, DataType), Expr> for Env<'e, 'c> {
	fn eval(self, (VL(l), ty): (VL, DataType)) -> Expr {
		assert_eq!(self.0[l].ty(), ty, "wrong type for {}", VL(l));
		self.0[l].clone()
	}
}

impl<'e, 'c> Eval<Relation, Relation> for Env<'e, 'c> {
	fn eval(self, source: Relation) -> Relation {
		use shared::Relation::*;
		match source {
			Var(l) => Var(l),
			Lam(scopes, body) => {
				let (ref subst, ref z3_subst) = self.append(scopes.clone());
				Lam(scopes, Box::new(self.update(subst, z3_subst).eval(*body)))
			},
			HOp(op, args, rel) => HOp(op, self.eval(args), self.eval(rel)),
		}
	}
}

impl<'e, 'c> Eval<UExpr, UExpr> for Env<'e, 'c> {
	fn eval(self, source: UExpr) -> UExpr {
		source.0.into_iter().filter_map(|term| self.eval(term)).collect()
	}
}
