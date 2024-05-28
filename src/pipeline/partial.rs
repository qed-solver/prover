use std::ops::Mul;

use imbl::{vector, Vector};

use super::shared::{Lambda, Schema};
use crate::pipeline::shared::{DataType, Eval, Neutral as Neut, Terms, Typed, VL};
use crate::pipeline::unify::Unify;
use crate::pipeline::{normal, shared, syntax};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Relation(pub Vector<DataType>, pub Env, pub syntax::UExpr);
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Aggr(pub String, pub Vector<DataType>, pub Env, pub syntax::UExpr, pub syntax::Expr);
pub type Expr = shared::Expr<UExpr, Relation, Aggr>;
pub type Logic = shared::Logic<UExpr, Expr>;
pub type Head = shared::Head<Relation, Expr>;
pub type Neutral = shared::Neutral<Relation, Expr>;

impl Typed for Aggr {
	fn ty(&self) -> DataType {
		self.4.ty()
	}
}

impl Relation {
	pub fn app(self, args: Vector<Expr>) -> UExpr {
		let Relation(_, env, body) = self;
		(&env.append(args)).eval(body)
	}

	pub fn degen(&self, env: &normal::Env) -> bool {
		let sum = UExpr::sum(self.clone());
		env.unify(&sum.clone(), &UExpr::logic(Logic::squash(sum)))
	}
}

/// An U-expression in product normal form
pub type UExpr = Terms<Term>;

impl UExpr {
	pub fn logic(logic: Logic) -> Self {
		UExpr::term(Term { logic, ..Term::default() })
	}

	pub fn sum(summand: Relation) -> Self {
		UExpr::term(Term { sums: vector![summand], ..Term::default() })
	}

	pub fn neutral(head: Head, args: Vector<Expr>) -> Self {
		UExpr::term(Term { apps: vector![Neut(head, args)], ..Term::default() })
	}
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Term {
	pub logic: Logic,
	pub apps: Vector<Neutral>,
	pub sums: Vector<Relation>,
}

impl Default for Term {
	fn default() -> Self {
		Term { logic: Logic::tt(), apps: vector![], sums: vector![] }
	}
}

impl Mul for Term {
	type Output = Term;

	fn mul(self, rhs: Self) -> Self::Output {
		let logic = self.logic * rhs.logic;
		let apps = self.apps + rhs.apps;
		let sums = self.sums + rhs.sums;
		Term { logic, apps, sums }
	}
}

pub type NormAgg = (Vector<DataType>, Logic, Vector<Neutral>, Expr);

impl Expr {
	pub fn split(self, aop: &str, context: &Vector<DataType>) -> Vector<NormAgg> {
		match self {
			Expr::Op(op, args, _) if op == aop => {
				args.into_iter().flat_map(|arg| arg.split(aop, context)).collect()
			},
			Expr::Agg(Aggr(op, scope, env, u, e)) if op == aop => {
				let vars = shared::Expr::vars(context.len(), scope.clone());
				let env = &env.append(vars);
				let e = env.eval(e);
				let context = &(context + &scope);
				env.eval(u)
					.into_iter()
					.flat_map(|t| t.split(context))
					.flat_map(|(scp1, l1, apps1)| {
						let scope = &scope;
						e.clone().split(aop, &(context + &scp1)).into_iter().map(
							move |(scp2, l2, apps2, e)| {
								(
									scope + &scp1 + scp2,
									Logic::And(vector![l1.clone(), l2]),
									&apps1 + &apps2,
									e,
								)
							},
						)
					})
					.collect()
			},
			_ => vector![(vector![], Logic::tt(), vector![], self)],
		}
	}
}

pub type NormTerm = (Vector<DataType>, Logic, Vector<Neutral>);

impl Term {
	pub fn split(self, context: &Vector<DataType>) -> Vector<NormTerm> {
		self.splitter(context, vector![])
	}

	fn splitter(mut self, context: &Vector<DataType>, apps: Vector<Neutral>) -> Vector<NormTerm> {
		if let Some(app) = self.apps.pop_front() {
			match app.0 {
				Head::HOp(op, args, _) if op == "limit" && args[0] == 0u32.into() => vector![],
				Head::HOp(op, h_args, rel)
					if ((op == "limit" && h_args[0] == 1u32.into()) && rel.degen(context))
						|| (op == "offset" && h_args[0] == 0u32.into()) =>
				{
					(rel.app(app.1.clone()) * self)
						.into_iter()
						.flat_map(|t| t.splitter(context, apps.clone()))
						.collect()
				},
				_ => self.splitter(context, apps + vector![app]),
			}
		} else if let Some(summand) = self.sums.pop_front() {
			let scope = summand.0.clone();
			let vars = shared::Expr::vars(context.len(), scope.clone());
			let context = &(context + &scope);
			(summand.app(vars) * self)
				.into_iter()
				.flat_map(|t| {
					t.splitter(context, apps.clone())
						.into_iter()
						.map(|(s, l, a)| (&scope + &s, l, a))
				})
				.collect()
		} else {
			vector![(vector![], self.logic, apps)]
		}
	}
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Env(Vector<Expr>, Vector<Schema>);

impl Env {
	pub fn new(subst: Vector<Expr>, schemas: Vector<Schema>) -> Self {
		Env(subst, schemas)
	}

	pub fn append(&self, subst: Vector<Expr>) -> Env {
		Env(self.0.clone() + subst, self.1.clone())
	}
}

impl Eval<syntax::UExpr, UExpr> for &Env {
	fn eval(self, source: syntax::UExpr) -> UExpr {
		use syntax::UExpr::*;
		match source {
			Add(us) => us.into_iter().flat_map(|u| self.eval(u)).collect(),
			Mul(us) => us.into_iter().map(|u| self.eval(u)).fold(UExpr::one(), UExpr::mul),
			Squash(u) => UExpr::logic(Logic::squash(self.eval(*u))),
			Not(u) => UExpr::logic(!Logic::squash(self.eval(*u))),
			Sum(scope, body) => UExpr::sum(Relation(scope, self.clone(), *body)),
			Pred(logic) => UExpr::logic(self.eval(*logic)),
			App(table, args) => self.eval(*table).app(self.eval(args)),
			Neu(Neut(head, args)) => UExpr::neutral(self.eval(head), self.eval(args)),
		}
	}
}

impl Eval<(VL, DataType), Expr> for &Env {
	fn eval(self, (VL(l), ty): (VL, DataType)) -> Expr {
		assert_eq!(self.0[l].ty(), ty, "Wrong type for {}", VL(l));
		self.0[l].clone()
	}
}

impl Eval<syntax::Aggr, Expr> for &Env {
	fn eval(self, syntax::Aggr(op, scope, u, e): syntax::Aggr) -> Expr {
		Expr::Agg(Aggr(op, scope, self.clone(), u, *e))
	}
}

impl Eval<syntax::Relation, Relation> for &Env {
	fn eval(self, Lambda(scope, body): syntax::Relation) -> Relation {
		Relation(scope, self.clone(), body)
	}
}
