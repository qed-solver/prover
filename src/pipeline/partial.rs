use std::ops::Mul;

use imbl::{vector, Vector};
use itertools::Either;

use super::shared::Schema;
use crate::pipeline::shared::{DataType, Eval, Terms, VL};
use crate::pipeline::unify::Unify;
use crate::pipeline::{normal, shared, syntax};

pub type Expr = shared::Expr<Relation, UExpr>;
pub type Head = shared::Head<Relation, UExpr>;
pub type Neutral = shared::Neutral<Relation, UExpr>;
pub type Logic = shared::Logic<Relation, UExpr>;

impl Head {
	pub fn app(self, args: Vector<Expr>, env: &normal::Env) -> Either<Neutral, UExpr> {
		use shared::Head::*;
		match self {
			HOp(op, args, _) if op == "limit" && args[0] == 0u32.into() => {
				Either::Right(UExpr::zero())
			},
			HOp(op, h_args, rel)
				if ((op == "limit" && h_args[0] == 1u32.into()) && rel.degen(env))
					|| (op == "offset" && h_args[0] == 0u32.into()) =>
			{
				Either::Right(rel.app(args))
			},
			_ => Either::Left(Neutral::new(self, args)),
		}
	}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Relation {
	Rigid(Head),
	Lam(Vector<DataType>, Env, syntax::UExpr),
}

impl Relation {
	pub fn app(self, args: Vector<Expr>) -> UExpr {
		use Relation::*;
		match self {
			Rigid(head) => UExpr::apply(head, args),
			Lam(_, env, body) => (&env.append(args)).eval(body),
		}
	}

	pub fn scope(&self, schemas: &Vector<Schema>) -> Vector<DataType> {
		use Relation::*;
		match self {
			Rigid(Head::Var(l)) => schemas[l.0].types.clone().into(),
			Rigid(Head::HOp(_, _, rel)) => rel.scope(schemas),
			Lam(scopes, _, _) => scopes.clone(),
		}
	}

	fn degen(&self, env: &normal::Env) -> bool {
		env.unify(UExpr::sum(self.clone()), UExpr::logic(Logic::Exists(self.clone())))
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

	pub fn apply(head: Head, args: Vector<Expr>) -> Self {
		UExpr::term(Term { apps: vector![Neutral { head, args }], ..Term::default() })
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
			Sum(scopes, body) => UExpr::sum(Relation::Lam(scopes, self.clone(), *body)),
			Pred(logic) => UExpr::logic(self.eval(logic)),
			App(table, args) => {
				let rel: Relation = self.eval(table);
				rel.app(self.eval(args))
			},
		}
	}
}

impl Eval<(VL, DataType), Expr> for &Env {
	fn eval(self, (VL(l), ty): (VL, DataType)) -> Expr {
		assert_eq!(self.0[l].ty(), ty, "Wrong type for {}", VL(l));
		self.0[l].clone()
	}
}

impl Eval<syntax::Relation, Relation> for &Env {
	fn eval(self, source: syntax::Relation) -> Relation {
		use syntax::Relation::*;
		match source {
			Var(t) => Relation::Rigid(Head::Var(t)),
			HOp(name, args, rel) => {
				Relation::Rigid(Head::HOp(name, self.eval(args), self.eval(rel)))
			},
			Lam(scopes, body) => Relation::Lam(scopes, self.clone(), *body),
		}
	}
}
