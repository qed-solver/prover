use std::ops::Mul;

use imbl::{vector, Vector};

use crate::pipeline::shared::{DataType, Eval, Terms, VL};
use crate::pipeline::{shared, syntax};

pub(crate) type Relation = shared::Relation<Closure>;
type Predicate = shared::Predicate<Relation>;
type Expr = shared::Expr<Relation>;
type Application = shared::Application<Relation>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Closure {
	pub body: syntax::UExpr,
	pub env: Env,
}

impl Closure {
	pub fn new(body: syntax::UExpr, env: Env) -> Self {
		Closure { body, env }
	}
}

/// An U-expression in product normal form
pub type UExpr = Terms<Term>;

impl UExpr {
	pub fn squash(squash: SUExpr) -> Self {
		UExpr::term(Term { squash, ..Term::default() })
	}

	pub fn not(not: SUExpr) -> Self {
		UExpr::term(Term { not, ..Term::default() })
	}

	pub fn pred(pred: Predicate) -> Self {
		UExpr::term(Term { preds: vector![pred], ..Term::default() })
	}

	pub fn sum(scopes: Vector<DataType>, summand: Closure) -> Self {
		UExpr::term(Term { sums: vector![Summation { scopes, summand }], ..Term::default() })
	}

	pub fn apply(rel: Relation, args: Vector<Expr>) -> Self {
		match rel {
			Relation::Var(table) => {
				UExpr::term(Term { apps: vector![Application { table, args }], ..Term::default() })
			},
			Relation::Lam(scopes, closure) => (&closure.env.append(args)).eval(closure.body),
		}
	}
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Term {
	pub preds: Vector<Predicate>,
	pub squash: SUExpr,
	pub not: SUExpr,
	pub apps: Vector<Application>,
	pub sums: Vector<Summation>,
}

impl Default for Term {
	fn default() -> Self {
		Term {
			preds: vector![],
			squash: SUExpr::one(),
			not: SUExpr::zero(),
			apps: vector![],
			sums: vector![],
		}
	}
}

pub type SUExpr = Terms<STerm>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct STerm {
	pub preds: Vector<Predicate>,
	pub not: SUExpr,
	pub apps: Vector<Application>,
	pub sums: Vector<Summation>,
}

impl Default for STerm {
	fn default() -> Self {
		STerm { preds: vector![], not: SUExpr::zero(), apps: vector![], sums: vector![] }
	}
}

impl SUExpr {
	pub fn not(not: SUExpr) -> Self {
		SUExpr::term(STerm { not, ..STerm::default() })
	}

	pub fn pred(pred: Predicate) -> Self {
		SUExpr::term(STerm { preds: vector![pred], ..STerm::default() })
	}

	pub fn sum(scopes: Vector<DataType>, summand: Closure) -> Self {
		SUExpr::term(STerm { sums: vector![Summation { scopes, summand }], ..STerm::default() })
	}

	pub fn apply(rel: Relation, args: Vector<Expr>) -> Self {
		match rel {
			Relation::Var(table) => SUExpr::term(STerm {
				apps: vector![Application { table, args }],
				..STerm::default()
			}),
			Relation::Lam(scopes, closure) => (&closure.env.append(args)).eval(closure.body),
		}
	}
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Summation {
	pub scopes: Vector<DataType>,
	pub summand: Closure,
}

impl Mul for Term {
	type Output = Term;

	fn mul(self, rhs: Self) -> Self::Output {
		let preds = self.preds + rhs.preds;
		let squash = self.squash * rhs.squash;
		let not = self.not + rhs.not;
		let apps = self.apps + rhs.apps;
		let sums = self.sums + rhs.sums;
		Term { preds, squash, not, apps, sums }
	}
}

impl Mul for STerm {
	type Output = STerm;

	fn mul(self, rhs: Self) -> Self::Output {
		let preds = self.preds + rhs.preds;
		let not = self.not + rhs.not;
		let apps = self.apps + rhs.apps;
		let sums = self.sums + rhs.sums;
		STerm { preds, not, apps, sums }
	}
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Env(Vector<Expr>);

impl Env {
	pub fn append(&self, vars: Vector<Expr>) -> Env {
		Env(self.0.clone() + vars)
	}
}

impl<'e> Eval<syntax::UExpr, UExpr> for &'e Env {
	fn eval(self, source: syntax::UExpr) -> UExpr {
		use syntax::UExpr::*;
		match source {
			Zero => UExpr::zero(),
			One => UExpr::one(),
			Add(u1, u2) => self.eval(*u1): UExpr + self.eval(*u2),
			Mul(u1, u2) => self.eval(*u1): UExpr * self.eval(*u2): UExpr,
			Squash(uexpr) => UExpr::squash(self.eval(*uexpr)),
			Not(uexpr) => UExpr::not(self.eval(*uexpr)),
			Sum(scopes, body) => UExpr::sum(scopes, Closure::new(*body, self.clone())),
			Pred(pred) => UExpr::pred(self.eval(pred)),
			App(table, args) => UExpr::apply(self.eval(table), self.eval(args)),
		}
	}
}

impl<'e> Eval<syntax::UExpr, SUExpr> for &'e Env {
	fn eval(self, source: syntax::UExpr) -> SUExpr {
		use syntax::UExpr::*;
		match source {
			Zero => SUExpr::zero(),
			One => SUExpr::one(),
			Add(u1, u2) => self.eval(*u1): SUExpr + self.eval(*u2),
			Mul(u1, u2) => self.eval(*u1): SUExpr * self.eval(*u2): SUExpr,
			Squash(uexpr) => self.eval(*uexpr),
			Not(uexpr) => SUExpr::not(self.eval(*uexpr)),
			Sum(scopes, body) => SUExpr::sum(scopes, Closure::new(*body, self.clone())),
			Pred(pred) => SUExpr::pred(self.eval(pred)),
			App(table, args) => SUExpr::apply(self.eval(table), self.eval(args)),
		}
	}
}

impl<'e> Eval<(VL, DataType), Expr> for &'e Env {
	fn eval(self, (VL(l), ty): (VL, DataType)) -> Expr {
		assert_eq!(self.0[l].ty(), ty);
		self.0[l].clone()
	}
}

impl<'e> Eval<syntax::Relation, Relation> for &'e Env {
	fn eval(self, source: syntax::Relation) -> Relation {
		use shared::Relation::*;
		match source {
			Var(l) => Var(l),
			Lam(scopes, body) => Relation::lam(scopes, Closure::new(*body, self.clone())),
		}
	}
}
