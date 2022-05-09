use std::cell::RefCell;
use std::collections::HashMap;
use std::iter::once;
use std::ops::Mul;

use imbl::{vector, Vector};
use itertools::{Either, Itertools};
use z3::{Config, Context, Solver};

use super::shared::{Ctx, Schema};
use super::unify::{Unify, UnifyEnv};
use crate::pipeline::shared::{AppHead, DataType, Eval, Terms, VL};
use crate::pipeline::{normal, shared, syntax};

pub(crate) type Relation = shared::Relation<Closure>;
pub(crate) type Predicate = shared::Predicate<Relation>;
pub(crate) type Expr = shared::Expr<Relation>;
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

	pub fn apply(head: AppHead<Relation>, args: Vector<Expr>) -> Self {
		UExpr::term(Term { apps: vector![Application { head, args }], ..Term::default() })
	}
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Term {
	pub preds: Vector<Predicate>,
	pub squash: SUExpr,
	pub not: SUExpr,
	pub apps: Vector<Application>,
	pub stable_apps: Vector<Application>,
	pub sums: Vector<Summation>,
}

impl Default for Term {
	fn default() -> Self {
		Term {
			preds: vector![],
			squash: SUExpr::one(),
			not: SUExpr::zero(),
			apps: vector![],
			stable_apps: vector![],
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
	pub stable_apps: Vector<Application>,
	pub sums: Vector<Summation>,
}

impl Default for STerm {
	fn default() -> Self {
		STerm {
			preds: vector![],
			not: SUExpr::zero(),
			apps: vector![],
			stable_apps: vector![],
			sums: vector![],
		}
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

	pub fn apply(head: AppHead<Relation>, args: Vector<Expr>) -> Self {
		SUExpr::term(STerm { apps: vector![Application { head, args }], ..STerm::default() })
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
		let stable_apps = self.stable_apps + rhs.stable_apps;
		let sums = self.sums + rhs.sums;
		Term { preds, squash, not, apps, stable_apps, sums }
	}
}

impl Mul for STerm {
	type Output = STerm;

	fn mul(self, rhs: Self) -> Self::Output {
		let preds = self.preds + rhs.preds;
		let not = self.not + rhs.not;
		let apps = self.apps + rhs.apps;
		let stable_apps = self.stable_apps + rhs.stable_apps;
		let sums = self.sums + rhs.sums;
		STerm { preds, not, apps, stable_apps, sums }
	}
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Env(Vector<Expr>, Vector<Schema>);

impl Env {
	pub fn new(subst: Vector<Expr>, schemas: Vector<Schema>) -> Self {
		Env(subst, schemas)
	}

	pub fn append(&self, vars: Vector<Expr>) -> Env {
		Env(self.0.clone() + vars, self.1.clone())
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
			App(table, args) => {
				use syntax::AppHead::*;
				let args = self.eval(args);
				match table {
					Var(l) => UExpr::apply(AppHead::Var(l), args),
					Lam(_, body) => (&self.append(args)).eval(*body),
					HOp(op, hop_args, rel) => {
						let head = AppHead::HOp(op, self.eval(hop_args), self.eval(rel));
						UExpr::apply(head, args)
					},
				}
			},
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
			App(table, args) => {
				use syntax::AppHead::*;
				let args = self.eval(args);
				match table {
					Var(l) => SUExpr::apply(AppHead::Var(l), args),
					Lam(_, body) => (&self.append(args)).eval(*body),
					HOp(op, hop_args, rel) => {
						let head = AppHead::HOp(op, self.eval(hop_args), self.eval(rel));
						SUExpr::apply(head, args)
					},
				}
			},
		}
	}
}

impl<'e> Eval<(VL, DataType), Expr> for &'e Env {
	fn eval(self, (VL(l), ty): (VL, DataType)) -> Expr {
		assert_eq!(self.0[l].ty(), ty, "Wrong type for {}", VL(l));
		self.0[l].clone()
	}
}

impl<'e> Eval<syntax::Relation, Relation> for &'e Env {
	fn eval(self, source: syntax::Relation) -> Relation {
		let shared::Relation(scopes, body) = source;
		Relation::new(scopes, Closure::new(*body, self.clone()))
	}
}

impl<'e> Unify<UExpr> for normal::Env<'e> {
	fn unify(self, t1: UExpr, t2: UExpr) -> bool {
		let normal::Env(context, _) = self;
		let t1: normal::UExpr = self.eval(t1);
		let t2: normal::UExpr = self.eval(t2);
		let mut config = Config::new();
		config.set_timeout_msec(2000);
		let z3_ctx = &Context::new(&config);
		let ctx = &Ctx::new(Solver::new(z3_ctx));
		let uexpr_subst = &shared::Expr::vars(0, context.clone());
		let z3_subst = &context.iter().map(|ty| ctx.var(ty, "v")).collect();
		let h_ops = &RefCell::new(HashMap::new());
		let rel_h_ops = &RefCell::new(HashMap::new());
		let env = normal::StbEnv::new(uexpr_subst, context.len(), ctx, z3_subst, h_ops, rel_h_ops);
		let t1: normal::UExpr = env.eval(t1);
		let t2: normal::UExpr = env.eval(t2);
		UnifyEnv::new(ctx, z3_subst, z3_subst).unify(&t1, &t2)
	}
}

impl normal::Env<'_> {
	pub(crate) fn degen(self, rel: Relation) -> bool {
		let shared::Relation(scopes, clos) = rel;
		let count = UExpr::sum(scopes.clone(), *clos.clone());
		let exists = UExpr::squash(SUExpr::sum(scopes, *clos));
		self.unify(count, exists)
	}
}

pub(crate) fn partition_apps(
	apps: Vector<Application>,
	schemas: &[Schema],
) -> (Vector<Application>, Vec<Vec<Predicate>>) {
	apps.into_iter().partition_map(|app| match &app.head {
		&AppHead::Var(VL(l)) => {
			let schema = &schemas[l];
			let preds = schema
				.primary
				.iter()
				.enumerate()
				.flat_map(|(j, cols)| {
					use shared::Expr::*;
					use shared::Predicate::*;
					let (keys, args): (Vec<_>, Vec<_>) =
						app.args.iter().cloned().enumerate().partition_map(|(i, arg)| {
							if cols.contains(&i) {
								Either::Left(arg)
							} else {
								Either::Right(arg)
							}
						});
					let pk = Pred(format!("rpk!{}-{}", l, j), keys.clone());
					args.into_iter()
						.enumerate()
						.map(move |(i, arg)| {
							let ty = arg.ty();
							Eq(arg, Op(format!("rpn!{}-{}-{}", l, i, j), keys.clone(), ty))
						})
						.chain(once(pk))
				})
				.collect_vec();
			if preds.is_empty() {
				Either::Left(app)
			} else {
				Either::Right(preds)
			}
		},
		AppHead::HOp(_, _, _) => Either::Left(app),
	})
}
