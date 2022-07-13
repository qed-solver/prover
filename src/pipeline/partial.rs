use std::cell::RefCell;
use std::collections::HashMap;
use std::iter::once;
use std::ops::Mul;
use std::rc::Rc;

use imbl::{vector, Vector};
use itertools::{Either, Itertools};
use z3::{Config, Context, Solver};

use super::nom::Z3Env;
use super::shared::{Ctx, Schema};
use super::stable;
use super::unify::{Unify, UnifyEnv};
use crate::pipeline::shared::{AppHead, DataType, Eval, Terms, VL};
use crate::pipeline::{normal, shared, syntax};

pub type Expr = shared::Expr<Relation>;
pub type Predicate = shared::Predicate<Relation>;
pub type Logic = shared::Logic<Relation, LogicRel>;
pub type Application = shared::Application<Relation>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Relation {
	Var(VL),
	HOp(String, Vec<Expr>, Box<Relation>),
	Lam(Vector<DataType>, Env, syntax::UExpr),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum LogicRel {
	Var(VL),
	HOp(String, Vec<Expr>, Box<Relation>),
	Lam(Vector<DataType>, Env, syntax::UExpr),
}

impl LogicRel {
	pub fn scope(&self, schemas: &Vector<Schema>) -> Vector<DataType> {
		use LogicRel::*;
		match self {
			Var(l) => schemas[l.0].types.clone().into(),
			HOp(_, _, rel) => rel.scope(schemas),
			Lam(scopes, _, _) => scopes.clone(),
		}
	}
}

impl Relation {
	pub fn app(self, args: Vector<Expr>) -> UExpr {
		use Relation::*;
		match self {
			Var(l) => UExpr::apply(AppHead::Var(l), args),
			HOp(op, hop_args, rel) => UExpr::apply(AppHead::HOp(op, hop_args, rel), args),
			Lam(_, env, body) => (&env.append(args)).eval(body),
		}
	}

	pub fn app_logic(self, args: Vector<Expr>) -> Logic {
		use Relation::*;
		match self {
			Var(l) => Logic::Neutral(Application::new(AppHead::Var(l), args)),
			HOp(op, h_args, rel) => {
				Logic::Neutral(Application::new(AppHead::HOp(op, h_args, rel), args))
			},
			Lam(_, env, body) => (&env.append(args)).eval(body),
		}
	}

	pub fn scope(&self, schemas: &Vector<Schema>) -> Vector<DataType> {
		use Relation::*;
		match self {
			Var(l) => schemas[l.0].types.clone().into(),
			HOp(_, _, rel) => rel.scope(schemas),
			Lam(scopes, _, _) => scopes.clone(),
		}
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

	pub fn apply(head: AppHead<Relation>, args: Vector<Expr>) -> Self {
		UExpr::term(Term { apps: vector![Application { head, args }], ..Term::default() })
	}
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Term {
	pub logic: Logic,
	pub apps: Vector<Application>,
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
			Zero => UExpr::zero(),
			One => UExpr::one(),
			Add(u1, u2) => self.eval(*u1): UExpr + self.eval(*u2),
			Mul(u1, u2) => self.eval(*u1): UExpr * self.eval(*u2): UExpr,
			Squash(uexpr) => UExpr::logic(self.eval(*uexpr)),
			Not(uexpr) => UExpr::logic(Logic::neg(self.eval(*uexpr))),
			Sum(scopes, body) => UExpr::sum(Relation::Lam(scopes, self.clone(), *body)),
			Pred(pred) => UExpr::logic(Logic::Pred(self.eval(pred))),
			App(table, args) => self.eval(table).app(self.eval(args)),
		}
	}
}

impl Eval<syntax::UExpr, Logic> for &Env {
	fn eval(self, source: syntax::UExpr) -> Logic {
		use syntax::UExpr::*;
		match source {
			Zero => Logic::ff(),
			One => Logic::tt(),
			Add(u1, u2) => self.eval(*u1): Logic + self.eval(*u2),
			Mul(u1, u2) => self.eval(*u1): Logic * self.eval(*u2): Logic,
			Squash(uexpr) => self.eval(*uexpr),
			Not(uexpr) => Logic::neg(self.eval(*uexpr)),
			Sum(scopes, body) => Logic::Exists(LogicRel::Lam(scopes, self.clone(), *body)),
			Pred(pred) => Logic::Pred(self.eval(pred)),
			App(table, args) => {
				use syntax::Relation::*;
				let args = self.eval(args);
				match table {
					Var(l) => Logic::Neutral(Application::new(AppHead::Var(l), args)),
					Lam(_, body) => (&self.append(args)).eval(*body),
					HOp(op, hop_args, rel) => {
						let head = AppHead::HOp(op, self.eval(hop_args), self.eval(rel));
						Logic::Neutral(Application::new(head, args))
					},
				}
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
			Var(t) => Relation::Var(t),
			HOp(name, args, rel) => Relation::HOp(name, self.eval(args), self.eval(rel)),
			Lam(scopes, body) => Relation::Lam(scopes, self.clone(), *body),
		}
	}
}

impl Unify<UExpr> for &normal::Env {
	fn unify(self, t1: UExpr, t2: UExpr) -> bool {
		let t1: normal::UExpr = self.eval(t1);
		let t2: normal::UExpr = self.eval(t2);
		let mut config = Config::new();
		config.set_timeout_msec(2000);
		let z3_ctx = Context::new(&config);
		let ctx = Rc::new(Ctx::new(Solver::new(&z3_ctx)));
		let h_ops = Rc::new(RefCell::new(HashMap::new()));
		let rel_h_ops = Rc::new(RefCell::new(HashMap::new()));
		let env = &stable::Env(vector![], 0, Z3Env(ctx.clone(), vector![], h_ops, rel_h_ops));
		let t1 = env.eval(t1);
		let t2 = env.eval(t2);
		let t1: normal::UExpr = self.eval(t1);
		let t2: normal::UExpr = self.eval(t2);
		let uni_env = UnifyEnv(ctx, vector![], vector![]);
		(&uni_env).unify(&t1, &t2)
	}
}

impl normal::Env {
	pub(crate) fn degen(&self, rel: Relation) -> bool {
		use Relation::*;
		let lrel = match rel.clone() {
			Var(l) => LogicRel::Var(l),
			HOp(op, args, rel) => LogicRel::HOp(op, args, rel),
			Lam(scope, env, body) => LogicRel::Lam(scope, env, body),
		};
		self.unify(UExpr::sum(rel), UExpr::logic(Logic::Exists(lrel)))
	}
}

pub(crate) fn partition_apps(
	apps: Vector<Application>,
	schemas: &Vector<Schema>,
) -> (Vector<Application>, Logic) {
	let (apps, logics) = apps.into_iter().partition_map(|app| match &app.head {
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
				.map(Logic::Pred)
				.collect_vec();
			if preds.is_empty() {
				Either::Left(app)
			} else {
				Either::Right(Logic::And(preds.into()))
			}
		},
		AppHead::HOp(_, _, _) => Either::Left(app),
	});
	(apps, Logic::And(logics))
}
