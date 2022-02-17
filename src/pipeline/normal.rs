use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter, Write};
use std::iter::once;

use anyhow::{bail, Error};
use imbl::{vector, Vector};
use indenter::indented;
use itertools::{Either, Itertools};
use scopeguard::defer;
use z3::ast::{exists_const, Ast, Bool, Dynamic, Int, String as Str};
use z3::{Context, FuncDecl, SatResult, Solver, Sort};

use crate::pipeline::partial::{key_constraint, Closure, Summation};
use crate::pipeline::shared::{func_app, AppHead, DataType, Eval, Schema, Terms, VL};
use crate::pipeline::{partial, shared};

pub(crate) type Relation = shared::Relation<UExpr>;
type Predicate = shared::Predicate<Relation>;
pub(crate) type Expr = shared::Expr<Relation>;
type Application = shared::Application<Relation>;

pub type UExpr = Terms<Scoped<Inner>>;

pub type SUExpr = Terms<Scoped<SInner>>;

#[derive(Clone, Debug, Default, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Scoped<I> {
	pub scopes: Vector<DataType>,
	pub inner: I,
}

impl<I: Clone> Terms<Scoped<I>> {
	pub fn inner(inner: I) -> Self {
		Terms(vector![Scoped { scopes: vector![], inner }])
	}

	pub fn under(scopes: Vector<DataType>, terms: Terms<Scoped<I>>) -> Self {
		terms
			.into_iter()
			.map(|term| Scoped { scopes: scopes.clone() + term.scopes, inner: term.inner })
			.collect()
	}
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Inner {
	pub preds: Vector<Predicate>,
	pub squash: SUExpr,
	pub not: SUExpr,
	pub apps: Vector<Application>,
}

impl Default for Inner {
	fn default() -> Self {
		Inner { preds: vector![], squash: SUExpr::one(), not: SUExpr::zero(), apps: vector![] }
	}
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct SInner {
	pub preds: Vector<Predicate>,
	pub not: SUExpr,
	pub apps: Vector<Application>,
}

impl Default for SInner {
	fn default() -> Self {
		SInner { preds: vector![], not: SUExpr::zero(), apps: vector![] }
	}
}

impl<I: Display> Display for Scoped<I> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		writeln!(f, "∑ {:?} {{", self.scopes)?;
		writeln!(indented(f).with_str("\t"), "{}", self.inner)?;
		write!(f, "}}")
	}
}

impl Display for Inner {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let exps = self
			.preds
			.iter()
			.map(|pred| format!("⟦{}⟧", pred))
			.chain(once(format!("¬({})", self.not)))
			.chain(once(format!("‖{}‖", self.squash)))
			.chain(self.apps.iter().map(|app| format!("{}", app)))
			.format(" × ");
		write!(f, "{}", exps)
	}
}

impl Display for SInner {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let exps = self
			.preds
			.iter()
			.map(|pred| format!("⟦{}⟧", pred))
			.chain(once(format!("¬({})", self.not)))
			.chain(self.apps.iter().map(|app| format!("{}", app)))
			.format(" × ");
		write!(f, "{}", exps)
	}
}

impl Eval<partial::UExpr, UExpr> for (usize, &[Schema]) {
	fn eval(self, source: partial::UExpr) -> UExpr {
		let (lvl, schemas) = self;
		source
			.into_iter()
			.flat_map(|mut t| {
				if let Some(Summation { scopes, summand }) = t.sums.pop_front() {
					let entries = shared::Expr::vars(lvl, scopes.clone());
					let level = lvl + entries.len();
					let sum_body: partial::UExpr =
						(&summand.env.append(entries)).eval(summand.body);
					shared::Terms::under(scopes, (level, schemas).eval(sum_body * t))
				} else {
					let (apps, preds): (_, Vector<_>) =
						t.apps.clone().into_iter().partition_map(|app| match &app.head {
							&AppHead::Var(VL(l)) => {
								let schema = &schemas[l];
								match schema.primary.first() {
									None => Either::Left(app),
									Some(cols) => Either::Right(key_constraint(l, cols, app.args)),
								}
							},
							AppHead::HOp(_, _, _) => Either::Left(app),
						});
					UExpr::inner(Inner {
						preds: self.eval(t.preds + preds.into_iter().flatten().collect()),
						squash: self.eval(t.squash),
						not: self.eval(t.not),
						apps: self.eval(apps),
					})
				}
			})
			.collect()
	}
}

impl Eval<partial::SUExpr, SUExpr> for (usize, &[Schema]) {
	fn eval(self, source: partial::SUExpr) -> SUExpr {
		let (lvl, schemas) = self;
		source
			.into_iter()
			.flat_map(|mut t| {
				if let Some(Summation { scopes, summand }) = t.sums.pop_front() {
					let entries = shared::Expr::vars(lvl, scopes.clone());
					let level = lvl + entries.len();
					let sum_body: partial::SUExpr =
						(&summand.env.append(entries)).eval(summand.body);
					shared::Terms::under(scopes, (level, schemas).eval(sum_body * t))
				} else {
					SUExpr::inner(SInner {
						preds: self.eval(t.preds),
						not: self.eval(t.not),
						apps: self.eval(t.apps),
					})
				}
			})
			.collect()
	}
}

impl Eval<(VL, DataType), Expr> for (usize, &[Schema]) {
	fn eval(self, source: (VL, DataType)) -> Expr {
		Expr::Var(source.0, source.1)
	}
}

impl Eval<partial::Relation, Relation> for (usize, &[Schema]) {
	fn eval(self, source: partial::Relation) -> Relation {
		use shared::Relation::*;
		let (lvl, schemas) = self;
		match source {
			Var(l) => Var(l),
			Lam(scopes, closure) => {
				let Closure { env, body } = *closure;
				let vars = shared::Expr::vars(lvl, scopes.clone());
				let level = lvl + vars.len();
				Relation::lam(scopes, (level, schemas).eval((&env.append(vars)).eval(body)))
			},
			HOp(op, args, rel) => HOp(op, self.eval(args), self.eval(rel)),
		}
	}
}

#[derive(Copy, Clone)]
pub struct StbEnv<'e, 'c>(pub &'e Vector<Expr>, pub usize, Z3Env<'e, 'c>);

pub type HOpMap<'c> = HashMap<(String, Vec<Expr>, Relation, Vector<Dynamic<'c>>), Dynamic<'c>>;

pub type RelHOpMap<'c> = HashMap<(String, Vec<Expr>, Relation, Vector<Dynamic<'c>>), usize>;

#[derive(Copy, Clone)]
pub struct Z3Env<'e, 'c>(
	&'e Solver<'c>,
	&'e Vector<Dynamic<'c>>,
	&'e RefCell<HOpMap<'c>>,
	&'e RefCell<RelHOpMap<'c>>,
);

impl<'e, 'c> Z3Env<'e, 'c> {
	pub fn new(
		solver: &'e Solver<'c>,
		subst: &'e Vector<Dynamic<'c>>,
		h_ops: &'e RefCell<HOpMap<'c>>,
		rel_h_ops: &'e RefCell<RelHOpMap<'c>>,
	) -> Self {
		Z3Env(solver, subst, h_ops, rel_h_ops)
	}

	fn update(self, subst: &'e Vector<Dynamic<'c>>) -> Self {
		Z3Env(self.0, subst, self.2, self.3)
	}

	fn extend(self, scopes: Vector<DataType>) -> Vector<Dynamic<'c>> {
		let ctx = self.0.get_context();
		let vars = scopes.into_iter().map(|ty| shared::var(ctx, ty, "v")).collect();
		self.1.clone() + vars
	}
}

impl<'e, 'c> StbEnv<'e, 'c> {
	pub fn new(
		subst: &'e Vector<Expr>,
		level: usize,
		solver: &'e Solver<'c>,
		z3_subst: &'e Vector<Dynamic<'c>>,
		h_ops: &'e RefCell<HOpMap<'c>>,
		rel_h_ops: &'e RefCell<RelHOpMap<'c>>,
	) -> Self {
		StbEnv(subst, level, Z3Env::new(solver, z3_subst, h_ops, rel_h_ops))
	}

	fn update(self, subst: &'e Vector<Expr>, level: usize, z3_env: Z3Env<'e, 'c>) -> Self {
		StbEnv(subst, level, z3_env)
	}

	fn extend(self, scopes: Vector<DataType>) -> (Vector<Expr>, usize) {
		let level = self.1 + scopes.len();
		let uexpr_vars =
			scopes.into_iter().enumerate().map(|(l, ty)| Expr::Var(VL(self.1 + l), ty)).collect();
		(self.0 + &uexpr_vars, level)
	}
}

impl<'e, 'c: 'e> Eval<Scoped<Inner>, Option<Scoped<Inner>>> for StbEnv<'e, 'c> {
	fn eval(self, source: Scoped<Inner>) -> Option<Scoped<Inner>> {
		let StbEnv(subst, level, z3_env) = self;
		let solver = z3_env.0;
		solver.push();
		defer!(solver.pop(1));
		let z3_subst = &z3_env.extend(source.scopes.clone());
		let z3_env = z3_env.update(z3_subst);
		let constraint = z3_env.eval(&source.inner);
		solver.assert(&constraint);
		let asts = z3_subst.iter().map(|v| v as &dyn Ast).collect_vec();
		let (ids, res) = solver.get_implied_equalities(asts.as_slice());
		match dbg!(res) {
			SatResult::Unsat => None,
			SatResult::Unknown => {
				let (ref subst, level) = self.extend(source.scopes.clone());
				let inner = self.update(subst, level, z3_env).eval(source.inner);
				Some(Scoped { inner, ..source })
			},
			SatResult::Sat => {
				let mut scopes = vector![];
				let groups = ids.iter().enumerate().map(|(l, &g)| (g, VL(l))).collect_vec();
				let buckets: HashMap<_, _> = groups.into_iter().rev().collect();
				let mut new_subst = subst.clone();
				for l in 0..source.scopes.len() {
					let vl = l + subst.len();
					let &VL(rep) = buckets.get(&ids[vl]).unwrap();
					let target = new_subst.get(rep).cloned().unwrap_or_else(|| {
						let ty = source.scopes[l].clone();
						scopes.push_back(ty.clone());
						Expr::Var(VL(level + scopes.len() - 1), ty)
					});
					new_subst.push_back(target);
				}
				let inner =
					self.update(&new_subst, level + scopes.len(), z3_env).eval(source.inner);
				Some(Scoped { inner, scopes })
			},
		}
	}
}

impl<'e, 'c: 'e> Eval<Scoped<SInner>, Scoped<SInner>> for StbEnv<'e, 'c> {
	fn eval(self, source: Scoped<SInner>) -> Scoped<SInner> {
		let z3_env = self.2;
		let (ref subst, level) = self.extend(source.scopes.clone());
		let z3_subst = &z3_env.extend(source.scopes.clone());
		Scoped {
			inner: self.update(subst, level, z3_env.update(z3_subst)).eval(source.inner),
			..source
		}
	}
}

impl<'e, 'c: 'e> Eval<Inner, Inner> for StbEnv<'e, 'c> {
	fn eval(self, source: Inner) -> Inner {
		let preds = self.eval(source.preds);
		let squash = self.eval(source.squash);
		let not = self.eval(source.not);
		let apps = self.eval(source.apps);
		Inner { preds, squash, not, apps }
	}
}

impl<'e, 'c: 'e> Eval<SInner, SInner> for StbEnv<'e, 'c> {
	fn eval(self, source: SInner) -> SInner {
		let preds = self.eval(source.preds);
		let not = self.eval(source.not);
		let apps = self.eval(source.apps);
		SInner { preds, not, apps }
	}
}

impl<'e, 'c: 'e> Eval<(VL, DataType), Expr> for StbEnv<'e, 'c> {
	fn eval(self, (VL(l), ty): (VL, DataType)) -> Expr {
		assert_eq!(self.0[l].ty(), ty, "wrong type for {}", VL(l));
		self.0[l].clone()
	}
}

impl<'e, 'c: 'e> Eval<Relation, Relation> for StbEnv<'e, 'c> {
	fn eval(self, source: Relation) -> Relation {
		let z3_env = self.2;
		use shared::Relation::*;
		match source {
			Var(l) => Var(l),
			Lam(scopes, body) => {
				let z3_subst = &z3_env.extend(scopes.clone());
				let (ref subst, level) = self.extend(scopes.clone());
				Lam(
					scopes,
					Box::new(self.update(subst, level, z3_env.update(z3_subst)).eval(*body)),
				)
			},
			HOp(op, args, rel) => HOp(op, self.eval(args), self.eval(rel)),
		}
	}
}

impl<'e, 'c: 'e> Eval<UExpr, UExpr> for StbEnv<'e, 'c> {
	fn eval(self, source: UExpr) -> UExpr {
		source.0.into_iter().filter_map(|term| self.eval(term)).collect()
	}
}

impl<'e, 'c: 'e> Eval<&SUExpr, Bool<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &SUExpr) -> Bool<'c> {
		let ctx = self.0.get_context();
		let bools = source.into_iter().map(|term| self.eval(term)).collect_vec();
		Bool::or(ctx, &bools.iter().collect_vec())
	}
}

impl<'e, 'c: 'e> Eval<&Scoped<SInner>, Bool<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Scoped<SInner>) -> Bool<'c> {
		let ctx = self.0.get_context();
		let inner = &source.inner;
		let level = self.1.len();
		let subst = &self.extend(source.scopes.clone());
		let env = self.update(subst);
		let bools = inner
			.preds
			.iter()
			.map(|pred| env.eval(pred))
			.chain(once(env.eval(&inner.not).not()))
			.chain(env.eval(&inner.apps))
			.collect_vec();
		let vars = &(level..level + source.scopes.len()).map(|l| subst[l].clone()).collect_vec();
		let bounds = vars.iter().map(|v| v as &dyn Ast).collect_vec();
		let body = Bool::and(ctx, &bools.iter().collect_vec());
		exists_const(ctx, &bounds, &[], &body)
	}
}

impl<'e, 'c> Eval<&Inner, (Bool<'c>, Int<'c>)> for Z3Env<'e, 'c> {
	fn eval(self, source: &Inner) -> (Bool<'c>, Int<'c>) {
		let bool = self.eval(source);
		let apps = self.eval(&source.apps);
		let ctx = self.0.get_context();
		let int = if apps.is_empty() {
			Int::from_i64(ctx, 0)
		} else {
			Int::mul(ctx, &apps.iter().collect_vec())
		};
		(bool, int)
	}
}

impl<'e, 'c: 'e> Eval<&Inner, Bool<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Inner) -> Bool<'c> {
		let ctx = self.0.get_context();
		let bools = self
			.eval(&source.preds)
			.into_iter()
			.chain(once(self.eval(&source.squash)))
			.chain(once(self.eval(&source.not).not()))
			.collect_vec();
		Bool::and(ctx, &bools.iter().collect_vec())
	}
}

fn table_name(head: &AppHead<Relation>, env: Z3Env) -> String {
	let Z3Env(_, subst, _, map) = env;
	match head {
		AppHead::Var(VL(l)) => "r!".to_string() + &l.to_string(),
		AppHead::HOp(op, args, rel) => {
			let len = map.borrow().len();
			"rh!".to_string()
				+ &map
					.borrow_mut()
					.entry((op.clone(), args.clone(), *rel.clone(), subst.clone()))
					.or_insert(len)
					.to_string()
		},
	}
}

impl<'e, 'c: 'e> Eval<&Application, Bool<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Application) -> Bool<'c> {
		let args = source.args.iter().map(|v| self.eval(v)).collect_vec();
		func_app(self.0.get_context(), table_name(&source.head, self), args, DataType::Boolean)
			.as_bool()
			.unwrap()
	}
}

impl<'e, 'c: 'e> Eval<&Application, Int<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Application) -> Int<'c> {
		let args = source.args.iter().map(|v| self.eval(v)).collect_vec();
		func_app(self.0.get_context(), table_name(&source.head, self), args, DataType::Integer)
			.as_int()
			.unwrap()
	}
}

impl<'e, 'c: 'e> Eval<&Expr, Dynamic<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Expr) -> Dynamic<'c> {
		let Z3Env(solver, subst, h_ops, _) = self;
		let ctx = solver.get_context();
		let parse = |ctx, input: &str, ty| {
			use DataType::*;
			Ok(match ty {
				&Integer => Int::from_i64(ctx, input.parse()?).into(),
				&Boolean => Bool::from_bool(ctx, input.to_lowercase().parse()?).into(),
				&String => Str::from_str(ctx, input).unwrap().into(),
				_ => bail!("unsupported type {:?} for constant {}", ty, input),
			})
		};
		match source {
			Expr::Var(v, _) => subst[v.0].clone(),
			Expr::Op(op, args, ty) if args.is_empty() => parse(ctx, op, ty).unwrap(),
			Expr::Op(op, args, ty) => {
				let args = args.iter().map(|arg| self.eval(arg)).collect_vec();
				match op.as_str() {
					num_op @ ("+" | "-" | "*" | "/" | "%") => {
						let args = args.into_iter().map(|arg| arg.as_int().unwrap()).collect_vec();
						match num_op {
							"+" => Int::add(ctx, &args.iter().collect_vec()),
							"-" => Int::sub(ctx, &args.iter().collect_vec()),
							"*" => Int::mul(ctx, &args.iter().collect_vec()),
							"/" => args[0].div(&args[1]),
							"%" => args[0].modulo(&args[1]),
							_ => unreachable!(),
						}
						.into()
					},
					cmp @ (">" | "<" | ">=" | "<=") => {
						let args = args.into_iter().map(|arg| arg.as_int().unwrap()).collect_vec();
						match cmp {
							">" => args[0].gt(&args[1]),
							"<" => args[0].lt(&args[1]),
							">=" => args[0].ge(&args[1]),
							"<=" => args[0].le(&args[1]),
							_ => unreachable!(),
						}
						.into()
					},
					"=" => args[0]._eq(&args[1]).into(),
					"CASE" if args.len() == 3 => args[0].as_bool().unwrap().ite(&args[1], &args[2]),
					op => {
						shared::func_app(ctx, "f!".to_owned() + &op.to_string(), args, ty.clone())
					},
				}
			},
			Expr::HOp(f, args, rel, ty) => h_ops
				.borrow_mut()
				.entry((f.clone(), args.clone(), *rel.clone(), subst.clone()))
				.or_insert_with(|| shared::var(ctx, ty.clone(), "h"))
				.clone(),
		}
	}
}

impl<'e, 'c: 'e> Eval<&Predicate, Bool<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Predicate) -> Bool<'c> {
		let ctx = self.0.get_context();
		match source {
			Predicate::Eq(e1, e2) => self.eval(e1)._eq(&self.eval(e2)),
			Predicate::Pred(pred, args) => self
				.eval(&Expr::Op(pred.clone(), args.clone(), DataType::Boolean))
				.as_bool()
				.unwrap(),
			Predicate::Null(expr) => {
				// TODO: Proper NULL handling
				let expr = &self.eval(expr);
				let f = FuncDecl::new(ctx, "null", &[&expr.get_sort()], &Sort::bool(ctx));
				f.apply(&[expr]).as_bool().unwrap()
			},
			Predicate::Bool(expr) => self.eval(expr).as_bool().unwrap(),
			p => panic!("Unhandled predicate translation for {:?}", p),
		}
	}
}
