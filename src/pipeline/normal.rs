use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter, Write};
use std::iter::once;

use anyhow::{bail, Error};
use imbl::{vector, Vector};
use indenter::indented;
use itertools::{Either, Itertools};
use num::ToPrimitive;
use scopeguard::defer;
use z3::ast::{exists_const, Ast, Bool, Dynamic, Int, Real as Re, String as Str};
use z3::{Context, FuncDecl, SatResult, Solver, Sort};

use crate::pipeline::partial::{partition_apps, Closure, STerm, Summation, Term};
use crate::pipeline::shared::DataType::{Integer, Real};
use crate::pipeline::shared::{func_app, AppHead, DataType, Eval, Schema, Terms, VL};
use crate::pipeline::unify::Unify;
use crate::pipeline::{partial, shared};

pub(crate) type Relation = shared::Relation<UExpr>;
type Predicate = shared::Predicate<Relation>;
pub(crate) type Expr = shared::Expr<Relation>;
type Application = shared::Application<Relation>;

pub type UExpr = Terms<BiScoped<Inner>>;

pub type SUExpr = Terms<Scoped<SInner>>;

impl UExpr {
	pub fn inner(inner: Inner) -> Self {
		Terms(vector![BiScoped { keys: vector![], deps: vector![], inner }])
	}

	pub fn under(scopes: Vector<DataType>, terms: UExpr) -> Self {
		terms
			.into_iter()
			.map(|term| BiScoped { keys: scopes.clone() + term.keys, ..term })
			.collect()
	}
}

impl SUExpr {
	pub fn inner(inner: SInner) -> Self {
		Terms(vector![Scoped { scopes: vector![], inner }])
	}

	pub fn under(scopes: Vector<DataType>, terms: SUExpr) -> Self {
		terms
			.into_iter()
			.map(|term| Scoped { scopes: scopes.clone() + term.scopes, inner: term.inner })
			.collect()
	}
}

#[derive(Copy, Clone)]
pub struct Env<'e>(pub &'e Vector<DataType>, pub &'e [Schema]);

impl<'e> Env<'e> {
	pub fn new(context: &'e Vector<DataType>, schemas: &'e [Schema]) -> Self {
		Env(context, schemas)
	}
}

impl<'e> Eval<partial::UExpr, UExpr> for Env<'e> {
	fn eval(self, source: partial::UExpr) -> UExpr {
		source.into_iter().flat_map(|t| self.eval(t)).collect()
	}
}

impl<'e> Eval<partial::Term, UExpr> for Env<'e> {
	fn eval(self, mut source: Term) -> UExpr {
		let Env(context, schemas) = self;
		let lvl = context.len();
		if let Some(Summation { scopes, summand }) = source.sums.pop_front() {
			let entries = shared::Expr::vars(lvl, scopes.clone());
			let sum_body: partial::UExpr = (&summand.env.append(entries)).eval(summand.body);
			let context = context + &scopes;
			UExpr::under(scopes, Env(&context, schemas).eval(sum_body * source))
		} else if let Some(app) = source.apps.pop_front() {
			match &app.head {
				AppHead::Var(_) => {
					source.stable_apps.push_back(app);
					self.eval(source)
				},
				AppHead::HOp(op, args, rel) => {
					if op == "limit"
						&& &args[0]
							== &partial::Expr::Op("1".to_string(), vec![], DataType::Integer)
					{
						let shared::Relation(scopes, clos) = *rel.clone();
						use partial::{SUExpr, UExpr};
						let count = UExpr::sum(scopes.clone(), *clos.clone());
						let exist = UExpr::squash(SUExpr::sum(scopes.clone(), *clos.clone()));
						if self.unify(count, exist) {
							let body: UExpr = (&clos.env.append(app.args)).eval(clos.body);
							self.eval(body * source)
						} else {
							source.stable_apps.push_back(app);
							self.eval(source)
						}
					} else {
						source.stable_apps.push_back(app);
						self.eval(source)
					}
				},
			}
		} else {
			let (apps, preds) = partition_apps(source.stable_apps, schemas);
			UExpr::inner(Inner {
				preds: self.eval(source.preds + preds.into_iter().flatten().collect()),
				squash: self.eval(source.squash),
				not: self.eval(source.not),
				apps: self.eval(apps),
			})
		}
	}
}

impl<'e> Eval<partial::SUExpr, SUExpr> for Env<'e> {
	fn eval(self, source: partial::SUExpr) -> SUExpr {
		source.into_iter().flat_map(|mut t| self.eval(t)).collect()
	}
}

impl<'e> Eval<partial::STerm, SUExpr> for Env<'e> {
	fn eval(self, mut source: STerm) -> SUExpr {
		let Env(context, schemas) = self;
		let lvl = context.len();
		if let Some(Summation { scopes, summand }) = source.sums.pop_front() {
			let entries = shared::Expr::vars(lvl, scopes.clone());
			let sum_body: partial::SUExpr = (&summand.env.append(entries)).eval(summand.body);
			let context = context + &scopes;
			SUExpr::under(scopes, Env(&context, schemas).eval(sum_body * source))
		} else if let Some(app) = source.apps.pop_front() {
			match &app.head {
				AppHead::Var(_) => {
					source.stable_apps.push_back(app);
					self.eval(source)
				},
				AppHead::HOp(op, args, rel) => {
					if op == "limit"
						&& &args[0]
							== &partial::Expr::Op("1".to_string(), vec![], DataType::Integer)
					{
						let shared::Relation(scopes, clos) = *rel.clone();
						use partial::{SUExpr, UExpr};
						let count = UExpr::sum(scopes.clone(), *clos.clone());
						let exist = UExpr::squash(SUExpr::sum(scopes.clone(), *clos.clone()));
						if self.unify(count, exist) {
							let body: SUExpr = (&clos.env.append(app.args)).eval(clos.body);
							self.eval(body * source)
						} else {
							source.stable_apps.push_back(app);
							self.eval(source)
						}
					} else {
						source.stable_apps.push_back(app);
						self.eval(source)
					}
				},
			}
		} else {
			let (apps, preds) = partition_apps(source.stable_apps, schemas);
			SUExpr::inner(SInner {
				preds: self.eval(source.preds + preds.into_iter().flatten().collect()),
				not: self.eval(source.not),
				apps: self.eval(apps),
			})
		}
	}
}

impl<'e> Eval<(VL, DataType), Expr> for Env<'e> {
	fn eval(self, source: (VL, DataType)) -> Expr {
		Expr::Var(source.0, source.1)
	}
}

impl<'e> Eval<partial::Relation, Relation> for Env<'e> {
	fn eval(self, source: partial::Relation) -> Relation {
		let Env(context, schemas) = self;
		let lvl = context.len();
		let shared::Relation(scopes, clos) = source;
		let Closure { env, body } = *clos;
		let vars = shared::Expr::vars(lvl, scopes.clone());
		let context = context + &scopes;
		let body: partial::UExpr = (&env.append(vars)).eval(body);
		Relation::new(scopes, Env(&context, schemas).eval(body))
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

	pub fn substs(self) -> &'e Vector<Dynamic<'c>> {
		self.1
	}

	pub fn solver(self) -> &'e Solver<'c> {
		self.0
	}

	pub fn update(self, subst: &'e Vector<Dynamic<'c>>) -> Self {
		Z3Env(self.0, subst, self.2, self.3)
	}

	pub fn append(self, scopes: Vector<DataType>) -> Vector<Dynamic<'c>> {
		let ctx = self.0.get_context();
		let vars = scopes.into_iter().map(|ty| shared::var(ctx, ty, "v")).collect();
		self.1.clone() + vars
	}

	pub fn extend(self, scopes: Vector<DataType>) -> Vector<Dynamic<'c>> {
		let ctx = self.0.get_context();
		scopes.into_iter().map(|ty| shared::var(ctx, ty, "v")).collect()
	}
}

impl<'e, 'c> Eval<&SUExpr, Bool<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &SUExpr) -> Bool<'c> {
		let ctx = self.0.get_context();
		let bools = source.into_iter().map(|term| self.eval(term)).collect_vec();
		Bool::or(ctx, &bools.iter().collect_vec())
	}
}

impl<'e, 'c> Eval<&Scoped<SInner>, Bool<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Scoped<SInner>) -> Bool<'c> {
		let ctx = self.0.get_context();
		let inner = &source.inner;
		let level = self.1.len();
		let subst = &self.append(source.scopes.clone());
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

impl<'e, 'c> Eval<&Inner, Bool<'c>> for Z3Env<'e, 'c> {
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

impl<'e, 'c> Eval<&Application, Bool<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Application) -> Bool<'c> {
		let args = source.args.iter().map(|v| self.eval(v)).collect_vec();
		func_app(
			self.0.get_context(),
			table_name(&source.head, self) + "p",
			args,
			DataType::Boolean,
		)
		.as_bool()
		.unwrap()
	}
}

impl<'e, 'c> Eval<&Application, Int<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Application) -> Int<'c> {
		let args = source.args.iter().map(|v| self.eval(v)).collect_vec();
		func_app(self.0.get_context(), table_name(&source.head, self), args, DataType::Integer)
			.as_int()
			.unwrap()
	}
}

impl<'e, 'c> Eval<&Expr, Dynamic<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Expr) -> Dynamic<'c> {
		let Z3Env(solver, subst, h_ops, _) = self;
		let ctx = solver.get_context();
		let parse = |ctx, input: &str, ty| {
			use DataType::*;
			Ok(match ty {
				&Integer => Int::from_i64(ctx, input.parse()?).into(),
				&Real => {
					let r: f64 = input.parse()?;
					let r = num::rational::Ratio::from_float(r).unwrap();
					Re::from_real(ctx, r.numer().to_i32().unwrap(), r.denom().to_i32().unwrap())
						.into()
				},
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
					num_op @ ("+" | "-" | "*" | "/" | "%" | "POWER") if ty == &Integer => {
						let args = args.into_iter().map(|arg| arg.as_int().unwrap()).collect_vec();
						match num_op {
							"+" => Int::add(ctx, &args.iter().collect_vec()),
							"-" => Int::sub(ctx, &args.iter().collect_vec()),
							"*" => Int::mul(ctx, &args.iter().collect_vec()),
							"/" => args[0].div(&args[1]),
							"%" => args[0].modulo(&args[1]),
							"POWER" => args[0].power(&args[1]),
							_ => unreachable!(),
						}
						.into()
					},
					num_op @ ("+" | "-" | "*" | "/" | "POWER") if ty == &Real => {
						let args = args.into_iter().map(|arg| arg.as_real().unwrap()).collect_vec();
						match num_op {
							"+" => Re::add(ctx, &args.iter().collect_vec()),
							"-" => Re::sub(ctx, &args.iter().collect_vec()),
							"*" => Re::mul(ctx, &args.iter().collect_vec()),
							"/" => args[0].div(&args[1]),
							"POWER" => args[0].power(&args[1]),
							_ => unreachable!(),
						}
						.into()
					},
					cmp @ (">" | "<" | ">=" | "<=") if matches!(args[0].as_int(), Some(_)) => {
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
					cmp @ (">" | "<" | ">=" | "<=") if matches!(args[0].as_real(), Some(_)) => {
						let args = args.into_iter().map(|arg| arg.as_real().unwrap()).collect_vec();
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
					"<>" => args[0]._eq(&args[1]).not().into(),
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

impl<'e, 'c> Eval<&Predicate, Bool<'c>> for Z3Env<'e, 'c> {
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

#[derive(Clone, Debug, Default, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct BiScoped<I> {
	pub keys: Vector<DataType>,
	pub deps: Vector<DataType>,
	pub inner: I,
}

#[derive(Clone, Debug, Default, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Scoped<I> {
	pub scopes: Vector<DataType>,
	pub inner: I,
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

impl<I: Display> Display for BiScoped<I> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		writeln!(f, "∑ {:?} {:?} {{", self.keys, self.deps)?;
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
