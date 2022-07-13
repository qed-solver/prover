use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter, Write};
use std::iter::once;
use std::ops::Range;
use std::rc::Rc;

use anyhow::bail;
use imbl::{vector, Vector};
use indenter::indented;
use itertools::Itertools;
use num::ToPrimitive;
use z3::ast::{exists_const, Ast, Bool, Dynamic, Int, Real as Re, String as Str};

use super::partial::partition_apps;
use super::shared::{Ctx, Lambda};
use super::stable;
use crate::pipeline::shared::{AppHead, DataType, Eval, Schema, Terms, VL};
use crate::pipeline::{partial, shared};

pub type Relation = Lambda<UExpr>;

pub type Predicate = shared::Predicate<Relation>;
pub type Expr = shared::Expr<Relation>;
pub type Application = shared::Application<Relation>;
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct LogicRel(pub Vector<DataType>, pub Box<Logic>);
pub type Logic = shared::Logic<Relation, LogicRel>;

pub type UExpr = Terms<Term>;

impl UExpr {
	pub fn under(scope: Vector<DataType>, terms: UExpr) -> Self {
		terms.into_iter().map(|term| Term { scope: scope.clone() + term.scope, ..term }).collect()
	}
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Term {
	pub scope: Vector<DataType>,
	pub logic: Logic,
	pub apps: Vector<Application>,
}

impl Term {
	pub fn app(app: Application) -> Self {
		Term { scope: vector![], logic: Logic::And(vector![]), apps: vector![app] }
	}
}

impl Display for LogicRel {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		writeln!(f, "{:?} {{", self.0)?;
		writeln!(indented(f).with_str("\t"), "{}", self.1)?;
		write!(f, "}}")
	}
}

impl Display for Term {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		writeln!(f, "∑ {:?} {{", self.scope)?;
		writeln!(
			indented(f).with_str("\t"),
			"⟦{}⟧ × {}",
			self.logic,
			self.apps.iter().format(" × ")
		)?;
		write!(f, "}}")
	}
}

impl Expr {
	pub(crate) fn deps(&self, vars: Range<usize>) -> HashSet<VL> {
		match self {
			Expr::Var(v, _) if vars.contains(&v.0) => once(*v).collect(),
			Expr::Var(_, _) => HashSet::new(),
			Expr::Op(_, args, _) => args.iter().flat_map(|expr| expr.deps(vars.clone())).collect(),
			Expr::HOp(_, args, rel, _) => rel
				.deps(vars.clone())
				.union(&args.iter().flat_map(|arg| arg.deps(vars.clone())).collect())
				.cloned()
				.collect(),
		}
	}
}

impl Relation {
	fn deps(&self, vars: Range<usize>) -> HashSet<VL> {
		self.1.iter().flat_map(|t| t.deps(vars.clone())).collect()
	}
}

impl Term {
	fn deps(&self, vars: Range<usize>) -> HashSet<VL> {
		self.logic
			.deps(vars.clone())
			.union(&self.apps.iter().flat_map(|app| app.deps(vars.clone())).collect())
			.cloned()
			.collect()
	}
}

impl Application {
	fn deps(&self, vars: Range<usize>) -> HashSet<VL> {
		let head_vars = match &self.head {
			AppHead::Var(_) => HashSet::new(),
			AppHead::HOp(_, args, rel) => rel
				.deps(vars.clone())
				.union(&args.iter().flat_map(|arg| arg.deps(vars.clone())).collect())
				.cloned()
				.collect(),
		};
		head_vars
			.union(&self.args.iter().flat_map(|arg| arg.deps(vars.clone())).collect())
			.cloned()
			.collect()
	}
}

impl Predicate {
	fn deps(&self, vars: Range<usize>) -> HashSet<VL> {
		use shared::Predicate::*;
		match self {
			Eq(e1, e2) => e1.deps(vars.clone()).union(&e2.deps(vars.clone())).cloned().collect(),
			Pred(_, args) => args.iter().flat_map(|arg| arg.deps(vars.clone())).collect(),
			Like(e, _) => e.deps(vars),
			Bool(e) => e.deps(vars),
		}
	}
}

impl Logic {
	fn deps(&self, vars: Range<usize>) -> HashSet<VL> {
		use shared::Logic::*;
		match self {
			Neg(l) => l.deps(vars),
			And(ls) => ls.iter().flat_map(|l| l.deps(vars.clone())).collect(),
			Or(ls) => ls.iter().flat_map(|l| l.deps(vars.clone())).collect(),
			Pred(p) => p.deps(vars),
			Neutral(app) => app.deps(vars),
			Exists(LogicRel(_, l)) => l.deps(vars),
		}
	}
}

#[derive(Clone)]
pub struct Env(pub Vector<DataType>, pub Vector<Schema>);

impl Env {
	pub fn extend(&self, scope: Vector<DataType>) -> Env {
		Env(self.0.clone() + scope, self.1.clone())
	}
}

impl Eval<partial::UExpr, UExpr> for &Env {
	fn eval(self, source: partial::UExpr) -> UExpr {
		source.into_iter().flat_map(|t| helper(self, t, vector![])).collect()
	}
}

fn helper(env: &Env, mut term: partial::Term, apps: Vector<partial::Application>) -> UExpr {
	let Env(context, schemas) = env;
	if let Some(summand) = term.sums.pop_front() {
		let scope = summand.scope(schemas);
		let vars = shared::Expr::vars(context.len(), scope.clone());
		let env = &env.extend(scope.clone());
		let body = (summand.app(vars) * term)
			.into_iter()
			.flat_map(|t| helper(env, t, apps.clone()))
			.collect();
		UExpr::under(scope, body)
	} else if let Some(app) = term.apps.pop_front() {
		match app.head {
			AppHead::HOp(op, args, _) if op == "limit" && args[0] == 0u32.into() => UExpr::zero(),
			AppHead::HOp(op, args, rel)
				if ((op == "limit" && args[0] == 1u32.into()) && env.degen(*rel.clone()))
					|| (op == "offset" && args[0] == 0u32.into()) =>
			{
				(rel.app(app.args) * term)
					.into_iter()
					.flat_map(|t| helper(env, t, apps.clone()))
					.collect()
			},
			_ => helper(env, term, apps + vector![app]),
		}
	} else {
		let (apps, logic) = partition_apps(apps, schemas);
		UExpr::term(Term {
			scope: vector![],
			logic: env.eval(term.logic * logic),
			apps: env.eval(apps),
		})
	}
}

impl Eval<partial::Application, Logic> for &Env {
	fn eval(self, app: partial::Application) -> Logic {
		match app.head {
			AppHead::HOp(op, args, _) if op == "limit" && args[0] == 0u32.into() => Logic::ff(),
			AppHead::HOp(op, args, rel)
				if ((op == "limit" && args[0] == 1u32.into()) && self.degen(*rel.clone()))
					|| (op == "offset" && args[0] == 0u32.into()) =>
			{
				self.eval(rel.app_logic(app.args))
			},
			_ => Logic::Neutral(self.eval(app)),
		}
	}
}

impl Eval<partial::LogicRel, LogicRel> for &Env {
	fn eval(self, source: partial::LogicRel) -> LogicRel {
		use partial::LogicRel::*;
		let Env(context, schemas) = self;
		let scope = source.scope(schemas);
		let env = &self.extend(scope.clone());
		let vars = Expr::vars(context.len(), scope.clone());
		LogicRel(
			scope,
			Box::new(match source {
				Var(l) => Logic::Neutral(Application::new(AppHead::Var(l), vars)),
				HOp(op, args, rel) => Logic::Neutral(Application::new(
					AppHead::HOp(op, env.eval(args), env.eval(rel)),
					vars,
				)),
				Lam(scope, clos_env, body) => {
					let vars = shared::Expr::vars(context.len(), scope.clone());
					let body: partial::Logic = (&clos_env.append(vars)).eval(body);
					env.eval(body)
				},
			}),
		)
	}
}

impl Eval<(VL, DataType), Expr> for &Env {
	fn eval(self, source: (VL, DataType)) -> Expr {
		Expr::Var(source.0, source.1)
	}
}

impl Eval<partial::Relation, Relation> for &Env {
	fn eval(self, source: partial::Relation) -> Relation {
		use partial::Relation::*;
		let Env(context, schemas) = self;
		let scope = source.scope(schemas);
		let env = &self.extend(scope.clone());
		let vars = Expr::vars(context.len(), scope.clone());
		Lambda(scope, match source {
			Var(l) => UExpr::term(Term::app(Application::new(AppHead::Var(l), vars))),
			HOp(op, args, rel) => {
				let app = Application::new(AppHead::HOp(op, env.eval(args), env.eval(rel)), vars);
				UExpr::term(Term::app(app))
			},
			Lam(scope, clos_env, body) => {
				let vars = shared::Expr::vars(context.len(), scope.clone());
				let body: partial::UExpr = (&clos_env.append(vars)).eval(body);
				env.eval(body)
			},
		})
	}
}

impl<'c> Eval<stable::Relation<'c>, Relation> for &Env {
	fn eval(self, stable::Relation(scope, env, body): stable::Relation<'c>) -> Relation {
		let lvl = self.0.len();
		log::info!("resuming with {:?}", env.2 .1);
		let body = (&env.extend(lvl, scope.clone())).eval(body);
		Lambda(scope.clone(), (&self.extend(scope)).eval(body))
	}
}

impl<'c> Eval<stable::UExpr<'c>, UExpr> for &Env {
	fn eval(self, source: stable::UExpr<'c>) -> UExpr {
		source.into_iter().map(|t| self.eval(t)).collect()
	}
}

impl<'c> Eval<stable::Term<'c>, Term> for &Env {
	fn eval(self, source: stable::Term<'c>) -> Term {
		let scope = source.scope;
		let env = &self.extend(scope.clone());
		let logic = env.eval(source.logic);
		let apps = env.eval(source.apps);
		Term { scope, logic, apps }
	}
}

impl<'c> Eval<stable::LogicRel<'c>, LogicRel> for &Env {
	fn eval(self, stable::LogicRel(scope, env, body): stable::LogicRel<'c>) -> LogicRel {
		let lvl = self.0.len();
		let body = (&env.extend(lvl, scope.clone())).eval(body);
		LogicRel(scope.clone(), Box::new((&self.extend(scope)).eval(body)))
	}
}

impl<'c> Eval<stable::Application<'c>, Logic> for &Env {
	fn eval(self, source: stable::Application<'c>) -> Logic {
		Logic::Neutral(self.eval(source))
	}
}

pub type HOpMap<'c> = HashMap<(String, Vec<Expr>, Relation, Vector<Dynamic<'c>>), Dynamic<'c>>;

pub type RelHOpMap<'c> =
	HashMap<(String, Vec<Expr>, Relation, Vector<Dynamic<'c>>, bool), (String, Vec<DataType>)>;

#[derive(Clone)]
pub struct Z3Env<'c>(
	pub Rc<Ctx<'c>>,
	pub Vector<Dynamic<'c>>,
	pub Rc<RefCell<HOpMap<'c>>>,
	pub Rc<RefCell<RelHOpMap<'c>>>,
);

impl<'c> Z3Env<'c> {
	pub fn extend(&self, scope: &Vector<DataType>) -> Self {
		log::info!("Extending {:?} from {:?}", scope, self.1);
		let vars = scope.into_iter().map(|ty| self.0.var(ty, "v")).collect();
		Z3Env(self.0.clone(), self.1.clone() + vars, self.2.clone(), self.3.clone())
	}

	pub fn extend_vars(&self, scope: &Vector<DataType>) -> (Z3Env<'c>, Vector<Dynamic<'c>>) {
		log::info!("Extending {:?} from {:?}", scope, self.1);
		let vars = scope.into_iter().map(|ty| self.0.var(ty, "v")).collect();
		(Z3Env(self.0.clone(), &self.1 + &vars, self.2.clone(), self.3.clone()), vars)
	}
}

impl<'c> Eval<&Logic, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Logic) -> Bool<'c> {
		use shared::Logic::*;
		let Z3Env(ctx, _, _, _) = self;
		let z3_ctx = ctx.z3_ctx();
		match source {
			Neg(l) => self.eval(l.as_ref()).not(),
			And(ls) => {
				let bools = self.eval(ls);
				Bool::and(z3_ctx, &bools.iter().collect_vec())
			},
			Or(ls) => {
				let bools = self.eval(ls);
				Bool::or(z3_ctx, &bools.iter().collect_vec())
			},
			Pred(pred) => self.eval(pred),
			Neutral(app) => self.eval(app),
			Exists(LogicRel(scope, l)) => {
				let (ref env, vars) = self.clone().extend_vars(&scope);
				let bounds = vars.iter().map(|v| v as &dyn Ast).collect_vec();
				let body = env.eval(l.as_ref());
				exists_const(z3_ctx, &bounds, &[], &body)
			},
		}
	}
}

impl<'c> Eval<&Vector<Application>, Int<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Vector<Application>) -> Int<'c> {
		let apps: Vector<_> = self.eval(source);
		let z3_ctx = self.0.z3_ctx();
		if apps.is_empty() {
			Int::from_i64(z3_ctx, 1)
		} else {
			Int::mul(z3_ctx, &apps.iter().collect_vec())
		}
	}
}

fn table_name(
	head: &AppHead<Relation>,
	env: &Z3Env,
	squashed: bool,
	domain: Vec<DataType>,
) -> String {
	let Z3Env(_, subst, _, map) = env;
	match head {
		AppHead::Var(VL(l)) => format!("r{}!{}", if squashed { "p" } else { "" }, l),
		AppHead::HOp(op, args, rel) => {
			let len = map.borrow().len();
			let name = format!("rh{}!{}", if squashed { "p" } else { "" }, len);
			map.borrow_mut()
				.entry((op.clone(), args.clone(), *rel.clone(), subst.clone(), squashed))
				.or_insert((name, domain))
				.0
				.clone()
		},
	}
}

impl<'c> Eval<&Application, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Application) -> Bool<'c> {
		let domain = source.args.iter().map(|a| a.ty()).collect();
		let args = source.args.iter().map(|v| self.eval(v)).collect_vec();
		let args = args.iter().collect_vec();
		self.0
			.app(
				&(table_name(&source.head, self, true, domain) + "p"),
				&args,
				&DataType::Boolean,
				false,
			)
			.as_bool()
			.unwrap()
	}
}

impl<'c> Eval<&Application, Int<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Application) -> Int<'c> {
		let domain = source.args.iter().map(|a| a.ty()).collect();
		let args = source.args.iter().map(|v| self.eval(v)).collect_vec();
		let args = args.iter().collect_vec();
		self.0
			.app(&table_name(&source.head, self, false, domain), &args, &DataType::Integer, false)
			.as_int()
			.unwrap()
	}
}

impl<'c> Eval<&Expr, Dynamic<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Expr) -> Dynamic<'c> {
		use DataType::*;
		let Z3Env(ctx, subst, h_ops, _) = self;
		let parse = |ctx: &Ctx<'c>, input: &str, ty: &DataType| -> anyhow::Result<Dynamic<'c>> {
			if input.to_lowercase() == "null" {
				let null = match ty {
					Integer => ctx.int_none(),
					Real => ctx.real_none(),
					Boolean => ctx.bool_none(),
					String => ctx.string_none(),
					_ => bail!("unsupported type {:?} for null", ty),
				};
				return Ok(null);
			}
			let z3_ctx = ctx.z3_ctx();
			Ok(match ty {
				Integer => ctx.int_some(Int::from_i64(z3_ctx, input.parse()?)),
				Real => {
					let r: f32 = input.parse()?;
					let r = num::rational::Ratio::from_float(r).unwrap();
					ctx.real_some(Re::from_real(
						z3_ctx,
						r.numer().to_i32().unwrap(),
						r.denom().to_i32().unwrap(),
					))
				},
				Boolean => ctx.bool_some(Bool::from_bool(z3_ctx, input.to_lowercase().parse()?)),
				String => ctx.string_some(Str::from_str(z3_ctx, input).unwrap()),
				_ => bail!("unsupported type {:?} for constant {}", ty, input),
			})
		};
		match source {
			Expr::Var(v, _) => subst[v.0].clone(),
			Expr::Op(op, args, ty) if args.is_empty() => parse(ctx.as_ref(), op, ty).unwrap(),
			Expr::Op(op, expr_args, ty) => {
				let args = expr_args.iter().map(|arg| self.eval(arg)).collect_vec();
				let args = args.iter().collect_vec();
				match op.as_str() {
					num_op @ ("+" | "-" | "*" | "/" | "%" /*| "POWER" */) if ty == &Integer => {
						match num_op {
							"+" => ctx.int_add_v(&args),
							"-" => ctx.int_sub_v(&args),
							"*" => ctx.int_mul_v(&args),
							"/" => ctx.int_div(args[0], args[1]),
							"%" => ctx.int_modulo(args[0], args[1]),
							// "POWER" => ctx.int_power(args[0], args[1]),
							_ => unreachable!(),
						}
					},
					num_op @ ("+" | "-" | "*" | "/" /*| "POWER" */) if ty == &Real => match num_op {
						"+" => ctx.real_add_v(&args),
						"-" => ctx.real_sub_v(&args),
						"*" => ctx.real_mul_v(&args),
						"/" => ctx.real_div(args[0], args[1]),
						// "POWER" => ctx.real_power(args[0], args[1]),
						_ => unreachable!(),
					},
					cmp @ (">" | "<" | ">=" | "<=") if expr_args[0].ty() == Integer => match cmp {
						">" => ctx.int_gt(args[0], args[1]),
						"<" => ctx.int_lt(args[0], args[1]),
						">=" => ctx.int_ge(args[0], args[1]),
						"<=" => ctx.int_le(args[0], args[1]),
						_ => unreachable!(),
					},
					cmp @ (">" | "<" | ">=" | "<=") if expr_args[0].ty() == Integer => match cmp {
						">" => ctx.real_gt(args[0], args[1]),
						"<" => ctx.real_lt(args[0], args[1]),
						">=" => ctx.real_ge(args[0], args[1]),
						"<=" => ctx.real_le(args[0], args[1]),
						_ => unreachable!(),
					},
					"=" => ctx.bool_some(args[0]._eq(args[1])),
					"<>" => ctx.bool_some(args[0]._eq(args[1]).not()),
					"CASE" if args.len() % 2 == 1 => {
						let (chunks, remainder) = args.as_chunks();
						chunks.iter().rfold(remainder[0].clone(), |rem, [cond, body]| {
							ctx.bool_is_true(cond).ite(body, &rem)
						})
					},
					"IS NULL" => {
						ctx.bool_some(ctx.none(&expr_args[0].ty()).unwrap()._eq(args[0]))
					},
					"IS NOT NULL" => {
						ctx.bool_some(ctx.none(&expr_args[0].ty()).unwrap()._eq(args[0]).not())
					},
					op => ctx.app(&format!("f!{}", op), &args, ty, true),
				}
			},
			Expr::HOp(f, args, rel, ty) => h_ops
				.borrow_mut()
				.entry((f.clone(), args.clone(), *rel.clone(), subst.clone()))
				.or_insert_with(|| self.0.var(ty, "h"))
				.clone(),
		}
	}
}

impl<'c> Eval<&Predicate, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Predicate) -> Bool<'c> {
		match source {
			Predicate::Eq(e1, e2) => self.eval(e1)._eq(&self.eval(e2)),
			// Predicate::Eq(e1, e2) => self.eval(e1)._safe_eq(&self.eval(e2)).unwrap_or_else(|_| {
			// 	log::info!("Incorrect comparing {} and {}", e1, e2);
			// 	log::info!("under context {:?}", self.1);
			// 	panic!()
			// }),
			Predicate::Pred(pred, args) => {
				let args = args.iter().map(|arg| self.eval(arg)).collect_vec();
				let args = args.iter().collect_vec();
				self.0.app(pred, &args, &DataType::Boolean, false).as_bool().unwrap()
			},
			Predicate::Bool(expr) => self.0.bool_is_true(&self.eval(expr)),
			Predicate::Like(expr, pat) => {
				self.eval(expr)._eq(&self.0.app(pat, &[], &DataType::String, true))
			},
		}
	}
}
