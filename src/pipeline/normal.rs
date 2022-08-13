use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter, Write};
use std::ops::Range;
use std::rc::Rc;

use anyhow::bail;
use imbl::{vector, HashSet, Vector};
use indenter::indented;
use itertools::{Either, Itertools};
use num::ToPrimitive;
use z3::ast::{exists_const, Ast, Bool, Dynamic, Int, Real as Re, String as Str};
use z3::{Config, Context, Solver};

use super::shared::{Ctx, Lambda};
use super::stable;
use super::unify::{Unify, UnifyEnv};
use crate::pipeline::shared::{DataType, Eval, Head, Schema, Terms, VL};
use crate::pipeline::{partial, shared};

pub type Relation = Lambda<UExpr>;

pub type Expr = shared::Expr<Relation>;
pub type Neutral = shared::Neutral<Relation>;
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct LogicRel(pub Vector<DataType>, pub Box<Logic>);
pub type Logic = shared::Logic<Relation, LogicRel, Neutral>;

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
	pub apps: Vector<Neutral>,
}

impl Term {
	pub fn app(app: Neutral) -> Self {
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
	pub(crate) fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		match self {
			Expr::Var(v, _) if vars.contains(&v.0) => HashSet::unit(*v),
			Expr::Var(_, _) => HashSet::new(),
			Expr::Op(_, args, _) => HashSet::unions(args.iter().map(|arg| arg.deps(vars))),
			Expr::HOp(_, args, rel, _) => {
				HashSet::unions(args.iter().map(|arg| arg.deps(vars))) + rel.deps(vars)
			},
		}
	}

	pub(crate) fn in_scope(&self, lvl: usize) -> bool {
		match self {
			Expr::Var(VL(l), _) => *l < lvl,
			Expr::Op(_, args, _) => args.iter().all(|arg| arg.in_scope(lvl)),
			Expr::HOp(_, args, rel, _) => {
				args.iter().all(|arg| arg.in_scope(lvl)) && rel.in_scope(lvl)
			},
		}
	}
}

impl Relation {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		HashSet::unions(self.1.iter().map(|t| t.deps(vars)))
	}

	fn in_scope(&self, lvl: usize) -> bool {
		let Lambda(scope, body) = self;
		body.iter().all(|t| t.in_scope(lvl + scope.len()))
	}
}

impl Term {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		self.logic.deps(vars) + HashSet::unions(self.apps.iter().map(|app| app.deps(vars)))
	}

	fn in_scope(&self, lvl: usize) -> bool {
		let lvl = lvl + self.scope.len();
		self.logic.in_scope(lvl) && self.apps.iter().all(|app| app.in_scope(lvl))
	}
}

impl Neutral {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		(match &self.head {
			Head::Var(_) => HashSet::new(),
			Head::HOp(_, args, rel) => {
				rel.deps(vars) + HashSet::unions(args.iter().map(|arg| arg.deps(vars)))
			},
		}) + HashSet::unions(self.args.iter().map(|arg| arg.deps(vars)))
	}

	fn in_scope(&self, lvl: usize) -> bool {
		(match &self.head {
			Head::Var(_) => true,
			Head::HOp(_, args, rel) => {
				args.iter().all(|arg| arg.in_scope(lvl)) && rel.in_scope(lvl)
			},
		}) && self.args.iter().all(|arg| arg.in_scope(lvl))
	}
}

impl Logic {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		use shared::Logic::*;
		match self {
			Bool(e) => e.deps(vars),
			Eq(e1, e2) => e1.deps(vars) + e2.deps(vars),
			Pred(_, args) => HashSet::unions(args.iter().map(|arg| arg.deps(vars))),
			Neg(l) => l.deps(vars),
			And(ls) | Or(ls) => HashSet::unions(ls.iter().map(|l| l.deps(vars))),
			App(app) => app.deps(vars),
			Exists(LogicRel(_, l)) => l.deps(vars),
		}
	}

	fn in_scope(&self, lvl: usize) -> bool {
		use shared::Logic::*;
		match self {
			Bool(e) => e.in_scope(lvl),
			Eq(e1, e2) => e1.in_scope(lvl) && e2.in_scope(lvl),
			Pred(_, args) => args.iter().all(|arg| arg.in_scope(lvl)),
			Neg(l) => l.in_scope(lvl),
			And(ls) | Or(ls) => ls.iter().all(|l| l.in_scope(lvl)),
			App(app) => app.in_scope(lvl),
			Exists(LogicRel(scope, l)) => l.in_scope(lvl + scope.len()),
		}
	}

	fn is_tt(&self) -> bool {
		use shared::Logic::*;
		match self {
			Eq(e1, e2) if e1 == e2 => true,
			And(ls) if ls.is_empty() => true,
			Neg(l) if l.is_ff() => true,
			_ => false,
		}
	}

	fn is_ff(&self) -> bool {
		use shared::Logic::*;
		match self {
			Or(ls) if ls.is_empty() => true,
			Neg(l) if l.is_tt() => true,
			_ => false,
		}
	}

	fn norm(self) -> Logic {
		use shared::Logic::*;
		match self {
			l if l.is_tt() => Logic::tt(),
			l if l.is_ff() => Logic::ff(),
			And(ls) => {
				let ls = ls.into_iter().flat_map(|l| match l {
					And(ls) => ls,
					l => vector![l],
				});
				And(ls.collect())
			},
			Or(ls) => {
				let ls = ls.into_iter().flat_map(|l| match l {
					Or(ls) => ls,
					l => vector![l],
				});
				Or(ls.collect())
			},
			l => l,
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

fn helper(env: &Env, mut term: partial::Term, apps: Vector<partial::Neutral>) -> UExpr {
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
		match app.head.app(app.args, env) {
			Either::Left(app) => helper(env, term, apps + vector![app]),
			Either::Right(uexpr) => {
				(uexpr * term).into_iter().flat_map(|t| helper(env, t, apps.clone())).collect()
			},
		}
	} else {
		UExpr::term(Term { scope: vector![], logic: env.eval(term.logic), apps: env.eval(apps) })
	}
}

impl Eval<partial::Neutral, Logic> for &Env {
	fn eval(self, app: partial::Neutral) -> Logic {
		match app.head.app_logic(app.args, self) {
			Either::Left(app) => Logic::App(self.eval(app)),
			Either::Right(logic) => self.eval(logic),
		}
	}
}

impl Eval<partial::LogicRel, LogicRel> for &Env {
	fn eval(self, source: partial::LogicRel) -> LogicRel {
		use partial::LogicRel::*;
		let Env(context, schemas) = self;
		let scope = source.scope(schemas);
		let env = &self.extend(scope.clone());
		let vars = shared::Expr::vars(context.len(), scope.clone());
		LogicRel(
			scope,
			Box::new(match source {
				Rigid(head) => match head.app_logic(vars, env) {
					Either::Left(app) => env.eval(app),
					Either::Right(logic) => env.eval(logic),
				},
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
		let vars = shared::Expr::vars(context.len(), scope.clone());
		Lambda(scope, match source {
			Rigid(head) => match head.app(vars, env) {
				Either::Left(app) => UExpr::term(Term::app(env.eval(app))),
				Either::Right(uexpr) => env.eval(uexpr),
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

impl<'c> Eval<stable::Logic<'c>, Logic> for &Env {
	fn eval(self, source: stable::Logic<'c>) -> Logic {
		use shared::Logic::*;
		match source {
			Bool(e) => Bool(self.eval(e)),
			Eq(e1, e2) => Eq(self.eval(e1), self.eval(e2)),
			Pred(p, args) => Pred(p, self.eval(args)),
			Neg(l) => Neg(self.eval(l)),
			And(ls) => And(self.eval(ls)),
			Or(ls) => Or(self.eval(ls)),
			App(app) => self.eval(app),
			Exists(stable::LogicRel(scope, env, body)) => {
				let body = (&env.extend(self.0.len(), scope.clone())).eval(body);
				Exists(LogicRel(scope.clone(), Box::new((&self.extend(scope)).eval(body))))
			},
		}
		.norm()
	}
}

impl<'c> Eval<stable::Neutral<'c>, Logic> for &Env {
	fn eval(self, source: stable::Neutral<'c>) -> Logic {
		Logic::App(self.eval(source))
	}
}

impl Unify<partial::UExpr> for &Env {
	fn unify(self, t1: partial::UExpr, t2: partial::UExpr) -> bool {
		let Env(context, _) = self;
		let t1: UExpr = self.eval(t1);
		let t2: UExpr = self.eval(t2);
		let mut config = Config::new();
		config.set_timeout_msec(2000);
		let z3_ctx = Context::new(&config);
		let ctx = Rc::new(Ctx::new(Solver::new(&z3_ctx)));
		let h_ops = Rc::new(RefCell::new(HashMap::new()));
		let rel_h_ops = Rc::new(RefCell::new(HashMap::new()));
		let uexpr_subst = shared::Expr::vars(0, context.clone()).into_iter().map(Some).collect();
		let z3_subst: Vector<_> = context.iter().map(|ty| ctx.var(ty, "v")).collect();
		let env =
			&stable::Env(uexpr_subst, 0, Z3Env(ctx.clone(), z3_subst.clone(), h_ops, rel_h_ops));
		let t1 = env.eval(t1);
		let t2 = env.eval(t2);
		let t1: UExpr = self.eval(t1);
		let t2: UExpr = self.eval(t2);
		let uni_env = UnifyEnv(ctx, z3_subst.clone(), z3_subst);
		(&uni_env).unify(&t1, &t2)
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
		let vars = scope.into_iter().map(|ty| self.0.var(ty, "v")).collect();
		Z3Env(self.0.clone(), self.1.clone() + vars, self.2.clone(), self.3.clone())
	}

	pub fn extend_vars(&self, scope: &Vector<DataType>) -> (Z3Env<'c>, Vector<Dynamic<'c>>) {
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
			Bool(e) => self.0.bool_is_true(&self.eval(e)),
			Eq(e1, e2) => self.eval(e1)._eq(&self.eval(e2)),
			Pred(p, args) => {
				let args = args.iter().map(|arg| self.eval(arg)).collect_vec();
				let args = args.iter().collect_vec();
				self.0.app(p, &args, &DataType::Boolean, false).as_bool().unwrap()
			},
			Neg(l) => self.eval(l.as_ref()).not(),
			And(ls) => z3::ast::Bool::and(z3_ctx, &self.eval(ls).iter().collect_vec()),
			Or(ls) => z3::ast::Bool::or(z3_ctx, &self.eval(ls).iter().collect_vec()),
			App(app) => self.eval(app),
			Exists(LogicRel(scope, l)) => {
				let (ref env, vars) = self.clone().extend_vars(&scope);
				let bounds = vars.iter().map(|v| v as &dyn Ast).collect_vec();
				let body = env.eval(l.as_ref());
				exists_const(z3_ctx, &bounds, &[], &body)
			},
		}
	}
}

impl<'c> Eval<&Vector<Neutral>, Int<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Vector<Neutral>) -> Int<'c> {
		let apps: Vector<_> = self.eval(source);
		let z3_ctx = self.0.z3_ctx();
		if apps.is_empty() {
			Int::from_i64(z3_ctx, 1)
		} else {
			Int::mul(z3_ctx, &apps.iter().collect_vec())
		}
	}
}

fn table_name(head: &Head<Relation>, env: &Z3Env, squashed: bool, domain: Vec<DataType>) -> String {
	let Z3Env(_, subst, _, map) = env;
	match head {
		Head::Var(VL(l)) => format!("r{}!{}", if squashed { "p" } else { "" }, l),
		Head::HOp(op, args, rel) => {
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

impl<'c> Eval<&Neutral, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Neutral) -> Bool<'c> {
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

impl<'c> Eval<&Neutral, Int<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Neutral) -> Int<'c> {
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
				let cast = matches!(op.as_str(), "+" | "-" | "*" | "/" if ty == &Real)
					|| matches!(op.as_str(), ">" | "<" | ">=" | "<=" | "=" if expr_args.iter().any(|e| e.ty() == Real));
				let args = expr_args
					.iter()
					.map(|arg| {
						if cast && arg.ty() != Real {
							ctx.int_to_real(&self.eval(arg))
						} else {
							self.eval(arg)
						}
					})
					.collect_vec();
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
					cmp @ (">" | "<" | ">=" | "<=") if expr_args[0].ty() == Real => match cmp {
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
					"CAST" if ty == &Real && expr_args[0].ty() == Integer => {
						ctx.int_to_real(args[0])
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
