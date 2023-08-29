use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter, Write};
use std::ops::Range;
use std::rc::Rc;

use anyhow::bail;
use imbl::{vector, HashSet, Vector};
use indenter::indented;
use itertools::Itertools;
use num::ToPrimitive;
use z3::ast::{exists_const, Ast, Bool, Dynamic, Int, Real as Re, String as Str};
use z3::{Config, Context, Solver};

use super::shared::{Ctx, Lambda, Sigma, Typed};
use super::stable::{self, stablize};
use super::unify::{Unify, UnifyEnv};
use crate::pipeline::relation::num_op;
use crate::pipeline::shared::{DataType, Eval, Neutral as Neut, Terms, VL};
use crate::pipeline::{partial, shared};

pub type Relation = Lambda<UExpr>;

pub type Expr = shared::Expr<UExpr, Relation, Aggr>;
pub type Neutral = shared::Neutral<Relation, Expr>;
pub type Head = shared::Head<Relation, Expr>;
pub type Logic = shared::Logic<UExpr, Expr>;

pub type Term = Sigma<Inner>;
pub type UExpr = Terms<Term>;

impl UExpr {
	pub fn under(scope: Vector<DataType>, terms: UExpr) -> Self {
		terms.into_iter().map(|term| Sigma(scope.clone() + term.0, term.1)).collect()
	}
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Aggr(pub String, pub Vector<DataType>, pub Box<Inner>, pub Box<Expr>);

impl Display for Aggr {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let Aggr(name, scope, uexpr, expr) = self;
		write!(f, "⨿{} {:?} {{", name, scope)?;
		writeln!(indented(f).with_str("\t"), "{},", uexpr)?;
		writeln!(indented(f).with_str("\t"), "{}", expr)?;
		write!(f, "}}")
	}
}

impl Typed for Aggr {
	fn ty(&self) -> DataType {
		self.3.ty()
	}
}

impl Aggr {
	pub fn under(scope: Vector<DataType>, aggs: Vector<Aggr>) -> Vector<Aggr> {
		aggs.into_iter().map(|Aggr(op, scp, u, e)| Aggr(op, scope.clone() + scp, u, e)).collect()
	}
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Inner {
	pub logic: Logic,
	pub apps: Vector<Neutral>,
}

impl Display for Inner {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "⟦{}⟧ × ({})", self.logic, self.apps.iter().format(" × "))
	}
}

impl Inner {
	pub(crate) fn in_scope(&self, lvl: usize) -> bool {
		self.logic.in_scope(lvl) && self.apps.iter().all(|app| app.in_scope(lvl))
	}
}

impl Aggr {
	pub(crate) fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		let Aggr(_, _, u, e) = self;
		e.deps(vars) + u.logic.deps(vars) + HashSet::unions(u.apps.iter().map(|app| app.deps(vars)))
	}

	pub(crate) fn in_scope(&self, lvl: usize) -> bool {
		let Aggr(_, scope, u, e) = self;
		u.in_scope(lvl + scope.len()) && e.in_scope(lvl + scope.len())
	}
}

impl Expr {
	pub(crate) fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		match self {
			Expr::Var(v, _) if vars.contains(&v.0) => HashSet::unit(*v),
			Expr::Var(_, _) => HashSet::new(),
			Expr::Log(l) => l.deps(vars),
			Expr::Agg(agg) => agg.deps(vars),
			Expr::Op(_, args, _) => HashSet::unions(args.iter().map(|arg| arg.deps(vars))),
			Expr::HOp(_, args, rel, _) => {
				HashSet::unions(args.iter().map(|arg| arg.deps(vars))) + rel.deps(vars)
			},
		}
	}

	pub(crate) fn in_scope(&self, lvl: usize) -> bool {
		match self {
			Expr::Var(VL(l), _) => *l < lvl,
			Expr::Log(l) => l.in_scope(lvl),
			Expr::Agg(agg) => agg.in_scope(lvl),
			Expr::Op(_, args, _) => args.iter().all(|arg| arg.in_scope(lvl)),
			Expr::HOp(_, args, rel, _) => {
				args.iter().all(|arg| arg.in_scope(lvl)) && rel.in_scope(lvl)
			},
		}
	}

	fn exprs(&self) -> Vector<&Expr> {
		match self {
			Expr::Log(l) => l.exprs(),
			Expr::Op(op, es, ty)
				if matches!(
					op.as_str(),
					"=" | "EQ" | "<=" | "LE" | "<" | "LT" | ">=" | "GE" | ">" | "GT"
				) && es.len() == 2 && ty == &DataType::Boolean =>
			{
				es.iter().collect()
			},
			Expr::Op(_, es, _) | Expr::HOp(_, es, _, _) => {
				es.iter().flat_map(Expr::exprs).collect()
			},
			_ => vector![],
		}
	}
}

impl UExpr {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		HashSet::unions(self.iter().map(|t| t.deps(vars)))
	}

	fn in_scope(&self, lvl: usize) -> bool {
		self.iter().all(|t| t.in_scope(lvl))
	}

	fn exprs(&self) -> Vector<&Expr> {
		self.iter().flat_map(Term::exprs).collect()
	}
}

impl Relation {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		self.1.deps(vars)
	}

	fn in_scope(&self, lvl: usize) -> bool {
		let Lambda(scope, body) = self;
		body.in_scope(lvl + scope.len())
	}

	fn exprs(&self) -> Vector<&Expr> {
		self.1.exprs()
	}
}

impl Term {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		let Sigma(_, Inner { logic, apps }) = self;
		logic.deps(vars) + HashSet::unions(apps.iter().map(|app| app.deps(vars)))
	}

	fn in_scope(&self, lvl: usize) -> bool {
		let Sigma(scope, Inner { logic, apps }) = self;
		let lvl = lvl + scope.len();
		logic.in_scope(lvl) && apps.iter().all(|app| app.in_scope(lvl))
	}

	fn exprs(&self) -> Vector<&Expr> {
		let Sigma(scope, Inner { logic, apps }) = self;
		logic.exprs() + apps.iter().flat_map(Neutral::exprs).collect()
	}
}

impl Neutral {
	fn deps(&self, vars: &Range<usize>) -> HashSet<VL> {
		let Neut(head, args) = self;
		(match &head {
			Head::Var(_) => HashSet::new(),
			Head::HOp(_, args, rel) => {
				rel.deps(vars) + HashSet::unions(args.iter().map(|arg| arg.deps(vars)))
			},
		}) + HashSet::unions(args.iter().map(|arg| arg.deps(vars)))
	}

	fn in_scope(&self, lvl: usize) -> bool {
		let Neut(head, args) = self;
		(match &head {
			Head::Var(_) => true,
			Head::HOp(_, args, rel) => {
				args.iter().all(|arg| arg.in_scope(lvl)) && rel.in_scope(lvl)
			},
		}) && args.iter().all(|arg| arg.in_scope(lvl))
	}

	fn exprs(&self) -> Vector<&Expr> {
		let Neut(head, args) = self;
		(match &head {
			Head::Var(_) => vector![],
			Head::HOp(_, args, rel) => {
				args.iter().flat_map(Expr::exprs).chain(rel.exprs()).collect()
			},
		}) + args.iter().flat_map(Expr::exprs).collect()
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
			Squash(u) => u.deps(vars),
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
			Squash(u) => u.in_scope(lvl),
		}
	}

	fn simpl(self) -> Self {
		use shared::Logic::*;
		match self {
			Eq(e1, e2) if e1 == e2 => Logic::tt(),
			Bool(Expr::Op(p, es, _)) if p == "=" && es.len() == 2 && es[0] == es[1] => {
				!es[0].clone().is_null()
			},
			And(ls) => And(ls
				.into_iter()
				.flat_map(|l| match l.simpl() {
					And(ls) => ls,
					l => vector![l],
				})
				.collect()),
			Or(ls) => Or(ls
				.into_iter()
				.flat_map(|l| match l.simpl() {
					Or(ls) => ls,
					l => vector![l],
				})
				.collect()),
			Neg(l) => Neg(l.simpl().into()),
			l => l,
		}
	}

	pub(crate) fn exprs(&self) -> Vector<&Expr> {
		use shared::Logic::*;
		match self {
			Bool(e) => e.exprs(),
			Pred(_, es) => es.iter().flat_map(Expr::exprs).collect(),
			Eq(e1, e2) => vector![e1, e2] + e1.exprs() + e2.exprs(),
			Neg(l) => l.exprs(),
			And(ls) => ls.iter().flat_map(Logic::exprs).collect(),
			Or(ls) => ls.iter().flat_map(Logic::exprs).collect(),
			Squash(u) => u.exprs(),
		}
	}
}

pub type Env = Vector<DataType>;

impl Eval<partial::Aggr, Expr> for &Env {
	fn eval(self, agg: partial::Aggr) -> Expr {
		use shared::Expr::*;
		let op = agg.0.clone();
		let ty = agg.ty();
		let es = Agg(agg).split(&op, self).into_iter().map(|(scp, l, apps, e)| {
			let env = &(self + &scp);
			let inner = Inner { logic: env.eval(l), apps: env.eval(apps) };
			Agg(Aggr(op.clone(), scp, Box::new(inner), Box::new(env.eval(e))))
		});
		Op(op.clone(), es.collect(), ty)
	}
}

impl Eval<partial::UExpr, UExpr> for &Env {
	fn eval(self, source: partial::UExpr) -> UExpr {
		source
			.into_iter()
			.flat_map(|t| t.split(self))
			.map(|(scp, l, apps)| {
				let env = &(self + &scp);
				Sigma(scp, Inner { logic: env.eval(l), apps: env.eval(apps) })
			})
			.collect()
	}
}

impl Eval<(VL, DataType), Expr> for &Env {
	fn eval(self, source: (VL, DataType)) -> Expr {
		Expr::Var(source.0, source.1)
	}
}

impl Eval<partial::Relation, Relation> for &Env {
	fn eval(self, source: partial::Relation) -> Relation {
		let partial::Relation(scope, clos_env, body) = source;
		let env = &(self + &scope);
		let vars = shared::Expr::vars(self.len(), scope.clone());
		let body: partial::UExpr = (&clos_env.append(vars)).eval(body);
		Lambda(scope, env.eval(body))
	}
}

impl<'c> Eval<stable::Relation<'c>, Relation> for &Env {
	fn eval(self, stable::Relation(scope, env, body): stable::Relation<'c>) -> Relation {
		let body = (&env.extend(self.len(), scope.clone())).eval(body);
		Lambda(scope.clone(), (&(self + &scope)).eval(body))
	}
}

impl<'c> Eval<stable::UExpr<'c>, UExpr> for &Env {
	fn eval(self, source: stable::UExpr<'c>) -> UExpr {
		source.into_iter().filter_map(|t| self.eval(t)).collect()
	}
}

impl<'c> Eval<stable::Term<'c>, Option<Term>> for &Env {
	fn eval(self, stable::Term(scope, clos_env, inner): stable::Term<'c>) -> Option<Term> {
		let (new_scope, new_subst) = stablize(&clos_env, scope.clone(), self, inner.logic.clone())?;
		let stable::Env(subst, z3_env) = clos_env;
		let clos_env = &stable::Env(subst + new_subst, z3_env.extend(&scope));
		let env = &(self + &new_scope);
		let logic = env.eval(clos_env.eval(inner.logic)).simpl();
		let apps = env.eval(clos_env.eval(inner.apps));
		Some(Sigma(new_scope, Inner { logic, apps }))
	}
}

impl<'c> Eval<stable::Aggr<'c>, Expr> for &Env {
	fn eval(self, agg: stable::Aggr<'c>) -> Expr {
		use shared::Expr::*;
		let op = agg.0.clone();
		let ty = agg.ty();
		let es = Agg(agg).split(&op, self).into_iter().map(|(scp, l, apps, e)| {
			let env = &(self + &scp);
			let inner = Inner { logic: env.eval(l), apps: env.eval(apps) };
			Agg(Aggr(op.clone(), scp, Box::new(inner), Box::new(env.eval(e))))
		});
		Op(op.clone(), es.collect(), ty)
	}
}

impl Unify<partial::UExpr> for Env {
	fn unify(&self, t1: &partial::UExpr, t2: &partial::UExpr) -> bool {
		let t1: UExpr = self.eval(t1.clone());
		let t2: UExpr = self.eval(t2.clone());
		let config = Config::new();
		let z3_ctx = Context::new(&config);
		let ctx = Rc::new(Ctx::new(Solver::new(&z3_ctx)));
		let h_ops = Rc::new(RefCell::new(HashMap::new()));
		let agg_ops = Rc::new(RefCell::new(HashMap::new()));
		let rel_h_ops = Rc::new(RefCell::new(HashMap::new()));
		let subst = shared::Expr::vars(0, self.clone()).into_iter().map(Some).collect();
		let z3_subst: Vector<_> = self.iter().map(|ty| ctx.var(ty, "v")).collect();
		let env =
			&stable::Env(subst, Z3Env(ctx.clone(), z3_subst.clone(), h_ops, agg_ops, rel_h_ops));
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

pub type AggMap<'c> =
	HashMap<(String, Lambda<(Inner, Vec<Expr>)>, Vector<Dynamic<'c>>), Dynamic<'c>>;

#[derive(Clone)]
pub struct Z3Env<'c>(
	pub Rc<Ctx<'c>>,
	pub Vector<Dynamic<'c>>,
	pub Rc<RefCell<HOpMap<'c>>>,
	pub Rc<RefCell<AggMap<'c>>>,
	pub Rc<RefCell<RelHOpMap<'c>>>,
);

impl<'c> Z3Env<'c> {
	pub fn extend(&self, scope: &Vector<DataType>) -> Self {
		let vars = scope.into_iter().map(|ty| self.0.var(ty, "v")).collect();
		Z3Env(self.0.clone(), self.1.clone() + vars, self.2.clone(), self.3.clone(), self.4.clone())
	}

	pub fn extend_vals(&self, vals: &Vector<Dynamic<'c>>) -> Self {
		Z3Env(self.0.clone(), &self.1 + vals, self.2.clone(), self.3.clone(), self.4.clone())
	}

	pub fn extend_vars(&self, scope: &Vector<DataType>) -> (Z3Env<'c>, Vector<Dynamic<'c>>) {
		let vars = scope.into_iter().map(|ty| self.0.var(ty, "v")).collect();
		(
			Z3Env(self.0.clone(), &self.1 + &vars, self.2.clone(), self.3.clone(), self.4.clone()),
			vars,
		)
	}
}

impl<'c> Eval<&Logic, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Logic) -> Bool<'c> {
		use shared::Logic::*;
		let Z3Env(ctx, _, _, _, _) = self;
		let z3_ctx = ctx.z3_ctx();
		match source {
			Bool(e) => ctx.bool_is_true(&self.eval(e)),
			Eq(e1, e2) => {
				assert_eq!(e1.ty(), e2.ty(), "{} and {} have different types", e1, e2);
				self.eval(e1)._eq(&self.eval(e2))
			},
			Pred(p, args) => {
				let args = args.iter().map(|arg| self.eval(arg)).collect_vec();
				let args = args.iter().collect_vec();
				ctx.app(p, &args, &DataType::Boolean, false).as_bool().unwrap()
			},
			Neg(l) => self.eval(l.as_ref()).not(),
			And(ls) => z3::ast::Bool::and(z3_ctx, &self.eval(ls).iter().collect_vec()),
			Or(ls) => z3::ast::Bool::or(z3_ctx, &self.eval(ls).iter().collect_vec()),
			Squash(u) => self.eval(u.as_ref()),
		}
	}
}

impl<'c> Eval<&UExpr, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &UExpr) -> Bool<'c> {
		let terms = source.iter().map(|t| self.eval(t)).collect_vec();
		Bool::or(self.0.z3_ctx(), &terms.iter().collect_vec())
	}
}

impl<'c> Eval<&Term, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Term) -> Bool<'c> {
		let z3_ctx = self.0.z3_ctx();
		let Sigma(scope, body) = source;
		let (ref env, vars) = self.extend_vars(scope);
		let bounds = vars.iter().map(|v| v as &dyn Ast).collect_vec();
		exists_const(z3_ctx, &bounds, &[], &env.eval(body))
	}
}

impl<'c> Eval<&Inner, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Inner) -> Bool<'c> {
		Bool::and(self.0.z3_ctx(), &[&self.eval(&source.logic), &self.eval(&source.apps)])
	}
}

impl<'c> Eval<&Vector<Neutral>, Bool<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Vector<Neutral>) -> Bool<'c> {
		let apps: Vector<_> = self.eval(source);
		let z3_ctx = self.0.z3_ctx();
		if apps.is_empty() {
			Bool::from_bool(z3_ctx, true)
		} else {
			Bool::and(z3_ctx, &apps.iter().collect_vec())
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

fn table_name(head: &Head, env: &Z3Env, squashed: bool, domain: Vec<DataType>) -> String {
	let Z3Env(_, subst, _, _, map) = env;
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
	fn eval(self, shared::Neutral(head, args): &Neutral) -> Bool<'c> {
		let domain = args.iter().map(|a| a.ty()).collect();
		let args = args.iter().map(|v| self.eval(v)).collect_vec();
		let args = args.iter().collect_vec();
		self.0
			.app(&(table_name(&head, self, true, domain) + "p"), &args, &DataType::Boolean, false)
			.as_bool()
			.unwrap()
	}
}

impl<'c> Eval<&Neutral, Int<'c>> for &Z3Env<'c> {
	fn eval(self, shared::Neutral(head, args): &Neutral) -> Int<'c> {
		let domain = args.iter().map(|a| a.ty()).collect();
		let args = args.iter().map(|v| self.eval(v)).collect_vec();
		let args = args.iter().collect_vec();
		self.0
			.app(&table_name(&head, self, false, domain), &args, &DataType::Integer, false)
			.as_int()
			.unwrap()
	}
}

impl<'c> Eval<&Expr, Dynamic<'c>> for &Z3Env<'c> {
	fn eval(self, source: &Expr) -> Dynamic<'c> {
		use DataType::*;
		let Z3Env(ctx, subst, h_ops, agg_ops, _) = self;
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
			Expr::Var(VL(l), _) => subst[*l].clone(),
			Expr::Log(l) => ctx.bool_some(self.eval(l.as_ref())),
			Expr::Op(op, args, ty) if args.is_empty() && let Ok(exp) = parse(ctx.as_ref(), op, ty) => exp,
			Expr::Op(op, expr_args, ty) => {
				let args = expr_args.iter().map(|a| self.eval(a)).collect_vec();
				let args = args.iter().collect_vec();
				match op.as_str() {
					op if num_op(op) && ty == &Integer => match op {
						"+" | "PLUS" | "UNARY PLUS" => ctx.int_add_v(&args),
						"-" | "MINUS" | "UNARY MINUS" => ctx.int_sub_v(&args),
						"*" | "MULT" => ctx.int_mul_v(&args),
						"/" | "DIV" => ctx.int_div(args[0], args[1]),
						"%" => ctx.int_modulo(args[0], args[1]),
						// "POWER" => ctx.int_power(args[0], args[1]),
						_ => unreachable!(),
					},
					op if num_op(op) && ty == &Real => match op {
						"+" | "PLUS" | "UNARY PLUS" => ctx.real_add_v(&args),
						"-" | "MINUS" | "UNARY MINUS" => ctx.real_sub_v(&args),
						"*" | "MULT" => ctx.real_mul_v(&args),
						"/" | "DIV" => ctx.real_div(args[0], args[1]),
						// "POWER" => ctx.real_power(args[0], args[1]),
						_ => unreachable!(),
					},
					cmp @ (">" | "GT" | "<" | "LT" | ">=" | "GE" | "<=" | "LE")
						if expr_args[0].ty() == Integer =>
					{
						match cmp {
							">" | "GT" => ctx.int_gt(args[0], args[1]),
							"<" | "LT" => ctx.int_lt(args[0], args[1]),
							">=" | "GE" => ctx.int_ge(args[0], args[1]),
							"<=" | "LE" => ctx.int_le(args[0], args[1]),
							_ => unreachable!(),
						}
					},
					cmp @ (">" | "GT" | "<" | "LT" | ">=" | "GE" | "<=" | "LE")
						if expr_args[0].ty() == Real =>
					{
						match cmp {
							">" | "GT" => ctx.real_gt(args[0], args[1]),
							"<" | "LT" => ctx.real_lt(args[0], args[1]),
							">=" | "GE" => ctx.real_ge(args[0], args[1]),
							"<=" | "LE" => ctx.real_le(args[0], args[1]),
							_ => unreachable!(),
						}
					},
					cmp @ (">" | "GT" | "<" | "LT" | ">=" | "GE" | "<=" | "LE")
						if expr_args[0].ty() == String =>
					{
						match cmp {
							">" | "GT" => ctx.string_gt(args[0], args[1]),
							"<" | "LT" => ctx.string_lt(args[0], args[1]),
							">=" | "GE" => ctx.string_ge(args[0], args[1]),
							"<=" | "LE" => ctx.string_le(args[0], args[1]),
							_ => unreachable!(),
						}
					},
					cmp @ ("=" | "EQ" | "<>" | "!=" | "NE") => {
						let (a1, a2) = (args[0], args[1]);
						assert_eq!(
							a1.get_sort(),
							a2.get_sort(),
							"{} and {} have different types.",
							expr_args[0],
							expr_args[1]
						);
						let eq = match expr_args[0].ty() {
							Integer => ctx.int__eq(a1, a2),
							Real => ctx.real__eq(a1, a2),
							Boolean => ctx.bool__eq(a1, a2),
							String => ctx.string__eq(a1, a2),
							Custom(ty) => ctx.generic_eq(ty, a1, a2),
						};
						if cmp == "=" || cmp == "EQ" {
							eq
						} else {
							ctx.bool_not(&eq)
						}
					},
					"NOT" if args.len() == 1 => ctx.bool_not(args[0]),
					"AND" => ctx.bool_and_v(&args),
					"OR" => ctx.bool_or_v(&args),
					"CASE" if args.len() % 2 == 1 => {
						let (chunks, remainder) = args.as_chunks();
						chunks.iter().rfold(remainder[0].clone(), |rem, [cond, body]| {
							ctx.bool_is_true(cond).ite(body, &rem)
						})
					},
					"CAST" if ty == &expr_args[0].ty() => args[0].clone(),
					"CAST" if ty == &Real && expr_args[0].ty() == Integer => {
						ctx.int_to_real(args[0])
					},
					"CAST" if let Expr::Op(op, args, _) = &expr_args[0] && args.is_empty()
						&& let Ok(exp) = parse(ctx.as_ref(), op, ty) => exp,
					"COUNT" | "SUM" | "MIN" | "MAX" => {
						if args.len() == 1 {
							args[0].clone()
						} else {
							ctx.app(&format!("f{}!{}", args.len(), op), &args, ty, true)
						}
					},
					op => ctx.app(&format!("f!{}", op), &args, ty, true),
				}
			},
			Expr::HOp(f, args, rel, DataType::Boolean) if f == "IN" => {
				let z3_ctx = ctx.z3_ctx();
				let (is_nulls, args, nulls): (Vec<_>, _, _) = args
					.iter()
					.map(|a| {
						let null = ctx.none(&a.ty()).unwrap();
						let a = self.eval(a);
						(null._eq(&a), a, null)
					})
					.multiunzip();
				let Lambda(_, uexpr) = *rel.clone();
				let any_null = Bool::or(z3_ctx, &is_nulls.iter().collect_vec());
				any_null.ite(
					&ctx.bool_none(),
					&(&self.extend_vals(&args)).eval(&uexpr).ite(
						&ctx.bool_some(Bool::from_bool(z3_ctx, true)),
						&(&self.extend_vals(&nulls))
							.eval(&uexpr)
							.ite(&ctx.bool_none(), &ctx.bool_some(Bool::from_bool(z3_ctx, false))),
					),
				)
			},
			Expr::HOp(f, args, rel, ty) => h_ops
				.borrow_mut()
				.entry((f.clone(), args.clone(), *rel.clone(), subst.clone()))
				.or_insert_with(|| self.0.var(ty, "h"))
				.clone(),
			Expr::Agg(agg) => {
				let Aggr(f, scope, inner, expr) = agg;
				agg_ops
					.borrow_mut()
					.entry((
						f.clone(),
						Lambda(scope.clone(), (*inner.clone(), vec![*expr.clone()])),
						subst.clone(),
					))
					.or_insert_with(|| self.0.var(&expr.ty(), "h"))
					.clone()
			},
		}
	}
}
