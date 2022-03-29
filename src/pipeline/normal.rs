use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::{Display, Formatter, Write};
use std::iter::once;
use std::ops::Range;
use std::time::Duration;

use anyhow::bail;
use imbl::{vector, Vector};
use indenter::indented;
use itertools::Itertools;
use num::ToPrimitive;
use z3::ast::{exists_const, Ast, Bool, Dynamic, Int, Real as Re, String as Str};
use z3::{SatResult, Solver};

use super::partial::partition_apps;
use super::shared::z3_const;
use crate::pipeline::partial::{Closure, Summation};
use crate::pipeline::shared::{z3_app, AppHead, DataType, Eval, Schema, Terms, VL};
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

#[derive(Copy, Clone)]
pub struct Env<'e>(pub &'e Vector<DataType>, pub &'e [Schema]);

impl Eval<partial::UExpr, UExpr> for Env<'_> {
	fn eval(self, source: partial::UExpr) -> UExpr {
		source.into_iter().flat_map(|t| self.eval(t)).collect()
	}
}

impl Eval<partial::Term, UExpr> for Env<'_> {
	fn eval(self, mut source: partial::Term) -> UExpr {
		let Env(context, schemas) = self;
		let lvl = context.len();
		if let Some(Summation { scopes, summand }) = source.sums.pop_front() {
			let entries = shared::Expr::vars(lvl, scopes.clone());
			let sum_body: partial::UExpr = (&summand.env.append(entries)).eval(summand.body);
			let context = context + &scopes;
			UExpr::under(scopes, Env(&context, schemas).eval(sum_body * source))
		} else if let Some(app) = source.apps.pop_front() {
			match &app.head {
				AppHead::HOp(op, args, _) if op == "limit" && &args[0] == &0u32.into() => {
					UExpr::zero()
				},
				AppHead::HOp(op, args, rel)
					if op == "limit" && &args[0] == &1u32.into() && self.degen(*rel.clone()) =>
				{
					let shared::Relation(scopes, clos) = *rel.clone();
					let body: partial::UExpr = (&clos.env.append(app.args)).eval(clos.body);
					self.eval(body * source)
				},
				_ => {
					source.stable_apps.push_back(app);
					self.eval(source)
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
		source.into_iter().flat_map(|t| self.eval(t)).collect()
	}
}

impl Eval<partial::STerm, SUExpr> for Env<'_> {
	fn eval(self, mut source: partial::STerm) -> SUExpr {
		let Env(context, schemas) = self;
		let lvl = context.len();
		if let Some(Summation { scopes, summand }) = source.sums.pop_front() {
			let entries = shared::Expr::vars(lvl, scopes.clone());
			let sum_body: partial::SUExpr = (&summand.env.append(entries)).eval(summand.body);
			let context = context + &scopes;
			shared::Terms::under(scopes, Env(&context, schemas).eval(sum_body * source))
		} else if let Some(app) = source.apps.pop_front() {
			match &app.head {
				AppHead::HOp(op, args, _) if op == "limit" && &args[0] == &0u32.into() => {
					SUExpr::zero()
				},
				AppHead::HOp(op, args, rel)
					if op == "limit" && &args[0] == &1u32.into() && self.degen(*rel.clone()) =>
				{
					let shared::Relation(scopes, clos) = *rel.clone();
					let body: partial::SUExpr = (&clos.env.append(app.args)).eval(clos.body);
					self.eval(body * source)
				},
				_ => {
					source.stable_apps.push_back(app);
					self.eval(source)
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

impl Eval<(VL, DataType), Expr> for Env<'_> {
	fn eval(self, source: (VL, DataType)) -> Expr {
		Expr::Var(source.0, source.1)
	}
}

impl Eval<partial::Relation, Relation> for Env<'_> {
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

impl Expr {
	fn deps(&self, vars: Range<usize>) -> Option<HashSet<VL>> {
		match self {
			Expr::Var(v, _) if vars.contains(&v.0) => Some(once(v.clone()).collect()),
			Expr::Var(_, _) => Some(HashSet::new()),
			Expr::Op(_, args, _) => args.iter().map(|expr| expr.deps(vars.clone())).fold_options(
				HashSet::new(),
				|mut s1, s2| {
					s1.extend(s2);
					s1
				},
			),
			Expr::HOp(_, _, _, _) => None,
		}
	}
}

fn var_elim(
	env: StbEnv,
	vars: &[(u32, &Expr)],
	cong: &[(u32, &Expr)],
) -> (Vector<Expr>, Vector<DataType>) {
	log::info!(
		"Eliminating {}, {}",
		vars.iter().map(|(g, e)| format!("[{}, {}]", g, e)).join(", "),
		cong.iter().map(|(g, e)| format!("[{}, {}]", g, e)).join(", ")
	);
	let StbEnv(subst, level, _) = env;
	let groups = vars.iter().chain(cong).map(|&g| g).into_group_map();
	let vars = vars
		.iter()
		.map(|&(g, e)| match e {
			&Expr::Var(v, ref ty) => (g, v, ty.clone()),
			_ => panic!(),
		})
		.collect_vec();

	fn saturate_deps(vars: &HashSet<VL>, mappings: &BTreeMap<VL, HashSet<VL>>) -> HashSet<VL> {
		let saturate = |var, mappings: &BTreeMap<_, _>| {
			mappings
				.get(&var)
				.map_or_else(|| once(var).collect(), |vars| saturate_deps(vars, mappings))
		};
		vars.into_iter().flat_map(|&v| saturate(v, mappings)).collect()
	}

	let bound = subst.len()..subst.len() + vars.len();
	let mut scopes = Vector::new();
	let mut keys: HashSet<_> = vars.iter().map(|&(_, v, _)| v).collect();
	let mut dep_maps = BTreeMap::new();
	let mut var_subst = vars
		.into_iter()
		.map(|(g, var, ty)| {
			let group = groups.get(&g).unwrap();
			keys.remove(&var);
			if let Some((deps, expr)) = group.iter().find_map(|&expr| {
				expr.deps(bound.clone())
					.map(|deps| (deps, expr))
					.filter(|(deps, _)| saturate_deps(deps, &dep_maps).is_subset(&keys))
			}) {
				log::info!("[dep] {} -> {}", var, expr);
				dep_maps.insert(var, deps);
				expr.clone()
			} else {
				keys.insert(var);
				let expr = Expr::Var(VL(level + scopes.len()), ty.clone());
				log::info!("[key] {} -> {}", var, expr);
				scopes.push_back(ty);
				expr
			}
		})
		.collect();

	fn prune(
		v: VL,
		keys: &HashSet<VL>,
		dep_maps: &mut BTreeMap<VL, HashSet<VL>>,
		var_subst: &mut Vector<Expr>,
		env: StbEnv,
	) {
		let StbEnv(subst, level, z3_env) = env;
		if let Some((v, deps)) = dep_maps.remove_entry(&v) {
			deps.into_iter().for_each(|w| prune(w, keys, dep_maps, var_subst, env));
			let i = v.0 - subst.len();
			var_subst[i] =
				StbEnv(&(subst + var_subst), level + keys.len(), z3_env).eval(var_subst[i].clone());
			log::info!("{} ~> {}", v, var_subst[i]);
		};
	}

	while let Some((&v, _)) = dep_maps.first_key_value() {
		prune(v, &keys, &mut dep_maps, &mut var_subst, env);
	}

	(var_subst, scopes)
}

impl<'e, 'c> Eval<Scoped<Inner>, Option<Scoped<Inner>>> for StbEnv<'e, 'c> {
	fn eval(self, Scoped { inner, scopes }: Scoped<Inner>) -> Option<Scoped<Inner>> {
		let StbEnv(subst, level, z3_env) = self;
		let solver = z3_env.0;
		let z3_subst = &z3_env.extend(scopes.clone());
		let z3_env = z3_env.update(z3_subst);
		let constraint = z3_env.eval(&inner);
		let vars = Expr::vars(subst.len(), scopes.clone());
		let exprs = vars
			.iter()
			.chain(inner.preds.iter().flat_map(|pred| match pred {
				Predicate::Eq(e1, e2) => vec![e1, e2],
				_ => vec![],
			}))
			.collect_vec();
		let z3_asts = exprs.iter().map(|&e| z3_env.eval(e)).collect_vec();
		let z3_asts = z3_asts.iter().map(|e| e as &dyn Ast).collect_vec();
		solver.reset();
		solver.assert(&constraint);
		let handle = solver.get_context().handle();
		let checked = crossbeam::atomic::AtomicCell::new(false);
		let (ids, res) = crossbeam::thread::scope(|s| {
			let checked = &checked;
			let p = crossbeam::sync::Parker::new();
			let u = p.unparker().clone();
			s.spawn(move |_| {
				p.park_timeout(Duration::from_secs(2));
				if !checked.load() {
					handle.interrupt();
				}
			});
			let (ids, res) = solver.get_implied_equalities(z3_asts.as_slice());
			checked.store(true);
			u.unpark();
			(ids, res)
		})
		.unwrap();
		solver.reset();
		match res {
			SatResult::Unsat => None,
			SatResult::Unknown => {
				let (ref subst, level) = self.extend(scopes.clone());
				let inner = self.update(subst, level, z3_env).eval(inner);
				Some(Scoped { scopes, inner })
			},
			SatResult::Sat => {
				let groups = ids.into_iter().zip(exprs).collect_vec();
				let (vars, cong) = groups.split_at(scopes.len());
				let (new_subst, new_scopes) = var_elim(self, vars, cong);
				let inner = self
					.update(&(subst + &new_subst), level + new_scopes.len(), z3_env)
					.eval(inner);
				Some(Scoped { inner, scopes: new_scopes })
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
		let preds = self
			.eval(source.preds)
			.into_iter()
			.filter(|p| !matches!(p, Predicate::Eq(e1, e2) if e1 == e2))
			.collect();
		let squash = self.eval(source.squash);
		let not = self.eval(source.not);
		let apps = self.eval(source.apps);
		Inner { preds, squash, not, apps }
	}
}

impl<'e, 'c: 'e> Eval<SInner, SInner> for StbEnv<'e, 'c> {
	fn eval(self, source: SInner) -> SInner {
		let preds = self
			.eval(source.preds)
			.into_iter()
			.filter(|p| !matches!(p, Predicate::Eq(e1, e2) if e1 == e2))
			.collect();
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
		let shared::Relation(scopes, body) = source;
		let z3_subst = &z3_env.extend(scopes.clone());
		let (ref subst, level) = self.extend(scopes.clone());
		shared::Relation(
			scopes,
			Box::new(self.update(subst, level, z3_env.update(z3_subst)).eval(*body)),
		)
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

impl<'e, 'c> Eval<&Scoped<SInner>, Bool<'c>> for Z3Env<'e, 'c> {
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
		AppHead::Var(VL(l)) => format!("r!{}", l),
		AppHead::HOp(op, args, rel) => {
			let len = map.borrow().len();
			let id = *map
				.borrow_mut()
				.entry((op.clone(), args.clone(), *rel.clone(), subst.clone()))
				.or_insert(len);
			format!("rh!{}", id)
		},
	}
}

impl<'e, 'c: 'e> Eval<&Application, Bool<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Application) -> Bool<'c> {
		let args = source.args.iter().map(|v| self.eval(v)).collect_vec();
		z3_app(self.0.get_context(), table_name(&source.head, self) + "p", args, DataType::Boolean)
			.as_bool()
			.unwrap()
	}
}

impl<'e, 'c: 'e> Eval<&Application, Int<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Application) -> Int<'c> {
		let args = source.args.iter().map(|v| self.eval(v)).collect_vec();
		z3_app(self.0.get_context(), table_name(&source.head, self), args, DataType::Integer)
			.as_int()
			.unwrap()
	}
}

impl<'e, 'c: 'e> Eval<&Expr, Dynamic<'c>> for Z3Env<'e, 'c> {
	fn eval(self, source: &Expr) -> Dynamic<'c> {
		use DataType::*;
		let Z3Env(solver, subst, h_ops, _) = self;
		let ctx = solver.get_context();
		let parse = |ctx, input: &str, ty: &DataType| {
			if input.to_lowercase() == "null" {
				return Ok(z3_app(ctx, format!("null-{:?}", ty), vec![], ty.clone()));
			}
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
					op => shared::z3_app(ctx, "f!".to_owned() + &op.to_string(), args, ty.clone()),
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
			Predicate::Bool(expr) => self.eval(expr).as_bool().unwrap(),
			Predicate::Like(expr, pat) => {
				self.eval(expr)._eq(&z3_const(ctx, pat.clone(), DataType::String))
			},
		}
	}
}
