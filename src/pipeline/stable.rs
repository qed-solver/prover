use std::collections::BTreeMap;
use std::time::Duration;

use imbl::{HashSet, Vector};
use itertools::Itertools;
use z3::ast::Ast;
use z3::SatResult;

use super::normal::Z3Env;
use super::shared::{DataType, Eval, Lambda, Terms};
use crate::pipeline::normal;
use crate::pipeline::shared::{self, VL};

pub type Expr<'c> = shared::Expr<Relation<'c>>;
#[derive(Clone)]
pub struct LogicRel<'c>(pub Vector<DataType>, pub Env<'c>, pub normal::Logic);
pub type Neutral<'c> = shared::Neutral<Relation<'c>>;
pub type Logic<'c> = shared::Logic<Relation<'c>, LogicRel<'c>, Neutral<'c>>;

#[derive(Clone)]
pub struct Relation<'c>(pub Vector<DataType>, pub Env<'c>, pub normal::UExpr);
pub type UExpr<'c> = Terms<Term<'c>>;

#[derive(Clone)]
pub struct Env<'c>(pub Vector<Option<Expr<'c>>>, pub usize, pub Z3Env<'c>);

impl<'c> Env<'c> {
	pub fn append(&self, subst: Vector<Option<Expr<'c>>>) -> Self {
		Env(self.0.clone() + subst, self.1, self.2.clone())
	}

	pub fn extend(&self, base: usize, scope: Vector<DataType>) -> Self {
		let vars = shared::Expr::vars(base, scope.clone()).into_iter().map(Some).collect();
		Env(self.0.clone() + vars, base + scope.len(), self.2.extend(&scope))
	}
}

#[derive(Clone)]
pub struct Term<'c> {
	pub scope: Vector<DataType>,
	pub logic: Logic<'c>,
	pub apps: Vector<Neutral<'c>>,
}

impl<'c> Eval<(VL, DataType), Expr<'c>> for &Env<'c> {
	fn eval(self, (VL(l), _): (VL, DataType)) -> Expr<'c> {
		self.0[l].clone().unwrap()
	}
}

impl<'c> Eval<normal::Relation, Relation<'c>> for &Env<'c> {
	fn eval(self, Lambda(scope, body): normal::Relation) -> Relation<'c> {
		Relation(scope, self.clone(), body)
	}
}

impl<'c> Eval<normal::LogicRel, LogicRel<'c>> for &Env<'c> {
	fn eval(self, normal::LogicRel(scope, body): normal::LogicRel) -> LogicRel<'c> {
		LogicRel(scope, self.clone(), *body)
	}
}

impl<'c> Eval<normal::Neutral, Logic<'c>> for &Env<'c> {
	fn eval(self, source: normal::Neutral) -> Logic<'c> {
		Logic::App(self.eval(source))
	}
}

impl<'c> Eval<normal::UExpr, UExpr<'c>> for &Env<'c> {
	fn eval(self, source: normal::UExpr) -> UExpr<'c> {
		source.into_iter().filter_map(|term| self.eval(term)).collect()
	}
}

fn exprs(logic: &normal::Logic) -> Vec<&normal::Expr> {
	use shared::Logic::*;
	match logic {
		Bool(_) | Pred(_, _) => vec![],
		Eq(e1, e2) => vec![e1, e2],
		Neg(l) => exprs(l),
		And(ls) => ls.iter().flat_map(exprs).collect(),
		Or(ls) => ls.iter().flat_map(exprs).collect(),
		App(_) => vec![],
		Exists(normal::LogicRel(_, l)) => exprs(l),
	}
}

fn var_elim<'c>(
	env: &Env<'c>,
	vars: &[(u32, &normal::Expr)],
	cong: &[(u32, &normal::Expr)],
) -> (Vector<DataType>, Vector<Option<Expr<'c>>>) {
	let groups = vars.iter().chain(cong).copied().into_group_map();
	let vars = vars
		.iter()
		.map(|&(g, e)| match e {
			&shared::Expr::Var(v, ref ty) => (g, v, ty.clone()),
			_ => unreachable!(),
		})
		.collect_vec();

	let Env(subst, lvl, _) = env;
	let level = subst.len();
	let bound = level..level + vars.len();
	let mut scope = Vector::new();
	let mut keys: HashSet<_> = vars.iter().map(|&(_, v, _)| v).collect();
	let mut deps_map = BTreeMap::new();
	let (exprs, mut var_subst) = vars
		.into_iter()
		.map(|(g, v, ty)| {
			let group = groups.get(&g).unwrap();
			keys.remove(&v);
			if let Some((_, deps, expr)) = group
				.iter()
				.filter_map(|&expr| {
					let deps = expr.deps(&bound);
					let root_deps = root_deps(&deps, &deps_map);
					root_deps.is_subset(&keys).then(|| (root_deps.len(), deps, expr))
				})
				.min_by_key(|a| a.0)
			{
				log::info!("[dep] {} -> {}", v, expr);
				deps_map.insert(v, deps);
				(expr.clone(), None)
			} else {
				keys.insert(v);
				let new_v = VL(lvl + scope.len());
				log::info!("[key] {} ~> {}", v, new_v);
				scope.push_back(ty.clone());
				(normal::Expr::Var(v, ty.clone()), Some(Expr::Var(new_v, ty)))
			}
		})
		.unzip();

	fn root_deps(vars: &HashSet<VL>, deps_map: &BTreeMap<VL, HashSet<VL>>) -> HashSet<VL> {
		let saturate = |var, deps: &BTreeMap<_, _>| {
			deps.get(&var).map_or_else(|| HashSet::unit(var), |vars| root_deps(vars, deps))
		};
		HashSet::unions(vars.iter().map(|&v| saturate(v, deps_map)))
	}

	fn prune<'c>(
		v: VL,
		keys: &HashSet<VL>,
		deps_map: &mut BTreeMap<VL, HashSet<VL>>,
		var_subst: &mut Vector<Option<Expr<'c>>>,
		exprs: &Vec<normal::Expr>,
		env: &Env<'c>,
	) {
		if let Some((v, deps)) = deps_map.remove_entry(&v) {
			deps.into_iter().for_each(|w| prune(w, keys, deps_map, var_subst, exprs, env));
			let i = v.0 - env.0.len();
			var_subst[i] = Some((&env.append(var_subst.clone())).eval(exprs[i].clone()));
		};
	}

	while let Some((&v, _)) = deps_map.first_key_value() {
		prune(v, &keys, &mut deps_map, &mut var_subst, &exprs, env);
	}
	(scope, var_subst)
}

impl<'c> Eval<normal::Term, Option<Term<'c>>> for &Env<'c> {
	fn eval(self, source: normal::Term) -> Option<Term<'c>> {
		let Env(subst, lvl, z3_env) = self;
		let z3_env = z3_env.extend(&source.scope);
		let solver = &z3_env.0.solver;
		let constraint = (&z3_env).eval(&source.logic);
		let vars = shared::Expr::vars(subst.len(), source.scope.clone());
		let exprs = vars
			.iter()
			.chain(exprs(&source.logic))
			.filter(|e| e.in_scope(subst.len() + source.scope.len()))
			.collect_vec();
		let z3_asts = exprs.iter().map(|&e| (&z3_env).eval(e)).collect_vec();
		let z3_asts = z3_asts.iter().map(|e| e as &dyn Ast).collect_vec();
		solver.push();
		solver.assert(&constraint);
		let handle = solver.get_context().handle();
		let checked = crossbeam::atomic::AtomicCell::new(false);
		let (ids, res) = crossbeam::thread::scope(|s| {
			let checked = &checked;
			let p = crossbeam::sync::Parker::new();
			let u = p.unparker().clone();
			s.spawn(move |_| {
				p.park_timeout(Duration::from_secs(10));
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
		solver.pop(1);
		match res {
			SatResult::Unsat => None,
			SatResult::Unknown => {
				let scope = source.scope;
				let vars = &Expr::vars(*lvl, scope.clone()).into_iter().map(Some).collect();
				let env = &Env(subst + vars, lvl + scope.len(), z3_env);
				let logic = env.eval(source.logic);
				let apps = env.eval(source.apps);
				Some(Term { scope, logic, apps })
			},
			SatResult::Sat => {
				let groups = ids.into_iter().zip(exprs).collect_vec();
				log::info!(
					"Congruence groups: {}",
					groups.iter().map(|(g, e)| format!("[{}, {}]", g, e)).join(", ")
				);
				let (vars, cong) = groups.split_at(source.scope.len());
				let env = &Env(subst.clone(), *lvl, z3_env.clone());
				let (scope, ref new_subst) = var_elim(env, vars, cong);
				let env = &Env(subst + new_subst, lvl + scope.len(), z3_env);
				let logic = env.eval(source.logic);
				let apps = env.eval(source.apps);
				Some(Term { scope, logic, apps })
			},
		}
	}
}
