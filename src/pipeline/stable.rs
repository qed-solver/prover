use std::collections::BTreeMap;
use std::time::Instant;

use imbl::{vector, HashSet, Vector};
use itertools::Itertools;
use z3::ast::Ast;
use z3::SatResult;

use super::normal::Z3Env;
use super::shared::{Ctx, DataType, Eval, Lambda, Sigma, Terms};
use crate::pipeline::normal;
use crate::pipeline::shared::{self, Typed, VL};

#[derive(Clone)]
pub struct Aggr<'c>(
	pub String,
	pub Vector<DataType>,
	pub Env<'c>,
	pub normal::Inner,
	pub normal::Expr,
);

impl Typed for Aggr<'_> {
	fn ty(&self) -> DataType {
		self.4.ty()
	}
}

pub type Expr<'c> = shared::Expr<UExpr<'c>, Relation<'c>, Aggr<'c>>;
pub type Neutral<'c> = shared::Neutral<Relation<'c>, Expr<'c>>;
pub type Logic<'c> = shared::Logic<UExpr<'c>, Expr<'c>>;

#[derive(Clone)]
pub struct Relation<'c>(pub Vector<DataType>, pub Env<'c>, pub normal::UExpr);
pub type UExpr<'c> = Terms<Term<'c>>;

// Env(subst: C -> stb::Expr D, z3: C -> z3::Expr): Eval (nom::Expr C) (stb::Expr D)
#[derive(Clone)]
pub struct Env<'c>(pub Vector<Option<Expr<'c>>>, pub Z3Env<'c>);

impl<'c> Env<'c> {
	pub fn append(&self, subst: Vector<Option<Expr<'c>>>) -> Self {
		Env(self.0.clone() + subst, self.1.clone())
	}

	pub fn extend(&self, base: usize, scope: Vector<DataType>) -> Self {
		let vars = shared::Expr::vars(base, scope.clone()).into_iter().map(Some).collect();
		Env(self.0.clone() + vars, self.1.extend(&scope))
	}
}

#[derive(Clone)]
pub struct Term<'c>(pub Vector<DataType>, pub Env<'c>, pub normal::Inner);

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

impl<'c> Eval<normal::Aggr, Expr<'c>> for &Env<'c> {
	fn eval(self, normal::Aggr(op, scope, i, e): normal::Aggr) -> Expr<'c> {
		Expr::Agg(Aggr(op, scope, self.clone(), *i, *e))
	}
}

impl<'c> Eval<normal::UExpr, UExpr<'c>> for &Env<'c> {
	fn eval(self, source: normal::UExpr) -> UExpr<'c> {
		source.into_iter().map(|term| self.eval(term)).collect()
	}
}

// env : C -> stb::Expr D
// cong : [(Id, nom::Expr (C + S))]
// S', C + S -> stb::Expr (D + S')
pub fn min_subst<'c>(
	env: &Env<'c>,
	scope: Vector<DataType>,
	context: &Vector<DataType>,
	cong: &[(u32, &normal::Expr)],
) -> (Vector<DataType>, Vector<Option<Expr<'c>>>) {
	let groups = cong.iter().copied().into_group_map();
	let Env(subst, _) = env;
	let level = subst.len();
	let bound = level..level + scope.len();
	let vars = bound.clone().map(VL);
	let var_groups = vars.clone().map(|v| {
		(
			v,
			cong.iter()
				.find(|&&(_, e)| e == &normal::Expr::Var(v, e.ty()))
				.map(|(g, _)| groups.get(g).unwrap()),
		)
	});
	let mut new_scope = Vector::new();
	let mut keys: HashSet<_> = vars.clone().collect();
	let mut deps_map = BTreeMap::new();

	fn root_deps(vars: &HashSet<VL>, deps_map: &BTreeMap<VL, HashSet<VL>>) -> HashSet<VL> {
		let saturate = |var, deps: &BTreeMap<_, _>| {
			deps.get(&var).map_or_else(|| HashSet::unit(var), |vars| root_deps(vars, deps))
		};
		HashSet::unions(vars.iter().map(|&v| saturate(v, deps_map)))
	}

	let (exprs, mut var_subst) = var_groups
		.zip(scope.clone())
		.map(|((v, es), ty)| {
			keys.remove(&v);
			if let Some((_, deps, expr)) = es
				.into_iter()
				.flatten()
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
				let new_v = VL(context.len() + new_scope.len());
				log::info!("[key] {} ~> {}", v, new_v);
				new_scope.push_back(ty.clone());
				(normal::Expr::Var(v, ty.clone()), Some(Expr::Var(new_v, ty)))
			}
		})
		.unzip();
	// Ensures v is mapped to some Expr
	fn prune<'c>(
		v: VL,
		deps_map: &mut BTreeMap<VL, HashSet<VL>>,
		var_subst: &mut Vector<Option<Expr<'c>>>,
		exprs: &Vec<normal::Expr>,
		env: &Env<'c>,
	) {
		if let Some((v, deps)) = deps_map.remove_entry(&v) {
			deps.into_iter().for_each(|w| prune(w, deps_map, var_subst, exprs, env));
			let i = v.0 - env.0.len();
			var_subst[i] = Some((&env.append(var_subst.clone())).eval(exprs[i].clone()));
		};
	}

	while let Some((&v, _)) = deps_map.first_key_value() {
		prune(v, &mut deps_map, &mut var_subst, &exprs, env);
	}
	(new_scope, var_subst)
}

impl<'c> Eval<normal::Term, Term<'c>> for &Env<'c> {
	fn eval(self, Sigma(scope, inner): normal::Term) -> Term<'c> {
		Term(scope, self.clone(), inner)
	}
}

pub type NormAgg<'c> = (Vector<DataType>, Logic<'c>, Vector<Neutral<'c>>, Expr<'c>);

impl<'c> Expr<'c> {
	pub fn split(self, aop: &str, context: &Vector<DataType>) -> Vector<NormAgg<'c>> {
		match self {
			Expr::Op(op, args, _) if op == aop => {
				args.into_iter().flat_map(|arg| arg.split(aop, context)).collect()
			},
			Expr::Agg(Aggr(op, old_scope, env, i, e)) if op == aop => {
				if let Some((scope, new_subst)) =
					stablize(&env, old_scope.clone(), context, i.logic.clone())
				{
					let Env(subst, z3_env) = env;
					let env = &Env(subst + new_subst, z3_env.extend(&old_scope));
					let logic = env.eval(i.logic);
					let apps = env.eval(i.apps);
					env.eval(e)
						.split(aop, &(context + &scope))
						.into_iter()
						.map(|(scp, l, aps, e)| {
							(&scope + &scp, Logic::And(vector![logic.clone(), l]), &apps + &aps, e)
						})
						.collect()
				} else {
					vector![]
				}
			},
			_ => vector![(vector![], Logic::tt(), vector![], self)],
		}
	}
}

// Env: C -> stb::Expr D
// C + S ~> C + S'
pub fn stablize<'c>(
	env: &Env<'c>,
	scope: Vector<DataType>,
	context: &Vector<DataType>,
	logic: normal::Logic,
) -> Option<(Vector<DataType>, Vector<Option<Expr<'c>>>)> {
	let Env(subst, z3_env) = env;
	let z3_env = &z3_env.extend(&scope);
	let solver = &z3_env.ctx.solver;
	let constraint = z3_env.eval(&logic);
	let vars = shared::Expr::vars(subst.len(), scope.clone());
	let exprs = vars
		.iter()
		.chain(logic.exprs())
		.filter(|e| e.in_scope(subst.len() + scope.len()))
		.unique()
		.collect_vec();
	let z3_asts = exprs.iter().map(|&e| z3_env.eval(e)).collect_vec();
	let z3_asts = z3_asts.iter().map(|e| e as &dyn Ast).collect_vec();
	solver.push();
	solver.assert(&constraint);
	let handle = solver.get_context().handle();
	let checked = crossbeam::atomic::AtomicCell::new(false);
	let timed_out = crossbeam::atomic::AtomicCell::new(false);
	let equiv_start = Instant::now();
	let (ids, res) = std::thread::scope(|s| {
		let checked = &checked;
		let timed_out = &timed_out;
		let p = crossbeam::sync::Parker::new();
		let u = p.unparker().clone();
		s.spawn(move || {
			p.park_timeout(Ctx::timeout());
			if !checked.load() {
				timed_out.store(true);
				handle.interrupt();
			}
		});
		let (ids, res) = solver.get_implied_equalities(z3_asts.as_slice());
		checked.store(true);
		u.unpark();
		(ids, res)
	});
	z3_env.ctx.update_equiv_class_duration(equiv_start.elapsed(), timed_out.into_inner());
	solver.pop(1);
	match res {
		SatResult::Unsat => None,
		SatResult::Unknown => {
			let vars = Expr::vars(context.len(), scope.clone()).into_iter().map(Some).collect();
			Some((scope, vars))
		},
		SatResult::Sat => {
			let groups = ids.into_iter().zip(exprs).collect_vec();
			log::info!(
				"Congruence groups: {}",
				groups.iter().map(|(g, e)| format!("[{}, {}]", g, e)).join(", ")
			);
			let env = &Env(subst.clone(), z3_env.clone());
			Some(min_subst(env, scope, context, &groups))
		},
	}
}
