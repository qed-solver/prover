use std::rc::Rc;
use std::time::{Duration, Instant};

use imbl::vector;
use serde::{Deserialize, Serialize};
use z3::{Config, Context, Solver};

use crate::pipeline::normal::Z3Env;
use crate::pipeline::shared::{Ctx, Eval, Schema};
use crate::pipeline::unify::{Unify, UnifyEnv};

pub mod normal;
mod null;
pub mod partial;
pub mod relation;
pub mod shared;
pub mod stable;
pub mod syntax;
#[cfg(test)]
mod tests;
pub mod unify;

#[derive(Serialize, Deserialize)]
pub struct Input {
	schemas: Vec<Schema>,
	pub queries: (relation::Relation, relation::Relation),
	#[serde(default)]
	help: (String, String),
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Stats {
	pub provable: bool,
	pub panicked: bool,
	pub complete_fragment: bool,
	pub equiv_class_duration: Duration,
	pub equiv_class_timed_out: bool,
	pub smt_duration: Duration,
	pub smt_timed_out: bool,
	pub nontrivial_perms: bool,
	pub translate_duration: Duration,
	pub normal_duration: Duration,
	pub stable_duration: Duration,
	pub unify_duration: Duration,
	pub total_duration: Duration,
}

pub fn unify(Input { schemas, queries: (rel1, rel2), help }: Input) -> (bool, Stats) {
	let mut stats = Stats::default();
	let subst = vector![];
	let env = relation::Env(&schemas, &subst, 0);
	log::info!("Schemas:\n{:?}", schemas);
	log::info!("Input:\n{}\n{}", help.0, help.1);
	stats.complete_fragment = rel1.complete() && rel2.complete();
	if rel1 == rel2 {
		println!("Trivially true!");
		return (true, stats);
	}
	let syn_start = Instant::now();
	let rel1 = env.eval(rel1);
	let rel2 = env.eval(rel2);
	stats.translate_duration = syn_start.elapsed();
	log::info!("Syntax left:\n{}", rel1);
	log::info!("Syntax right:\n{}", rel2);
	if rel1 == rel2 {
		return (true, stats);
	}
	let nom_env = &vector![];
	let eval_nom = |rel: syntax::Relation| -> normal::Relation {
		let rel = (&partial::Env::default()).eval(rel);
		nom_env.eval(rel)
	};
	let norm_start = Instant::now();
	let rel1 = eval_nom(rel1);
	let rel2 = eval_nom(rel2);
	stats.normal_duration = norm_start.elapsed();
	log::info!("Normal left:\n{}", rel1);
	log::info!("Normal right:\n{}", rel2);
	if rel1 == rel2 {
		return (true, stats);
	}
	let config = Config::new();
	let z3_ctx = &Context::new(&config);
	let ctx = Rc::new(Ctx::new_with_stats(Solver::new(z3_ctx), stats));
	let z3_env = Z3Env::empty(ctx.clone());
	let eval_stb = |nom: normal::Relation| -> normal::Relation {
		let env = &stable::Env(vector![], z3_env.clone());
		let stb = env.eval(nom);
		nom_env.eval(stb)
	};
	let stb_start = Instant::now();
	let rel1 = eval_stb(rel1);
	let rel2 = eval_stb(rel2);
	ctx.stats.borrow_mut().stable_duration = stb_start.elapsed();
	log::info!("Stable left:\n{}", rel1);
	log::info!("Stable right:\n{}", rel2);
	if rel1 == rel2 {
		return (true, ctx.stats.borrow().clone());
	}
	let env = UnifyEnv(ctx.clone(), vector![], vector![]);
	let unify_start = Instant::now();
	let res = env.unify(&rel1, &rel2);
	ctx.stats.borrow_mut().unify_duration = unify_start.elapsed();
	let stats = ctx.stats.borrow().clone();
	(res, stats)
}
