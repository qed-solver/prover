use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

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
	queries: (relation::Relation, relation::Relation),
	help: (String, String),
}

pub fn unify(Input { schemas, queries: (rel1, rel2), help }: Input) -> bool {
	let subst = vector![];
	let env = relation::Env(&schemas, &subst, 0);
	log::info!("Schemas:\n{:?}", schemas);
	log::info!("Input:\n{}\n{}", help.0, help.1);
	if rel1 == rel2 {
		return true;
	}
	let rel1 = env.eval(rel1);
	let rel2 = env.eval(rel2);
	if rel1 == rel2 {
		return true;
	}
	log::info!("Syntax left:\n{}", rel1);
	log::info!("Syntax right:\n{}", rel2);
	let nom_env = &normal::Env(vector![], schemas.clone().into());
	let eval_nom = |rel: syntax::Relation| -> normal::Relation {
		let rel = (&partial::Env::default()).eval(rel);
		nom_env.eval(rel)
	};
	let rel1 = eval_nom(rel1);
	let rel2 = eval_nom(rel2);
	log::info!("Normal left:\n{}", rel1);
	log::info!("Normal right:\n{}", rel2);
	if rel1 == rel2 {
		return true;
	}
	let eval_stb = |nom: normal::Relation| -> normal::Relation {
		let mut config = Config::new();
		config.set_timeout_msec(2000);
		let z3_ctx = &Context::new(&config);
		let ctx = Rc::new(Ctx::new(Solver::new(z3_ctx)));
		let h_ops = Rc::new(RefCell::new(HashMap::new()));
		let rel_h_ops = Rc::new(RefCell::new(HashMap::new()));
		let env = &stable::Env(vector![], 0, Z3Env(ctx, vector![], h_ops, rel_h_ops));
		let stb = env.eval(nom);
		nom_env.eval(stb)
	};
	let rel1 = eval_stb(rel1);
	let rel2 = eval_stb(rel2);
	log::info!("Stable left:\n{}", rel1);
	log::info!("Stable right:\n{}", rel2);
	if rel1 == rel2 {
		return true;
	}
	let mut config = Config::new();
	config.set_timeout_msec(4000);
	let z3_ctx = Context::new(&config);
	let ctx = Rc::new(Ctx::new(Solver::new(&z3_ctx)));
	let env = UnifyEnv(ctx, vector![], vector![]);
	env.unify(&rel1, &rel2)
}
