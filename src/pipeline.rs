use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use imbl::{vector, Vector};
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

pub fn evaluate(rel: syntax::Relation, schemas: &Vector<Schema>) -> normal::Relation {
	log::info!("Syntax:\n{}", rel);
	let prt: partial::Relation = (&partial::Env::default()).eval(rel);
	let nom_env = &normal::Env(vector![], schemas.clone());
	let nom = nom_env.eval(prt);
	log::info!("Normal:\n{}", nom);
	let mut config = Config::new();
	config.set_timeout_msec(2000);
	let z3_ctx = &Context::new(&config);
	let ctx = Rc::new(Ctx::new(Solver::new(z3_ctx)));
	let uexpr_subst = vector![];
	let z3_subst = vector![];
	let h_ops = Rc::new(RefCell::new(HashMap::new()));
	let rel_h_ops = Rc::new(RefCell::new(HashMap::new()));
	let env = &stable::Env(uexpr_subst, 0, Z3Env(ctx, z3_subst, h_ops, rel_h_ops));
	let stb = env.eval(nom);
	let nom = nom_env.eval(stb);
	log::info!("Stable:\n{}", nom);
	nom
}

pub fn unify(rel1: normal::Relation, rel2: normal::Relation) -> bool {
	let mut config = Config::new();
	config.set_timeout_msec(4000);
	let z3_ctx = Context::new(&config);
	let ctx = Rc::new(Ctx::new(Solver::new(&z3_ctx)));
	let subst1 = vector![];
	let subst2 = vector![];
	let env = UnifyEnv(ctx, subst1, subst2);
	env.unify(&rel1, &rel2)
}
