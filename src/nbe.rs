//! # Normalization by evaluation (NBE)
//! NBE is a common technique employed by theorem provers for term/type normalization.
//! It is used mainly for reducing terms in various style of lambda calculus,
//! but here we make some changes and adapt it for normalizing U-expressions.
//!
//! ## References
//! 1. https://en.wikipedia.org/wiki/Normalisation_by_evaluation (NBE on simply typed lambda calculus)
//! 2. https://github.com/jozefg/nbe-for-mltt/blob/master/nbe-explanation.md (NBE in a dependent type theory)

use shared::{Env, Schema, VIndex, VLevel};
use {semantics as sem, syntax as syn};

use crate::nbe::semantics::{Closure, Product, Summation};
use crate::nbe::shared::{Predicate, Tuple};
use crate::nbe::syntax::Table;

pub(crate) mod semantics;
pub(crate) mod shared;
pub(crate) mod syntax;

// SPNF: +, Sum, [[Pred], Squash, Not, [Table]]
pub(crate) fn eval(term: syn::Term, env: &Env<VLevel>) -> sem::Term {
	use syn::Term::*;
	match term {
		Zero => sem::Term::default(),
		One => sem::Term(vec![Product::default()]),
		Add(t1, t2) => eval(*t1, env) + eval(*t2, env),
		Sum(schema, body) => {
			sem::Term(vec![Product::with_sum(schema, Closure { body: *body, env: env.clone() })])
		},
		Mul(t1, t2) => eval(*t1, env) * eval(*t2, env),
		Squash(term) => sem::Term(vec![Product::with_squash(eval(*term, env))]),
		Not(term) => sem::Term(vec![Product::with_not(eval(*term, env))]),
		Pred(pred) => sem::Term(vec![Product::with_preds(vec![env.eval_pred(pred)])]),
		App(table, tuple) => apply(table, tuple, env),
	}
}

fn apply(table: Table, tuple: Tuple<VIndex>, env: &Env<VLevel>) -> sem::Term {
	let t = env.eval_tup(tuple);
	match table {
		Table::Var(i) => sem::Term(vec![Product::with_app(env.get_by_index(i), t)]),
		Table::Lam(schema, body) => {
			let mut env = env.clone();
			match t {
				Tuple::Var(l) => env.add_inner(l),
				_ => unreachable!(),
			}
			eval(*body, &env)
		},
	}
}

/// Fully reduce a product such that no unexpanded summation is left.
pub(crate) fn full_reduce(
	mut prod: Product,
	mut env: Env<VIndex>,
	mut scopes: Vec<Schema>,
) -> Vec<(Product, Env<VIndex>, Vec<Schema>)> {
	if let Some(Summation { schema, summand: Closure { body, env: mut sum_env } }) = prod.sums.pop()
	{
		sum_env.add_inner(VLevel(env.size()));
		env.add_outer(VIndex(env.size()));
		scopes.push(schema);
		(sem::Term(vec![prod]) * eval(body, &sum_env))
			.0
			.into_iter()
			.flat_map(|prod| full_reduce(prod, env.clone(), scopes.clone()))
			.collect()
	} else {
		vec![(prod, env, scopes)]
	}
}

/// Read back a syntactic term from a semantic term.
pub(crate) fn read(term: sem::Term, env: &Env<VIndex>) -> syn::Term {
	term.0.into_iter().map(|prod| read_prod(prod, env)).fold(syn::Term::Zero, |t, t1| t + t1)
}

fn read_prod(prod: Product, env: &Env<VIndex>) -> syn::Term {
	let mut result = syn::Term::Zero;
	for (Product { preds, squash, not, apps, .. }, env, scopes) in
		full_reduce(prod, env.clone(), Vec::new())
	{
		let mut term = syn::Term::One;
		term *= preds
			.into_iter()
			.map(|pred| syn::Term::Pred(env.read_pred(pred)))
			.fold(syn::Term::One, |t, p| t * p);
		if let Some(squash) = squash {
			term *= syn::Term::Squash(Box::new(read(*squash, &env)));
		}
		if let Some(not) = not {
			term *= syn::Term::Not(Box::new(read(*not, &env)));
		}
		for (f, tup) in apps {
			term *= syn::Term::App(Table::Var(env.get_by_level(f)), env.read_tup(tup));
		}
		for schema in scopes.into_iter().rev() {
			term = syn::Term::Sum(schema, Box::new(term));
		}
		result += term;
	}
	result
}

pub fn normalize(term: syn::Term, env: Env<VLevel>) -> syn::Term {
	read(eval(term, &env), &env.transpose())
}
