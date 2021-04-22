use std::collections::HashMap;

use shared::{Env, VL};
use {semantics as sem, syntax as syn};

use crate::nbe::semantics::{Application, Closure, StableTerm, Summation, Term};
use crate::nbe::shared::{DataType, Entry, Expr, Predicate};
use crate::nbe::syntax::Relation;

pub(crate) mod semantics;
pub(crate) mod shared;
pub(crate) mod syntax;

fn eval(term: syn::UExpr, env: &Env) -> sem::UExpr {
	use syn::UExpr::*;
	match term {
		Zero => sem::UExpr::default(),
		One => sem::UExpr(vec![Term::default()]),
		Add(t1, t2) => eval(*t1, env) + eval(*t2, env),
		Sum(types, body) => {
			sem::UExpr(vec![Term::with_sum(types, Closure { body: *body, env: env.clone() })])
		},
		Mul(t1, t2) => eval(*t1, env) * eval(*t2, env),
		Squash(term) => sem::UExpr(vec![Term::with_squash(eval(*term, env))]),
		Not(term) => sem::UExpr(vec![Term::with_not(eval(*term, env))]),
		Pred(pred) => sem::UExpr(vec![Term::with_preds(vec![env.eval_pred(pred)])]),
		App(table, args) => apply(table, args, env),
	}
}

fn apply(table: Relation, args: Vec<VL>, env: &Env) -> sem::UExpr {
	match table {
		Relation::Var(l) => sem::UExpr(vec![Term::with_app(env.get_var(l), env.read_args(args))]),
		Relation::Lam(scheme, body) => {
			let mut env = env.clone();
			for arg in args {
				env.introduce(env.get(arg).clone());
			}
			eval(*body, &env)
		},
	}
}

/// Fully reduce a term such that no unexpanded summation is left.
fn full_reduce(mut term: Term, mut scopes: Vec<DataType>, level: usize) -> Vec<StableTerm> {
	if let Some(Summation { types, summand: Closure { body, env: mut sum_env } }) = term.sums.pop()
	{
		scopes.extend(types.clone());
		let vars: Vec<_> = types
			.iter()
			.enumerate()
			.map(|(i, ty)| Entry::Value(VL(i + level), ty.clone()))
			.collect();
		sum_env.append(vars);
		(sem::UExpr(vec![term]) * eval(body, &sum_env))
			.into_terms()
			.flat_map(|t| full_reduce(t, scopes.clone(), level + types.len()))
			.collect()
	} else {
		vec![StableTerm::from(term, scopes)]
	}
}

/// Read back a syntactic term from a semantic term.
fn read(term: sem::UExpr, env: &Env) -> syn::UExpr {
	term.into_terms()
		.flat_map(|t| full_reduce(t, vec![], env.size()))
		.map(|t| read_term(t, env))
		.fold(syn::UExpr::Zero, |t, t1| t + t1)
}

fn chase(Application { table, args }: Application, term: &mut StableTerm, env: &Env) {
	let schema = env.get_schema(table);
	for (&col, &tab) in &schema.foreign {
		let dest_schema = env.get_schema(tab);
		let primary_col = dest_schema.primary.unwrap();
		let types = vec![DataType::Any; dest_schema.types.len()];
		let level = env.size() + term.scopes.len();
		let vars: Vec<_> = (0..dest_schema.types.len()).map(|i| VL(level + i)).collect();
		term.equiv.equate(Expr::Var(args[col]), Expr::Var(vars[primary_col]));
		let new_app = Application::new(tab, vars);
		term.apps.push(new_app.clone());
		term.scopes.extend(types);
		chase(new_app, term, env);
	}
}

fn merge_keys(term: &mut StableTerm, env: &Env) {
	let mut i = 0;
	while i < term.apps.len() {
		let Application { table: t1, args: args1 } = term.apps[i].clone();
		let mut j = i + 1;
		while j < term.apps.len() {
			let Application { table: t2, args: args2 } = term.apps[j].clone();
			if t1 == t2 {
				let e1 = env.get_schema(t1).primary.map(|c1| Expr::Var(args1[c1]));
				let e2 = env.get_schema(t2).primary.map(|c2| Expr::Var(args2[c2]));
				if let (Some(c1), Some(c2)) = (e1, e2) {
					if term.equiv.equal(&c1, &c2) {
						args1.iter().zip(args2.iter()).for_each(|(&a1, &a2)| {
							term.equiv.equate(Expr::Var(a1), Expr::Var(a2));
						});
						term.apps.swap_remove(j);
						continue;
					}
				}
			}
			j += 1;
		}
		i += 1;
	}
}

fn read_term(mut term: StableTerm, env: &Env) -> syn::UExpr {
	for app in term.apps.clone() {
		chase(app, &mut term, env);
	}
	merge_keys(&mut term, env);
	let StableTerm { mut preds, mut equiv, squash, not, apps, scopes } = term;
	let mut new_scopes = vec![];
	let mut mapping = HashMap::new();
	let level = env.size();
	let mut env = env.clone();
	let mut free = level;
	for (i, ty) in scopes.iter().enumerate() {
		let var = Expr::Var(VL(level + i));
		if let Some(Expr::Var(v)) = equiv.get(&var) {
			let entry = mapping.entry(v).or_insert_with(|| {
				new_scopes.push(ty.clone());
				free += 1;
				Entry::Value(VL(free - 1), ty.clone())
			});
			env.introduce(entry.clone());
		}
	}
	for (expr, root) in equiv.into_pairs() {
		preds.push(Predicate::Eq(expr, root))
	}
	let mut syn_term = syn::UExpr::One;
	syn_term *= preds
		.into_iter()
		.filter_map(|pred| match env.read_pred(pred) {
			Predicate::Eq(e1, e2) if e1 == e2 => None,
			pred => Some(syn::UExpr::Pred(pred)),
		})
		.fold(syn::UExpr::One, |t, p| t * p);
	if let Some(squash) = squash {
		syn_term *= syn::UExpr::Squash(Box::new(read(*squash, &env)));
	}
	if let Some(not) = not {
		syn_term *= !read(*not, &env);
	}
	for app in apps {
		syn_term *= syn::UExpr::App(Relation::Var(env.get_var(app.table)), env.read_args(app.args));
	}
	syn::UExpr::Sum(scopes, Box::new(syn_term))
}

pub fn normalize(term: syn::UExpr, env: &Env) -> syn::UExpr {
	read(eval(term, env), env)
}
