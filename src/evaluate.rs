use std::collections::HashMap;

use shared::{Env, VL};
use {normal as nom, stable as stb, syntax as syn};

use crate::evaluate::normal::{Application, Closure, EquivClass, Summation};
use crate::evaluate::shared::{DataType, Entry, Expr, Predicate};
use crate::evaluate::syntax::Relation;

pub(crate) mod normal;
pub(crate) mod shared;
pub(crate) mod stable;
pub(crate) mod syntax;

/// Syntax to normalized
fn normalize(term: syn::UExpr, env: &Env<Entry>) -> nom::UExpr {
	use syn::UExpr::*;
	match term {
		Zero => nom::UExpr::default(),
		One => nom::UExpr::one(),
		Add(t1, t2) => normalize(*t1, env) + normalize(*t2, env),
		Sum(types, body) => nom::UExpr::with_sum(types, Closure { body: *body, env: env.clone() }),
		Mul(t1, t2) => normalize(*t1, env) * normalize(*t2, env),
		Squash(term) => nom::UExpr::with_squash(normalize(*term, env)),
		Not(term) => nom::UExpr::with_not(normalize(*term, env)),
		Pred(pred) => nom::UExpr::with_preds(vec![env.eval_pred(pred)]),
		App(table, args) => apply(table, args, env),
	}
}

fn apply(table: Relation, args: Vec<VL>, env: &Env<Entry>) -> nom::UExpr {
	match table {
		Relation::Var(l) => nom::UExpr::with_app(env.get_var(l), env.eval_args(args)),
		Relation::Lam(types, body) => {
			let entries = args.into_iter().zip(types).map(|(v, ty)| {
				let entry = env.get(v);
				assert_eq!(entry.ty(), ty);
				entry.clone()
			});
			normalize(*body, &env.append(entries))
		},
	}
}

/// Normalized to stabilized
fn stabilize(uexp: nom::UExpr, env: &Env<Entry>) -> stb::UExpr {
	let terms = uexp
		.into_terms()
		.flat_map(|t| full_reduce(t, vec![], env.size()))
		.map(|(mut term, mut scopes)| {
			for app in term.apps.clone() {
				chase(app, &mut term, &mut scopes, env);
			}
			let mut equiv = term.extract_equiv();
			merge_keys(&mut term, env, &mut equiv);
			let new_env = merge_scopes(&mut scopes, env, &mut equiv);
			for (expr, root) in equiv.into_pairs() {
				term.preds.push(Predicate::Eq(root, expr));
			}
			let preds = term
				.preds
				.into_iter()
				.filter_map(|pred| match new_env.eval_pred(pred) {
					Predicate::Eq(e1, e2) if e1 == e2 => None,
					pred => Some(pred),
				})
				.collect();
			let apps = term
				.apps
				.into_iter()
				.map(|app| {
					Application::new(new_env.get_var(app.table), new_env.eval_args(app.args))
				})
				.collect();
			let not = term.not.map(|e| Box::new(stabilize(*e, &new_env)));
			let squash = term.squash.map(|e| Box::new(stabilize(flatten_squash(*e), &new_env)));
			stb::Term::new(preds, squash, not, apps, scopes)
		})
		.collect();
	stb::UExpr(terms)
}

fn full_reduce(
	mut term: nom::Term,
	mut scopes: Vec<DataType>,
	level: usize,
) -> Vec<(nom::Term, Vec<DataType>)> {
	if let Some(Summation { types, summand: Closure { body, mut env } }) = term.sums.pop() {
		scopes.extend(types.clone());
		let next_level = level + types.len();
		let vars: Vec<_> =
			(level..next_level).zip(types).map(|(l, ty)| Entry::Value(VL(l), ty)).collect();
		env.extend(vars);
		(nom::UExpr(vec![term]) * normalize(body, &env))
			.into_terms()
			.flat_map(|t| full_reduce(t, scopes.clone(), next_level))
			.collect()
	} else {
		vec![(term, scopes)]
	}
}

fn chase(app: Application, term: &mut nom::Term, scopes: &mut Vec<DataType>, env: &Env<Entry>) {
	let schema = env.get(app.table).sch();
	for (&col, &tab) in &schema.foreign {
		let dest_schema = env.get(tab).sch();
		let primary_col = dest_schema.primary.unwrap();
		let types = vec![DataType::Any; dest_schema.types.len()];
		let level = env.size() + scopes.len();
		let vars: Vec<_> = (0..dest_schema.types.len()).map(|i| VL(level + i)).collect();
		term.preds.push(Predicate::Eq(Expr::Var(app.args[col]), Expr::Var(vars[primary_col])));
		let new_app = Application::new(tab, vars);
		term.apps.push(new_app.clone());
		scopes.extend(types);
		chase(new_app, term, scopes, env);
	}
}

fn merge_keys(term: &mut nom::Term, env: &Env<Entry>, equiv: &mut EquivClass) {
	let mut i = 0;
	while i < term.apps.len() {
		let Application { table: t1, args: args1 } = term.apps[i].clone();
		let mut j = i + 1;
		while j < term.apps.len() {
			let Application { table: t2, args: args2 } = term.apps[j].clone();
			if t1 == t2 {
				let e1 = env.get(t1).sch().primary.map(|c1| Expr::Var(args1[c1]));
				let e2 = env.get(t2).sch().primary.map(|c2| Expr::Var(args2[c2]));
				if let (Some(c1), Some(c2)) = (e1, e2) {
					if equiv.equal(&c1, &c2) {
						args1.iter().zip(args2.iter()).for_each(|(&a1, &a2)| {
							equiv.equate(Expr::Var(a1), Expr::Var(a2));
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

fn merge_scopes(
	scopes: &mut Vec<DataType>,
	env: &Env<Entry>,
	equiv: &mut EquivClass,
) -> Env<Entry> {
	let mut new_scopes = vec![];
	let mut mapping = HashMap::new();
	let level = env.size();
	let mut env = env.clone();
	let mut free = level;
	for (i, ty) in scopes.iter().enumerate() {
		let var = Expr::Var(VL(level + i));
		let entry = if let Some(Expr::Var(v)) = equiv.get(&var) {
			if v.0 >= level {
				mapping
					.entry(v)
					.or_insert_with(|| {
						new_scopes.push(ty.clone());
						let entry = Entry::Value(VL(free), ty.clone());
						free += 1;
						entry
					})
					.clone()
			} else {
				Entry::Value(v, ty.clone())
			}
		} else {
			new_scopes.push(ty.clone());
			let entry = Entry::Value(VL(free), ty.clone());
			free += 1;
			entry
		};
		env.introduce(entry);
	}
	*scopes = new_scopes;
	env
}

fn flatten_squash(uexp: nom::UExpr) -> nom::UExpr {
	let terms = uexp
		.into_terms()
		.flat_map(|mut term| {
			let inner = std::mem::replace(&mut term.squash, None)
				.map_or(nom::UExpr::one(), |e| flatten_squash(*e));
			term.not = term.not.map(|e| Box::new(flatten_squash(*e)));
			(nom::UExpr::with_term(term) * inner).into_terms()
		})
		.collect();
	nom::UExpr(terms)
}

pub fn evaluate(uexp: syn::UExpr, env: &Env<Entry>) -> stb::UExpr {
	stabilize(normalize(uexp, env), env)
}
