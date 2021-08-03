use std::collections::HashMap;

use shared::{Application, Env, VL};
use {normal as nom, scoped as scp, stable as stb, syntax as syn};

use crate::evaluate::normal::{Closure, Summation};
use crate::evaluate::scoped::EquivClass;
use crate::evaluate::shared::{DataType, Entry, Eval, Expr, Predicate};
use crate::evaluate::syntax::Relation;

pub(crate) mod normal;
pub(crate) mod scoped;
pub(crate) mod shared;
pub(crate) mod stable;
pub(crate) mod syntax;
#[cfg(test)]
mod tests;

/// Syntax to normalized
impl Eval for syn::UExpr {
	type Output = nom::UExpr;

	fn eval(self, env: &Env<Entry>) -> Self::Output {
		use syn::UExpr::*;
		match self {
			Zero => nom::UExpr::default(),
			One => nom::UExpr::one(),
			Add(t1, t2) => t1.eval(env) + t2.eval(env),
			Sum(types, body) => nom::UExpr::sum(types, Closure { body: *body, env: env.clone() }),
			Mul(t1, t2) => t1.eval(env) * t2.eval(env),
			Squash(term) => nom::UExpr::squash(term.eval(env)),
			Not(term) => nom::UExpr::not(term.eval(env)),
			Pred(pred) => nom::UExpr::preds(vec![pred.eval(env)]),
			App(table, args) => apply(table, args, env),
		}
	}
}

fn apply(table: Relation, args: Vec<VL>, env: &Env<Entry>) -> nom::UExpr {
	match table {
		Relation::Var(l) => nom::UExpr::app(env.get_var(l), env.eval_args(args)),
		Relation::Lam(types, body) => {
			let entries = args.into_iter().zip(types).map(|(v, ty)| {
				let entry = env.get(v);
				assert_eq!(entry.ty(), ty);
				entry.clone()
			});
			body.eval(&env.append(entries))
		},
	}
}

impl Eval for nom::UExpr {
	type Output = scp::UExpr;

	fn eval(self, env: &Env<Entry>) -> Self::Output {
		self.into_terms()
			.flat_map(|t| full_reduce(t, vec![], env.level))
			.map(|(term, scopes)| {
				let env = &env.append_vars(scopes.clone());
				let preds = term.preds.into_iter().map(|p| p.eval(env)).collect();
				let squash = term.squash.map(|sq| flatten_squash(sq.eval(env)));
				let not = term.not.map(|n| n.eval(env));
				let apps = term.apps.into_iter().map(|app| app.eval(env)).collect();
				scp::Term { preds, squash, not, apps, scopes }
			})
			.collect()
	}
}

fn full_reduce(
	mut term: nom::Term,
	mut scopes: Vec<DataType>,
	level: usize,
) -> Vec<(nom::Term, Vec<DataType>)> {
	if let Some(Summation { types, summand: Closure { body, env } }) = term.sums.pop() {
		scopes.extend(types.clone());
		let next_level = level + types.len();
		(nom::UExpr(vec![term]) * body.eval(&env.shift_to(level).append_vars(types)))
			.into_terms()
			.flat_map(|t| full_reduce(t, scopes.clone(), next_level))
			.collect()
	} else {
		vec![(term, scopes)]
	}
}

fn flatten_squash(uexp: scp::UExpr) -> scp::UExpr {
	uexp.into_terms()
		.flat_map(|mut term| {
			let inner =
				std::mem::replace(&mut term.squash, None).map_or(scp::UExpr::one(), flatten_squash);
			term.not = term.not.map(flatten_squash);
			inner.into_terms().map(move |t| {
				let mut term = term.clone();
				term.scopes.extend(t.scopes);
				term.preds.extend(t.preds);
				let t_apps = t.apps;
				let t_not = t.not;
				term.apps.extend(t_apps);
				term.not = term.not.map(|mut u1| {
					u1.0.extend(t_not.map_or(vec![], |u2| u2.0));
					u1
				});
				assert_eq!(term.squash, None);
				term
			})
		})
		.collect()
}

impl Eval for scp::UExpr {
	type Output = stb::UExpr;

	fn eval(self, env: &Env<Entry>) -> Self::Output {
		self.into_terms()
			.map(|mut term| {
				for app in term.apps.clone() {
					chase(&app, &mut term, env);
				}
				let mut equiv = term.extract_equiv();
				merge_keys(&mut term, &mut equiv, env);
				let new_env = &merge_scopes(&mut term.scopes, env, &mut equiv);
				term.preds.retain(|pred| !matches!(pred, Predicate::Eq(_, _)));
				for (expr, root) in equiv.into_pairs() {
					term.preds.push(Predicate::Eq(root, expr));
				}
				let preds = term
					.preds
					.into_iter()
					.filter_map(|pred| match pred.eval(new_env) {
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
				let not = term.not.map(|e| e.eval(new_env));
				let squash = term.squash.map(|e| e.eval(new_env));
				stb::Term::new(preds, squash, not, apps, term.scopes)
			})
			.collect()
	}
}

fn chase(app: &Application, term: &mut scp::Term, env: &Env<Entry>) {
	let schema = env.get(app.table).sch();
	for (&col, &tab) in &schema.foreign {
		let dest_schema = env.get(tab).sch();
		let primary_col = dest_schema.primary.unwrap();
		let types = vec![DataType::Any; dest_schema.types.len()];
		let level = env.size() + term.scopes.len();
		let vars: Vec<_> = (0..dest_schema.types.len()).map(|i| VL(level + i)).collect();
		term.preds.push(Predicate::Eq(Expr::Var(app.args[col]), Expr::Var(vars[primary_col])));
		let new_app = Application::new(tab, vars);
		term.apps.push(new_app.clone());
		term.scopes.extend(types);
		chase(&new_app, term, env);
	}
}

fn merge_keys(term: &mut scp::Term, equiv: &mut EquivClass, env: &Env<Entry>) {
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
	let mut free = env.level;
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
	env.level = free;
	*scopes = new_scopes;
	env
}

pub fn evaluate(rel: syn::Relation, env: &Env<Entry>) -> stb::Relation {
	log::info!("Syntax:\n{}", rel);
	let nom = rel.eval(env);
	log::info!("Normal:\n{}", nom);
	let scp = nom.eval(env);
	log::info!("Scoped:\n{}", scp);
	let stb = scp.eval(env);
	log::info!("Stable:\n{}", stb);
	stb
}
