use std::collections::HashMap;

use im::{vector, Vector};
use itertools::Itertools;
use shared::{Application, Env, VL};
use {normal as nom, partial as prt, stable as stb, syntax as syn};

use crate::evaluate::normal::EquivClass;
use crate::evaluate::partial::{Closure, Summation};
use crate::evaluate::shared::{DataType, Entry, Eval, Expr, Predicate, Relation};

pub mod normal;
pub mod partial;
pub mod shared;
pub mod stable;
pub mod syntax;
#[cfg(test)]
mod tests;

/// Syntax to partial
impl Eval<prt::UExpr> for syn::UExpr {
	fn eval(self, env: &Env<Entry>) -> prt::UExpr {
		use syn::UExpr::*;
		match self {
			Zero => prt::UExpr::zero(),
			One => prt::UExpr::one(),
			Add(t1, t2) => t1.eval(env) + t2.eval(env),
			Sum(types, body) => prt::UExpr::sum(types, Closure { body: *body, env: env.clone() }),
			Mul(t1, t2) => t1.eval(env) * t2.eval(env),
			Squash(term) => prt::UExpr::squash(term.eval(env)),
			Not(term) => prt::UExpr::not(term.eval(env)),
			Pred(pred) => prt::UExpr::preds(vec![pred.eval(env)]),
			App(table, args) => apply(table, args, env),
		}
	}
}

impl Eval<prt::Relation> for syn::Relation {
	fn eval(self, env: &Env<Entry>) -> prt::Relation {
		use shared::Relation::*;
		match self {
			Var(l) => Var(env.get_var(l)),
			Lam(types, body) => {
				prt::Relation::lam(types, Closure { body: *body, env: env.clone() })
			},
		}
	}
}

fn apply(table: syn::Relation, args: Vector<VL>, env: &Env<Entry>) -> prt::UExpr {
	use shared::Relation::*;
	match table {
		Var(l) => prt::UExpr::app(env.get_var(l), env.eval_args(args)),
		Lam(types, body) => {
			let entries = args.into_iter().zip(types).map(|(v, ty)| {
				let entry = env.get(v);
				assert_eq!(entry.ty(), ty);
				entry.clone()
			});
			body.eval(&env.append(entries))
		},
	}
}

impl Eval<nom::UExpr> for prt::UExpr {
	fn eval(self, env: &Env<Entry>) -> nom::UExpr {
		self.into_terms()
			.flat_map(|t| full_reduce(t, vector![], env.level))
			.map(|(term, scopes)| {
				let env = &env.extend(scopes.clone());
				let preds = term.preds.into_iter().map(|p| p.eval(env)).collect();
				let squash = term.squash.map(|sq| flatten_squash(sq.eval(env)));
				let not = term.not.map(|n| flatten_squash(n.eval(env)));
				let apps = term.apps.into_iter().map(|app| app.eval(env)).collect();
				nom::Term { preds, squash, not, apps, scopes }
			})
			.collect()
	}
}

impl Eval<nom::Relation> for prt::Relation {
	fn eval(self, env: &Env<Entry>) -> nom::Relation {
		use Relation::*;
		match self {
			Var(l) => Var(env.get_var(l)),
			Lam(types, body) => {
				let Closure { env: lam_env, body } = *body;
				let body = body
					.eval(&lam_env.shift_to(env.level).extend(types.clone()))
					.eval(&env.extend(types.clone()));
				Relation::lam(types, body)
			},
		}
	}
}

fn full_reduce(
	mut term: prt::Term,
	scopes: Vector<DataType>,
	level: usize,
) -> Vec<(prt::Term, Vector<DataType>)> {
	if let Some(Summation { types, summand: Closure { body, env } }) = term.sums.pop_front() {
		let scopes = scopes + types.clone();
		let next_level = level + types.len();
		(prt::UExpr(vector![term]) * body.eval(&env.shift_to(level).extend(types)))
			.into_terms()
			.flat_map(|t| full_reduce(t, scopes.clone(), next_level))
			.collect()
	} else {
		vec![(term, scopes)]
	}
}

fn flatten_squash(uexp: nom::UExpr) -> nom::UExpr {
	uexp.into_terms()
		.flat_map(|term| {
			term.squash.clone().map_or(nom::UExpr::one(), flatten_squash).into_terms().map(
				move |t| {
					let term = term.clone();
					let scopes = term.scopes + t.scopes;
					let preds = term.preds + t.preds;
					let apps = term.apps + t.apps;
					let not = match (term.not.map(flatten_squash), t.not) {
						(Some(u1), Some(u2)) => Some(u1 + u2),
						(s, None) | (None, s) => s,
					};
					assert_eq!(t.squash, None);
					nom::Term { scopes, preds, apps, not, squash: None }
				},
			)
		})
		.collect()
}

impl Eval<stb::UExpr> for nom::UExpr {
	fn eval(self, env: &Env<Entry>) -> stb::UExpr {
		self.into_terms()
			.map(|mut term| {
				for app in term.apps.clone() {
					chase(&app, &mut term, env);
				}
				let mut equiv = term.extract_equiv();
				merge_keys(&mut term, &mut equiv, env);
				let (ref new_env, scopes) = merge_scopes(&term.scopes, env, &mut equiv);
				term.preds.retain(|pred| !matches!(pred, Predicate::Eq(_, _)));
				for (expr, root) in equiv.into_pairs() {
					term.preds.push_back(Predicate::Eq(root, expr));
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
				stb::Term { preds, squash, not, apps, scopes }
			})
			.collect()
	}
}

fn chase(app: &Application, term: &mut nom::Term, env: &Env<Entry>) {
	let schema = env.get(app.table).sch();
	for (&col, &tab) in &schema.foreign {
		let dest_schema = env.get(tab).sch();
		let primary_col = dest_schema.primary.unwrap();
		let types = vec![DataType::Any; dest_schema.types.len()];
		let level = env.size() + term.scopes.len();
		let vars: Vector<_> = (0..dest_schema.types.len()).map(|i| VL(level + i)).collect();
		term.preds.push_back(Predicate::Eq(Expr::Var(app.args[col], env.get(app.args[col]).ty()), Expr::Var(vars[primary_col], env.get(vars[primary_col]).ty())));
		let new_app = Application::new(tab, vars);
		term.apps.push_back(new_app.clone());
		term.scopes.extend(types);
		chase(&new_app, term, env);
	}
}

fn merge_keys(term: &mut nom::Term, equiv: &mut EquivClass, env: &Env<Entry>) {
	let (mut term_apps, mut squashed) = (vector![], vector![]);
	for (t, apps) in term.apps.iter().cloned().into_group_map_by(|a| a.table) {
		if let Some(col) = env.get(t).sch().primary {
			use shared::Expr::Var;
			squashed.extend(apps.clone());
			let groups = apps
				.into_iter()
				.filter_map(|app| equiv.get(&Var(app.args[col], env.get(app.args[col]).ty())).map(|root| (root, app.args)))
				.into_group_map();
			for (_, vars) in groups {
				let mut vars = vars.into_iter();
				let args = vars.next().unwrap();
				vars.flat_map(|v| v.into_iter().zip(args.clone()))
					.for_each(|(v1, v2)| equiv.equate(Var(v1, env.get(v1).ty()), Var(v2, env.get(v2).ty())));
			}
		} else {
			term_apps.extend(apps);
		}
	}
	term.apps = term_apps;
	if let Some(sq) = &mut term.squash {
		sq.0.iter_mut().for_each(|term| term.apps.extend(squashed.clone()));
	}
}

fn merge_scopes(
	scopes: &Vector<DataType>,
	env: &Env<Entry>,
	equiv: &mut EquivClass,
) -> (Env<Entry>, Vector<DataType>) {
	let mut new_scopes = vector![];
	let mut mapping = HashMap::new();
	let level = env.size();
	let mut env = env.clone();
	let mut free = env.level;
	for (i, ty) in scopes.iter().enumerate() {
		let var = Expr::Var(VL(level + i), ty.clone());
		let entry = if let Some(Expr::Var(v, root_ty)) = equiv.get(&var) {
			assert_eq!(ty.clone(), root_ty);
			if v.0 >= level {
				mapping
					.entry(v)
					.or_insert_with(|| {
						new_scopes.push_back(ty.clone());
						let entry = Entry::Value(VL(free), ty.clone());
						free += 1;
						entry
					})
					.clone()
			} else {
				Entry::Value(env.get_var(v), ty.clone())
			}
		} else {
			new_scopes.push_back(ty.clone());
			let entry = Entry::Value(VL(free), ty.clone());
			free += 1;
			entry
		};
		env.introduce(entry);
	}
	env.level = free;
	(env, new_scopes)
}

pub fn evaluate(rel: syn::Relation, env: &Env<Entry>) -> stb::Relation {
	log::info!("Syntax:\n{}", rel);
	let prt: prt::Relation = rel.eval(env);
	let nom = prt.eval(env);
	log::info!("Normal:\n{}", nom);
	let stb = nom.eval(env);
	log::info!("Stable:\n{}", stb);
	stb
}
