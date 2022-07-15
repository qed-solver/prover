use std::iter::once;
use std::ops::{Mul, Not};

use imbl::{vector, Vector};
use itertools::{Either, Itertools};
use serde::{Deserialize, Serialize};

use crate::pipeline::shared::{Constraint, DataType, Eval, Schema, VL};
use crate::pipeline::syntax::{Logic, UExpr};
use crate::pipeline::{shared, syntax};
use crate::solver::Payload;

#[derive(Serialize, Deserialize)]
pub struct Input {
	schemas: Vec<Schema>,
	queries: (Relation, Relation),
	help: (String, String),
}

impl From<Input> for Payload {
	fn from(input: Input) -> Self {
		let Input { schemas, queries: (r1, r2), help } = input;
		let subst = vector![];
		let env = Env(&schemas, &subst, 0);
		log::info!("Schemas:\n{:?}", schemas);
		log::info!("Input:\n{}\n{}", help.0, help.1);
		Payload(schemas.clone(), env.eval(r1), env.eval(r2))
	}
}

#[derive(Copy, Clone)]
struct Env<'e>(&'e [Schema], &'e Vector<syntax::Expr>, usize);

fn vars(level: usize, types: Vector<DataType>) -> Vector<syntax::Expr> {
	types.into_iter().enumerate().map(|(i, ty)| syntax::Expr::Var(VL(level + i), ty)).collect()
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Relation {
	Singleton,
	Scan(VL),
	Filter {
		condition: Expr,
		source: Box<Relation>,
	},
	Project {
		#[serde(alias = "target")]
		columns: Vec<Expr>,
		source: Box<Relation>,
	},
	Join {
		condition: Expr,
		left: Box<Relation>,
		right: Box<Relation>,
		kind: JoinKind,
	},
	Correlate(Box<Relation>, Box<Relation>),
	Union(Box<Relation>, Box<Relation>),
	Except(Box<Relation>, Box<Relation>),
	Distinct(Box<Relation>),
	Values {
		schema: Vec<DataType>,
		content: Vec<Vec<Expr>>,
	},
	Aggregate {
		#[serde(alias = "function")]
		columns: Vec<Expr>,
		source: Box<Relation>,
	},
	Sort {
		collation: Vec<(usize, DataType, String)>,
		offset: Option<Expr>,
		limit: Option<Expr>,
		source: Box<Relation>,
	},
}

impl Relation {
	fn scope(&self, schemas: &[Schema]) -> Vector<DataType> {
		use Relation::*;
		match self {
			Singleton => Vector::new(),
			Scan(table) => schemas[table.0].types.clone().into(),
			Filter { source, .. } => source.scope(schemas),
			Project { columns, .. } | Aggregate { columns, .. } => {
				columns.iter().map(|expr| expr.ty()).collect()
			},
			Join { left, kind: JoinKind::Semi | JoinKind::Anti, .. } => left.scope(schemas),
			Join { left, right, .. } | Correlate(left, right) => {
				left.scope(schemas) + right.scope(schemas)
			},
			Union(rel1, _) | Except(rel1, _) => rel1.scope(schemas),
			Distinct(rel) => rel.scope(schemas),
			Values { schema, .. } => schema.clone().into(),
			Sort { source, .. } => source.scope(schemas),
		}
	}
}

impl Eval<Relation, syntax::Relation> for Env<'_> {
	fn eval(self, source: Relation) -> syntax::Relation {
		use syntax::Relation as Rel;
		use syntax::UExpr::*;
		use Relation::*;
		let Env(schemas, subst, lvl) = self;
		let scopes = source.scope(schemas);
		match source {
			Singleton => Rel::lam(vector![], UExpr::one()),
			Scan(VL(t)) => {
				let vars = vars(lvl, scopes.clone());
				let schema = &schemas[t];
				let conds = schema
					.guaranteed
					.iter()
					.map(|cond| Pred(Env(schemas, &vars, lvl + scopes.len()).eval(cond.clone())));
				let constraints =
					schema.constraints.iter().zip(vars.clone()).map(|(constr, v)| match constr {
						Constraint::NotNullable => Pred(!Logic::is_null(v)),
						_ => UExpr::one(),
					});
				let app = if schema.primary.is_empty() {
					App(Rel::Var(VL(t)), vars.clone())
				} else {
					let key_constraints =
						schema.primary.iter().enumerate().flat_map(|(j, cols)| {
							use shared::Expr::*;
							let (keys, args): (Vec<_>, Vec<_>) =
								vars.iter().cloned().enumerate().partition_map(|(i, v)| {
									if cols.contains(&i) {
										Either::Left(v)
									} else {
										Either::Right(v)
									}
								});
							let pk = Logic::Pred(format!("rpk!{}-{}", t, j), keys.clone());
							let pa = args.into_iter().enumerate().map(move |(i, arg)| {
								let f =
									Op(format!("rpn!{}-{}-{}", t, i, j), keys.clone(), arg.ty());
								Logic::Eq(arg, f)
							});
							pa.chain(once(pk))
						});
					Pred(Logic::And(key_constraints.collect()))
				};
				Rel::lam(scopes.clone(), app * Mul(constraints.collect()) * Mul(conds.collect()))
			},
			// Filter R(x, y) by P[x, y]
			// λ x, y. [P[x, y]] × R(x, y)
			Filter { condition, source } => {
				let vars = vars(lvl, scopes.clone());
				let body_lvl = lvl + scopes.len();
				let cond_subst = subst + &vars;
				let condition = UExpr::Pred(Env(schemas, &cond_subst, body_lvl).eval(condition));
				let source = Env(schemas, subst, body_lvl).eval(*source);
				Rel::lam(scopes, condition * UExpr::App(source, vars))
			},
			// Project f[x, y] from R(x, y)
			// λ a. ∑ x, y. [a = f[x, y]] × R(x, y)
			Project { columns, source } => {
				let proj_vars = vars(lvl, scopes.clone());
				let inner_scopes = source.scope(schemas);
				let inner_vars = vars(lvl + scopes.len(), inner_scopes.clone());
				let inner_lvl = lvl + scopes.len() + inner_scopes.len();
				let source = Env(schemas, subst, inner_lvl).eval(*source);
				let cols_subst = subst + &inner_vars;
				let cols_env = Env(schemas, &(cols_subst), inner_lvl);
				let body = proj_vars
					.into_iter()
					.zip(columns)
					.map(|(var, col)| Pred(Logic::Eq(var, cols_env.eval(col))))
					.fold(UExpr::App(source, inner_vars), UExpr::mul);
				Rel::lam(scopes, UExpr::sum(inner_scopes, body))
			},
			// R(x) semi join S(y) on P[x, y]
			// λ x. R(x) × ‖∑ y. [P[x, y]] × S(y)‖
			Join { condition, left, right, kind: kind @ (JoinKind::Semi | JoinKind::Anti) } => {
				let left_vars = vars(lvl, scopes.clone());
				let body_lvl = lvl + scopes.len();
				let inner_scopes = right.scope(schemas);
				let inner_lvl = body_lvl + inner_scopes.len();
				let right_vars = vars(body_lvl, inner_scopes.clone());
				let cond_subst = subst + &(&left_vars + &right_vars);
				let cond = Pred(Env(schemas, &cond_subst, inner_lvl).eval(condition));
				let right_body = App(Env(schemas, subst, inner_lvl).eval(*right), right_vars);
				let left_body = App(Env(schemas, subst, body_lvl).eval(*left), left_vars);
				let wrapper = match kind {
					JoinKind::Semi => UExpr::squash,
					JoinKind::Anti => UExpr::not,
					_ => unreachable!(),
				};
				Rel::lam(scopes, left_body * wrapper(UExpr::sum(inner_scopes, cond * right_body)))
			},
			// R(x) inner join S(y) on P[x, y]
			// λ x, y. [P[x, y]] × R(x) × S(y)
			// R(x) full join S(y) on P[x, y]
			// λ x, y. [P[x, y]] × R(x) × S(y)
			//        + ¬(∑ x'. P[x', y] × R(x')) × Null(x) × S(y)
			//        + ¬(∑ y'. P[x, y'] × S(y')) × Null(y) × R(x)
			Join { condition, left, right, kind } => {
				let left_scopes = left.scope(schemas);
				let right_scopes = right.scope(schemas);
				let right_vars = &vars(lvl + left_scopes.len(), right_scopes);
				let left_vars = &vars(lvl, left_scopes);
				let body_lvl = lvl + scopes.len();
				let body_env = Env(schemas, subst, body_lvl);
				let left_body = UExpr::App(body_env.eval(*left.clone()), left_vars.clone());
				let right_body = UExpr::App(body_env.eval(*right.clone()), right_vars.clone());
				let cond_subst = subst + &(left_vars + right_vars);
				let cond_env = Env(schemas, &cond_subst, body_lvl);
				let matching = UExpr::Pred(cond_env.eval(condition.clone()))
					* left_body.clone() * right_body.clone();
				let miss = |miss_left| {
					let missing = *if miss_left { left.clone() } else { right.clone() };
					let inner_scopes = missing.scope(schemas);
					let inner_vars = vars(body_lvl, inner_scopes.clone());
					let inner_lvl = body_lvl + inner_scopes.len();
					let inner_cond_vars =
						if miss_left { &inner_vars + right_vars } else { left_vars + &inner_vars };
					let inner_cond_subst = subst + &inner_cond_vars;
					let inner_cond = UExpr::Pred(
						Env(schemas, &inner_cond_subst, inner_lvl).eval(condition.clone()),
					);
					let missing = Env(schemas, subst, inner_lvl).eval(missing);
					let inner_body = inner_cond * UExpr::App(missing, inner_vars);
					let other_body = if miss_left { right_body.clone() } else { left_body.clone() };
					if miss_left { left_vars } else { right_vars }
						.iter()
						.map(|v| UExpr::Pred(Logic::is_null(v.clone())))
						.fold(other_body * !UExpr::sum(inner_scopes, inner_body), UExpr::mul)
				};
				match kind {
					JoinKind::Inner => Rel::lam(scopes, matching),
					JoinKind::Left => Rel::lam(scopes, matching + miss(false)),
					JoinKind::Right => Rel::lam(scopes, matching + miss(true)),
					JoinKind::Full => Rel::lam(scopes, matching + miss(true) + miss(false)),
					_ => unreachable!(),
				}
			},
			// R(x) correlate join S[x](y)
			// λx, y. R(x) × S[x](y)
			Correlate(left, right) => {
				let left_scopes = left.scope(schemas);
				let right_scopes = right.scope(schemas);
				let right_vars = vars(lvl + left_scopes.len(), right_scopes);
				let left_vars = vars(lvl, left_scopes);
				let body_lvl = lvl + scopes.len();
				let left = Env(schemas, subst, body_lvl).eval(*left);
				let right_subst = subst + &left_vars;
				let right = Env(schemas, &right_subst, body_lvl).eval(*right);
				Rel::lam(scopes, UExpr::App(left, left_vars) * UExpr::App(right, right_vars))
			},
			// R(x) union S(y)
			// λx. R(x) + S(x)
			Union(left, right) => {
				let body_lvl = lvl + scopes.len();
				let vars = vars(lvl, scopes.clone());
				let left = Env(schemas, subst, body_lvl).eval(*left);
				let right = Env(schemas, subst, body_lvl).eval(*right);
				Rel::lam(scopes, UExpr::App(left, vars.clone()) + UExpr::App(right, vars))
			},
			// R(x) except S(y)
			// λx. R(x) × ¬S(x)
			Except(left, right) => {
				let body_lvl = lvl + scopes.len();
				let vars = vars(lvl, scopes.clone());
				let left = Env(schemas, subst, body_lvl).eval(*left);
				let right = Env(schemas, subst, body_lvl).eval(*right);
				Rel::lam(scopes, UExpr::App(left, vars.clone()) * !UExpr::App(right, vars))
			},
			// Distinct R(x)
			// λx. ‖R(x)‖
			Distinct(source) => {
				let source = Env(schemas, subst, lvl + scopes.len()).eval(*source);
				Rel::lam(scopes.clone(), UExpr::squash(UExpr::App(source, vars(lvl, scopes))))
			},
			// Values ((a1, b1), (a2, b2), (a3, b3))
			// λx, y. [x = a1] × [y = b1] + [x = a2] × [y = b2] + [x = a3] × [y = b3]
			Values { schema, content } => {
				let vars = vars(lvl, scopes.clone());
				let env = Env(schemas, subst, lvl + scopes.len());
				let rows = content.into_iter().map(|row| {
					let cols =
						vars.iter().zip(row).map(|(v, e)| Pred(Logic::Eq(v.clone(), env.eval(e))));
					UExpr::Mul(cols.collect())
				});
				Rel::lam(scopes, UExpr::Add(rows.collect()))
			},
			// Agg1(f[x, y]), Agg2(g[x, y]) on R(x, y)
			// λa, b. [a = Agg1(λc. ∑x, y. [c = f[x, y]] × R(x, y))]
			//        × [b = Agg2(λc. ∑x, y. [c = g[x, y]] × R(x, y))]
			Aggregate { columns, source } => {
				let vars = vars(lvl, scopes.clone());
				let env = Env(schemas, subst, lvl + scopes.len());
				let cols = vars
					.into_iter()
					.zip(columns)
					.map(|(v, agg)| Pred(Logic::Eq(v, agg.eval_agg(&source, env))));
				Rel::lam(scopes, Mul(cols.collect()))
			},
			Sort { mut collation, offset, limit, source } => {
				// TODO: Better way to handle multiple sort columns.
				if let Some((col, _, ord)) = collation.pop() {
					let col = col.into();
					let ord = ord.into();
					Rel::HOp(
						"sort".to_string(),
						vec![col, ord],
						self.eval(Sort { collation, offset, limit, source }.into()),
					)
				} else {
					let source = self.eval(source);
					let offset = offset.map(|n| self.eval(n)).unwrap_or(0u32.into());
					if let Some(count) = limit {
						Rel::HOp("limit".to_string(), vec![self.eval(count), offset], source)
					} else {
						Rel::HOp("offset".to_string(), vec![offset], source)
					}
				}
			},
		}
	}
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "UPPERCASE")]
pub enum JoinKind {
	Inner,
	Left,
	Right,
	Full,
	Semi,
	Anti,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[serde(untagged)]
pub enum Expr {
	Col {
		column: VL,
		#[serde(alias = "type")]
		ty: DataType,
	},
	HOp {
		#[serde(rename = "operator")]
		op: String,
		#[serde(rename = "operand")]
		args: Vec<Expr>,
		#[serde(rename = "query")]
		rel: Box<Relation>,
		#[serde(alias = "type")]
		ty: DataType,
	},
	Op {
		#[serde(rename = "operator")]
		op: String,
		#[serde(rename = "operand")]
		args: Vec<Expr>,
		#[serde(alias = "type")]
		ty: DataType,
	},
}

impl Expr {
	fn ty(&self) -> DataType {
		match self {
			Expr::Col { ty, .. } => ty,
			Expr::Op { ty, .. } => ty,
			Expr::HOp { ty, .. } => ty,
		}
		.clone()
	}

	fn eval_agg(self, source: &Relation, env: Env) -> syntax::Expr {
		use shared::Expr::*;
		if let Expr::Op { op, args, ty } = self {
			let source = match op.as_str() {
				"COUNT" if args.is_empty() => source.clone(),
				_ => Relation::Project { columns: args, source: Box::new(source.clone()) },
			};
			HOp(op, vec![], Box::new(env.eval(source)), ty)
		} else {
			panic!()
		}
	}
}

impl Eval<Expr, syntax::Expr> for Env<'_> {
	fn eval(self, source: Expr) -> syntax::Expr {
		use shared::Expr::*;
		match source {
			Expr::Col { column, ty } => self.1[column.0].clone(),
			Expr::Op { op, args, ty } if op == "CAST" && args.len() == 1 => {
				let args: Vec<syntax::Expr> = self.eval(args);
				if args[0].ty() == ty {
					args[0].clone()
				} else {
					Op(op, args, ty)
				}
			},
			Expr::Op { op, args, ty } => Op(op, self.eval(args), ty),
			Expr::HOp { op, args, rel, ty } => HOp(op, self.eval(args), self.eval(rel), ty),
		}
	}
}

impl Eval<Expr, Logic> for Env<'_> {
	fn eval(self, source: Expr) -> Logic {
		match source.clone() {
			Expr::Op { op, args, ty: DataType::Boolean } => match op.to_uppercase().as_str() {
				"TRUE" => Logic::tt(),
				"FALSE" => Logic::ff(),
				"=" => Logic::Eq(self.eval(args[0].clone()), self.eval(args[1].clone())),
				"<>" => !Logic::Eq(self.eval(args[0].clone()), self.eval(args[1].clone())),
				"AND" => Logic::And(args.into_iter().map(|arg| self.eval(arg)).collect()),
				"OR" => Logic::Or(args.into_iter().map(|arg| self.eval(arg)).collect()),
				"NOT" => Logic::not(self.eval(args[0].clone())),
				"IS NULL" => Logic::is_null(self.eval(args[0].clone())),
				"IS NOT NULL" => !Logic::is_null(self.eval(args[0].clone())),
				_ => Logic::Bool(self.eval(source)),
			},
			Expr::Col { ty: DataType::Boolean, .. } => Logic::Bool(self.eval(source)),
			Expr::HOp { op, args, rel, ty: DataType::Boolean } => match op.as_str() {
				"IN" => Logic::App(syntax::Application(self.eval(*rel), self.eval(args).into())),
				"EXISTS" => Logic::Exists(self.eval(*rel)),
				_ => Logic::Bool(self.eval(source)),
			},
			_ => panic!("wrong type for predicate"),
		}
	}
}
