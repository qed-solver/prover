use std::iter::once;
use std::ops::{Mul, Not};

use imbl::{vector, Vector};
use itertools::{Either, Itertools};
use serde::{Deserialize, Serialize};

use super::syntax::Aggr;
use crate::pipeline::shared::{DataType, Eval, Head, Lambda, Neutral, Schema, Typed, VL};
use crate::pipeline::syntax::{Logic, UExpr};
use crate::pipeline::{shared, syntax};

#[derive(Copy, Clone)]
pub struct Env<'e>(pub &'e [Schema], pub &'e Vector<syntax::Expr>, pub usize);

fn vars(level: usize, types: Vector<DataType>) -> Vector<syntax::Expr> {
	types.into_iter().enumerate().map(|(i, ty)| syntax::Expr::Var(VL(level + i), ty)).collect()
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
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
	Union(Vec<Relation>),
	Intersect(Vec<Relation>),
	Except(Box<Relation>, Box<Relation>),
	Distinct(Box<Relation>),
	Values {
		schema: Vec<DataType>,
		content: Vec<Vec<Expr>>,
	},
	Aggregate {
		#[serde(alias = "function")]
		columns: Vec<AggCall>,
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
			Project { columns, .. } => columns.iter().map(|expr| expr.ty()).collect(),
			Aggregate { columns, .. } => columns.iter().map(|agg| agg.ty.clone()).collect(),
			Join { left, kind: JoinKind::Semi | JoinKind::Anti, .. } => left.scope(schemas),
			Join { left, right, .. } | Correlate(left, right) => {
				left.scope(schemas) + right.scope(schemas)
			},
			Union(rels) | Intersect(rels) => rels[0].scope(schemas),
			Except(rel1, _) => rel1.scope(schemas),
			Distinct(rel) => rel.scope(schemas),
			Values { schema, .. } => schema.clone().into(),
			Sort { source, .. } => source.scope(schemas),
		}
	}
}

impl Eval<Relation, syntax::Relation> for Env<'_> {
	fn eval(self, source: Relation) -> syntax::Relation {
		use syntax::UExpr::*;
		use Relation::*;
		let Env(schemas, subst, lvl) = self;
		let scope = source.scope(schemas);
		match source {
			Singleton => Lambda(vector![], UExpr::one()),
			Scan(VL(t)) => {
				let vars = vars(lvl, scope.clone());
				let schema = &schemas[t];
				let conds = schema.guaranteed.iter().map(|cond| {
					UExpr::pred(Env(schemas, &vars, lvl + scope.len()).eval(cond.clone()))
				});
				let constraints =
					schema.nullabilities.iter().zip(vars.clone()).map(|(nullable, v)| {
						if !*nullable {
							UExpr::pred(!v.is_null())
						} else {
							UExpr::one()
						}
					});
				let app = if schema.primary.is_empty() {
					let app = UExpr::Neu(Neutral(Head::Var(VL(t)), vars.clone()));
					app.clone() * UExpr::squash(app)
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
					UExpr::pred(Logic::And(key_constraints.collect()))
				};
				Lambda(scope.clone(), app * Mul(constraints.collect()) * Mul(conds.collect()))
			},
			// Filter R(x, y) by P[x, y]
			// λ x, y. [P[x, y]] × R(x, y)
			Filter { condition, source } => {
				let vars = vars(lvl, scope.clone());
				let body_lvl = lvl + scope.len();
				let cond_subst = subst + &vars;
				let condition = UExpr::pred(Env(schemas, &cond_subst, body_lvl).eval(condition));
				let source = Env(schemas, subst, body_lvl).eval(*source);
				Lambda(scope, condition * UExpr::app(source, vars))
			},
			// Project f[x, y] from R(x, y)
			// λ a. ∑ x, y. [a = f[x, y]] × R(x, y)
			Project { columns, source } => {
				let proj_vars = vars(lvl, scope.clone());
				let inner_scope = source.scope(schemas);
				let inner_vars = vars(lvl + scope.len(), inner_scope.clone());
				let inner_lvl = lvl + scope.len() + inner_scope.len();
				let source = Env(schemas, subst, inner_lvl).eval(*source);
				let cols_subst = subst + &inner_vars;
				let cols_env = Env(schemas, &(cols_subst), inner_lvl);
				let body = proj_vars
					.into_iter()
					.zip(columns)
					.map(|(var, col)| UExpr::pred(Logic::Eq(var, cols_env.eval(col))))
					.fold(UExpr::app(source, inner_vars), UExpr::mul);
				Lambda(scope, UExpr::sum(inner_scope, body))
			},
			// R(x) semi join S(y) on P[x, y]
			// λ x. R(x) × ‖∑ y. [P[x, y]] × S(y)‖
			Join { condition, left, right, kind: kind @ (JoinKind::Semi | JoinKind::Anti) } => {
				let left_vars = vars(lvl, scope.clone());
				let body_lvl = lvl + scope.len();
				let inner_scope = right.scope(schemas);
				let inner_lvl = body_lvl + inner_scope.len();
				let right_vars = vars(body_lvl, inner_scope.clone());
				let cond_subst = subst + &(&left_vars + &right_vars);
				let cond = UExpr::pred(Env(schemas, &cond_subst, inner_lvl).eval(condition));
				let right_body =
					UExpr::app(Env(schemas, subst, inner_lvl).eval(*right), right_vars);
				let left_body = UExpr::app(Env(schemas, subst, body_lvl).eval(*left), left_vars);
				let wrapper = match kind {
					JoinKind::Semi => UExpr::squash,
					JoinKind::Anti => UExpr::not,
					_ => unreachable!(),
				};
				Lambda(scope, left_body * wrapper(UExpr::sum(inner_scope, cond * right_body)))
			},
			// R(x) inner join S(y) on P[x, y]
			// λ x, y. [P[x, y]] × R(x) × S(y)
			// R(x) full join S(y) on P[x, y]
			// λ x, y. [P[x, y]] × R(x) × S(y)
			//        + ¬(∑ x'. P[x', y] × R(x')) × Null(x) × S(y)
			//        + ¬(∑ y'. P[x, y'] × S(y')) × Null(y) × R(x)
			Join { condition, left, right, kind } => {
				let left_scope = left.scope(schemas);
				let right_scope = right.scope(schemas);
				let right_vars = &vars(lvl + left_scope.len(), right_scope);
				let left_vars = &vars(lvl, left_scope);
				let body_lvl = lvl + scope.len();
				let body_env = Env(schemas, subst, body_lvl);
				let left_body = UExpr::app(body_env.eval(*left.clone()), left_vars.clone());
				let right_body = UExpr::app(body_env.eval(*right.clone()), right_vars.clone());
				let cond_subst = subst + &(left_vars + right_vars);
				let cond_env = Env(schemas, &cond_subst, body_lvl);
				let matching = UExpr::pred(cond_env.eval(condition.clone()))
					* left_body.clone() * right_body.clone();
				let miss = |miss_left| {
					let missing = *if miss_left { left.clone() } else { right.clone() };
					let inner_scope = missing.scope(schemas);
					let inner_vars = vars(body_lvl, inner_scope.clone());
					let inner_lvl = body_lvl + inner_scope.len();
					let inner_cond_vars =
						if miss_left { &inner_vars + right_vars } else { left_vars + &inner_vars };
					let inner_cond_subst = subst + &inner_cond_vars;
					let inner_cond = UExpr::pred(
						Env(schemas, &inner_cond_subst, inner_lvl).eval(condition.clone()),
					);
					let missing = Env(schemas, subst, inner_lvl).eval(missing);
					let inner_body = inner_cond * UExpr::app(missing, inner_vars);
					let other_body = if miss_left { right_body.clone() } else { left_body.clone() };
					if miss_left { left_vars } else { right_vars }
						.iter()
						.map(|v| UExpr::pred(v.clone().is_null()))
						.fold(other_body * !UExpr::sum(inner_scope, inner_body), UExpr::mul)
				};
				match kind {
					JoinKind::Inner => Lambda(scope, matching),
					JoinKind::Left => Lambda(scope, matching + miss(false)),
					JoinKind::Right => Lambda(scope, matching + miss(true)),
					JoinKind::Full => Lambda(scope, matching + miss(true) + miss(false)),
					_ => unreachable!(),
				}
			},
			// R(x) correlated join S[x](y)
			// λx, y. R(x) × S[x](y)
			Correlate(left, right) => {
				let left_scope = left.scope(schemas);
				let right_scope = right.scope(schemas);
				let right_vars = vars(lvl + left_scope.len(), right_scope);
				let left_vars = vars(lvl, left_scope);
				let body_lvl = lvl + scope.len();
				let left = Env(schemas, subst, body_lvl).eval(*left);
				let right_subst = subst + &left_vars;
				let right = Env(schemas, &right_subst, body_lvl).eval(*right);
				Lambda(scope, UExpr::app(left, left_vars) * UExpr::app(right, right_vars))
			},
			// R(x) union all S(y)
			// λx. R(x) + S(x)
			Union(sources) => {
				let body_lvl = lvl + scope.len();
				let vars = vars(lvl, scope.clone());
				let sum = sources
					.into_iter()
					.map(|source| {
						UExpr::app(Env(schemas, subst, body_lvl).eval(source), vars.clone())
					})
					.collect();
				Lambda(scope, Add(sum))
			},
			// R(x) intersect S(y)
			// λx. ‖R(x) × S(x)‖
			Intersect(sources) => {
				let body_lvl = lvl + scope.len();
				let vars = vars(lvl, scope.clone());
				let prod = sources
					.into_iter()
					.map(|source| {
						UExpr::app(Env(schemas, subst, body_lvl).eval(source), vars.clone())
					})
					.collect();
				Lambda(scope, UExpr::squash(Mul(prod)))
			},
			// R(x) except S(y)
			// λx. ‖R(x) × ¬S(x)‖
			Except(left, right) => {
				let body_lvl = lvl + scope.len();
				let vars = vars(lvl, scope.clone());
				let left = Env(schemas, subst, body_lvl).eval(*left);
				let right = Env(schemas, subst, body_lvl).eval(*right);
				Lambda(
					scope,
					UExpr::squash(UExpr::app(left, vars.clone()) * !UExpr::app(right, vars)),
				)
			},
			// Distinct R(x)
			// λx. ‖R(x)‖
			Distinct(source) => {
				let source = Env(schemas, subst, lvl + scope.len()).eval(*source);
				Lambda(scope.clone(), UExpr::squash(UExpr::app(source, vars(lvl, scope))))
			},
			// Values ((a1, b1), (a2, b2), (a3, b3))
			// λx, y. [x = a1] × [y = b1] + [x = a2] × [y = b2] + [x = a3] × [y = b3]
			Values { schema: _, content } => {
				let vars = vars(lvl, scope.clone());
				let env = Env(schemas, subst, lvl + scope.len());
				let rows = content.into_iter().map(|row| {
					let cols = vars
						.iter()
						.zip(row)
						.map(|(v, e)| UExpr::pred(Logic::Eq(v.clone(), env.eval(e))));
					Mul(cols.collect())
				});
				Lambda(scope, Add(rows.collect()))
			},
			// Agg1(f[x, y]), Agg2(g[x, y]) on R(x, y)
			// λa, b. [a = Agg1(λc. ∑x, y. [c = f[x, y]] × R(x, y))]
			//        × [b = Agg2(λc. ∑x, y. [c = g[x, y]] × R(x, y))]
			Aggregate { columns, source } => {
				let vars = vars(lvl, scope.clone());
				let env = Env(schemas, subst, lvl + scope.len());
				let cols = vars
					.into_iter()
					.zip(columns)
					.map(|(v, agg)| UExpr::pred(Logic::Eq(v, env.eval((agg, *source.clone())))));
				Lambda(scope, Mul(cols.collect()))
			},
			Sort { mut collation, offset, limit, source } => {
				// TODO: Better way to handle multiple sort columns.
				let vars = vars(lvl, scope.clone());
				let env = Env(schemas, subst, lvl + scope.len());
				let head = if let Some((col, _, ord)) = collation.pop() {
					let body = env.eval(Sort { collation, offset, limit, source }.into());
					Head::HOp("sort".to_string(), vec![col.into(), ord.into()], body)
				} else {
					let source = env.eval(source);
					let offset = offset.map(|n| env.eval(n)).unwrap_or(0u32.into());
					if let Some(count) = limit {
						Head::HOp("limit".to_string(), vec![env.eval(count), offset], source)
					} else {
						Head::HOp("offset".to_string(), vec![offset], source)
					}
				};
				Lambda(scope, Neu(Neutral(head, vars)))
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
#[serde(rename_all = "camelCase")]
pub struct AggCall {
	#[serde(rename = "operator")]
	op: String,
	#[serde(rename = "operand")]
	args: Vec<Expr>,
	#[serde(default = "default_distinct")]
	distinct: bool,
	#[serde(default = "default_ignore_nulls")]
	ignore_nulls: bool,
	#[serde(alias = "type")]
	ty: DataType,
}

fn default_distinct() -> bool {
	false
}

fn default_ignore_nulls() -> bool {
	true
}

impl Eval<(AggCall, Relation), syntax::Expr> for Env<'_> {
	fn eval(self, (agg, rel): (AggCall, Relation)) -> syntax::Expr {
		let tys = agg.args.iter().map(|arg| arg.ty()).collect_vec();
		let args = agg.args;
		let source = match agg.op.as_str() {
			"COUNT" if args.is_empty() => rel,
			_ => Relation::Project { columns: args, source: rel.into() },
		};
		let source = if agg.distinct { Relation::Distinct(source.into()) } else { source };
		let source = if agg.ignore_nulls {
			let conditions = tys
				.into_iter()
				.enumerate()
				.map(|(i, ty)| Expr::Op {
					op: "IS NOT NULL".into(),
					args: vec![Expr::Col { column: VL(i), ty }],
					ty: DataType::Boolean,
				})
				.collect_vec();
			let condition = Expr::Op { op: "AND".into(), args: conditions, ty: DataType::Boolean };
			Relation::Filter { condition, source: source.into() }
		} else {
			source
		};
		let Env(_, _, lvl) = self;
		let Lambda(scope, body) = self.eval(source);
		// TODO: Handle various agg calls.
		match agg.op.as_str() {
			"COUNT" => syntax::Expr::Agg(Aggr(agg.op, scope, body, Box::new(1u32.into()))),
			_ if scope.len() == 1 => {
				let var = vars(lvl, scope.clone())[0].clone();
				syntax::Expr::Agg(Aggr(agg.op, scope, body, var.into()))
			},
			_ => syntax::Expr::HOp(agg.op, vec![], Lambda(scope, body).into(), agg.ty),
		}
	}
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
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

	fn into_real(self) -> Expr {
		if self.ty() == DataType::Real {
			self
		} else {
			Expr::Op { op: "CAST".to_string(), args: vec![self], ty: DataType::Real }
		}
	}
}

impl Eval<Expr, syntax::Expr> for Env<'_> {
	fn eval(self, source: Expr) -> syntax::Expr {
		use shared::Expr::*;
		self.eval_logic(&source).map(|l| Log(l.into())).unwrap_or_else(|| {
			match source {
				Expr::Col { column, ty: _ } => self.1[column.0].clone(),
				Expr::Op { op, args, ty } => {
					let cast = matches!(op.as_str(), "+" | "-" | "*" | "/" if ty == DataType::Real)
						|| matches!(op.as_str(), ">" | "<" | ">=" | "<=" | "=" | "<>" | "!=" if args.iter().any(|e| e.ty() == DataType::Real));
					let args =
						if cast { args.into_iter().map(Expr::into_real).collect() } else { args };
					Op(op, self.eval(args), ty)
				},
				Expr::HOp { op, args, rel, ty } => HOp(op, self.eval(args), self.eval(*rel).into(), ty),
			}
		})
	}
}

impl Env<'_> {
	fn eval_logic(self, source: &Expr) -> Option<Logic> {
		match source {
			Expr::Op { op, args, ty: DataType::Boolean } => match op.to_uppercase().as_str() {
				"TRUE" => Some(Logic::tt()),
				"FALSE" => Some(Logic::ff()),
				"<=>" | "IS NOT DISTINCT FROM" => {
					Some(Logic::Eq(self.eval(args[0].clone()), self.eval(args[1].clone())))
				},
				"IS DISTINCT FROM" => {
					Some(!Logic::Eq(self.eval(args[0].clone()), self.eval(args[1].clone())))
				},
				"IS NULL" => {
					let e: syntax::Expr = self.eval(args[0].clone());
					Some(e.is_null())
				},
				"IS NOT NULL" => {
					let e: syntax::Expr = self.eval(args[0].clone());
					Some(!e.is_null())
				},
				_ => None,
			},
			Expr::HOp { op, args: _, rel, ty: DataType::Boolean } => match op.as_str() {
				"EXISTS" => {
					let Env(schemas, subst, lvl) = self;
					let scope = rel.scope(schemas);
					let rel = Env(schemas, subst, lvl + scope.len()).eval(*rel.clone());
					let vars = vars(lvl, scope.clone());
					Some(Logic::squash(UExpr::sum(scope, UExpr::app(rel, vars))))
				},
				_ => None,
			},
			_ => None,
		}
	}
}

impl Eval<Expr, Logic> for Env<'_> {
	fn eval(self, source: Expr) -> Logic {
		assert_eq!(source.ty(), DataType::Boolean, "wrong type for predicate");
		self.eval_logic(&source).unwrap_or_else(|| match source.clone() {
			Expr::Op { op, args, .. } => match op.to_uppercase().as_str() {
				"AND" => Logic::And(args.into_iter().map(|arg| self.eval(arg)).collect()),
				"OR" => Logic::Or(args.into_iter().map(|arg| self.eval(arg)).collect()),
				_ => Logic::Bool(self.eval(source)),
			},
			Expr::Col { .. } | Expr::HOp { .. } => Logic::Bool(self.eval(source)),
		})
	}
}
