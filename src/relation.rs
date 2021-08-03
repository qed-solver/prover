use std::ops::{Add, Mul, Range};

use serde::{Deserialize, Serialize};

use crate::evaluate::shared::{DataType, Entry, Env, Schema, VL};
use crate::evaluate::syntax::UExpr;
use crate::evaluate::{shared, syntax};
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
		let env = Env::new(
			schemas.clone().into_iter().enumerate().map(|(i, schema)| Entry::Table(VL(i), schema)),
		);
		let schemas = &Env::new(schemas);
		log::info!("Schemas:\n{:?}", schemas.entries);
		log::info!("Input:\n{}\n{}", help.0, help.1);
		let r1 = r1.eval(&Env::empty(), schemas, schemas.size());
		let r2 = r2.eval(&Env::empty(), schemas, schemas.size());
		Payload(env, r1, r2)
	}
}

impl Env<VL> {
	pub fn append_vars(&self, level: usize, amount: usize) -> Env<VL> {
		self.append((0..amount).map(|l| VL(level + l)))
	}
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Relation {
	Singleton,
	Scan(VL),
	Filter {
		condition: Expr,
		source: Box<Relation>,
	},
	Project {
		#[serde(rename = "target")]
		columns: Vec<(Expr, DataType)>,
		source: Box<Relation>,
	},
	Join {
		condition: Expr,
		left: Box<Relation>,
		right: Box<Relation>,
		#[serde(rename = "type")]
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
		#[serde(rename = "function")]
		columns: Vec<(Expr, DataType)>,
		source: Box<Relation>,
	},
}

impl Relation {
	fn eval(self, env: &Env<VL>, schemas: &Env<Schema>, level: usize) -> syntax::Relation {
		use shared::Expr::*;
		use shared::Predicate as Pred;
		use syntax::Relation as Rel;
		use Relation::*;
		match self {
			Singleton => Rel::lam(vec![], UExpr::One),
			Scan(table) => Rel::Var(table),
			Filter { condition, source } => {
				let condition = condition.into_pred();
				let (types, body) = source.split(env, schemas, level);
				let env = &env.append_vars(level, types.len());
				Rel::lam(types, condition.eval(env, schemas, level) * body)
			},
			Project { columns, source } => {
				let new_level = level + columns.len();
				let (source_types, body) = source.split(env, schemas, new_level);
				let (exprs, types): (Vec<_>, Vec<_>) = columns.into_iter().unzip();
				let env = &env.append_vars(new_level, source_types.len());
				let new_body = exprs
					.into_iter()
					.enumerate()
					.map(|(i, expr)| {
						UExpr::Pred(Pred::Eq(Var(VL(level + i)), expr.eval(env, new_level)))
					})
					.fold(body, UExpr::mul);
				Rel::lam(types, UExpr::sum(source_types, new_body))
			},
			// R(x) INNER JOIN S(y) -> λx,y. R(x) × S(y)
			Join { condition, left, right, kind } => {
				let left_arity = left.arity(schemas);
				let right_arity = right.arity(schemas);
				let body_level = level + left_arity + right_arity;
				let left_outer = left.clone().eval(env, schemas, body_level);
				let right_outer = right.clone().eval(env, schemas, body_level);
				let left_vars = (0..left_arity).map(|i| VL(level + i)).collect();
				let right_vars = (0..right_arity).map(|i| VL(level + left_arity + i)).collect();
				let left_types = left_outer.types(schemas);
				let right_types = right_outer.types(schemas);
				let left_body = UExpr::App(left_outer, left_vars);
				let right_body = UExpr::App(right_outer, right_vars);
				let condition = condition.into_pred();
				let types = [left_types.clone(), right_types.clone()].concat();
				let env = &env.append_vars(level, types.len());
				let condition_outer = condition.clone().eval(env, schemas, level);
				let matching = condition_outer * left_body.clone() * right_body.clone();
				let miss = |body: Relation, outer_vars: Range<_>, inner_types: Vec<_>| {
					let inner_level = body_level + inner_types.len();
					let (_, inner_body) = body.split(env, schemas, inner_level);
					let inner_pred = UExpr::App(
						Rel::lam(types.clone(), condition.clone().eval(env, schemas, inner_level)),
						outer_vars.chain(body_level..inner_level).map(VL).collect(),
					);
					(body_level..inner_level)
						.map(|i| UExpr::Pred(Pred::Null(Var(VL(i)))))
						.fold(!UExpr::sum(inner_types, inner_pred * inner_body), UExpr::mul)
				};
				let left_level = level + left_arity;
				let right_miss = || miss(*right, level..left_level, right_types) * left_body;
				let left_miss = || miss(*left, left_level..body_level, left_types) * right_body;
				let types = types.clone();
				match kind {
					JoinKind::Inner => Rel::lam(types, matching),
					JoinKind::Left => Rel::lam(types, matching + right_miss()),
					JoinKind::Right => Rel::lam(types, matching + left_miss()),
					JoinKind::Full => Rel::lam(types, matching + left_miss() + right_miss()),
				}
			},
			Correlate(left, right) => {
				let left_arity = left.arity(schemas);
				let right_arity = right.arity(schemas);
				let new_level = level + left_arity + right_arity;
				let left = left.eval(env, schemas, new_level);
				let left_types = left.types(schemas);
				let left_vars = (0..left_arity).map(|i| VL(level + i));
				let right_env = &env.append(left_vars.clone());
				let right = right.eval(right_env, schemas, new_level);
				let right_types = right.types(schemas);
				let right_vars = (0..right_arity).map(|i| VL(level + right_arity + i));
				let left_body = UExpr::App(left, left_vars.collect());
				let right_body = UExpr::App(right, right_vars.collect());
				Rel::lam([left_types, right_types].concat(), left_body * right_body)
			},
			Union(left, right) => {
				let (left_types, left_body) = left.split(env, schemas, level);
				let (right_types, right_body) = right.split(env, schemas, level);
				assert_eq!(left_types, right_types);
				Rel::lam(left_types, left_body + right_body)
			},
			Except(left, right) => {
				let (left_types, left_body) = left.split(env, schemas, level);
				let (right_types, right_body) = right.split(env, schemas, level);
				assert_eq!(left_types, right_types);
				Rel::lam(left_types, left_body * !right_body)
			},
			Distinct(relation) => {
				let (types, body) = relation.split(env, schemas, level);
				Rel::lam(types, UExpr::squash(body))
			},
			Values { schema, content } => {
				let vars = (0..schema.len()).map(|l| shared::Expr::Var(VL(level + l)));
				let body = content
					.into_iter()
					.map(|row| {
						vars.clone()
							.zip(row)
							.map(|(v, e)| UExpr::Pred(Pred::Eq(v, e.eval(env, level))))
							.fold(UExpr::One, UExpr::mul)
					})
					.fold(UExpr::Zero, UExpr::add);
				Rel::lam(schema, body)
			},
			Aggregate { columns, source } => {
				let new_level = level + columns.len();
				let (source_types, _) = source.clone().split(env, schemas, new_level);
				let (aggs, types): (Vec<_>, Vec<_>) = columns.into_iter().unzip();
				let new_body = aggs
					.into_iter()
					.enumerate()
					.map(|(i, agg)| {
						UExpr::Pred(Pred::Eq(Var(VL(level + i)), agg.eval_agg(*source.clone(), env, schemas, new_level)))
					})
					.fold(UExpr::One, UExpr::mul);
				Rel::lam(types, UExpr::sum(source_types, new_body))
			},
		}
	}

	fn split(self, env: &Env<VL>, schemas: &Env<Schema>, level: usize) -> (Vec<DataType>, UExpr) {
		use shared::Relation::*;
		match self.eval(env, schemas, level) {
			Var(l) => {
				let types = schemas.get(l).types.clone();
				let vars = (0..types.len()).map(|i| VL(level + i)).collect();
				(types, UExpr::App(Var(l), vars))
			},
			Lam(types, body) => (types, *body),
		}
	}

	fn arity(&self, schemas: &Env<Schema>) -> usize {
		use Relation::*;
		match self {
			Singleton => 0,
			Scan(table) => schemas.get(*table).types.len(),
			Filter { source, .. } => source.arity(schemas),
			Project { columns, .. } => columns.len(),
			Join { left, right, .. } => left.arity(schemas) + right.arity(schemas),
			Correlate(left, right) => left.arity(schemas) + right.arity(schemas),
			Union(rel1, _) | Except(rel1, _) => rel1.arity(schemas),
			Distinct(rel) => rel.arity(schemas),
			Values { schema, .. } => schema.len(),
			Aggregate { columns, .. } => columns.len(),
		}
	}
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "UPPERCASE")]
pub enum JoinKind {
	Inner,
	Left,
	Right,
	Full,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[serde(untagged)]
pub enum Expr {
	Col {
		column: VL,
	},
	Op {
		#[serde(rename = "operator")]
		op: String,
		#[serde(rename = "operand")]
		args: Vec<Expr>,
	},
}

impl Expr {
	fn eval(self, env: &Env<VL>, level: usize) -> syntax::Expr {
		use shared::Expr::*;
		match self {
			Expr::Col { column } => Var(*env.get(column)),
			Expr::Op { op, args } => Op(op, args.into_iter().map(|e| e.eval(env, level)).collect()),
		}
	}

	fn eval_agg(self, source: Relation, env: &Env<VL>, schemas: &Env<Schema>, level: usize) -> syntax::Expr {
		use shared::Expr::*;
		if let Expr::Op { op, args } = self {
			match op.as_str() {
				"COUNT" if args.is_empty() => Agg(op, Box::new(source.eval(env, schemas, level))),
				_ => Agg(op, Box::new(Relation::Project {
					columns: args.into_iter().map(|arg| (arg, DataType::Any)).collect(),
					source: Box::new(source),
				}.eval(env, schemas, level))),
			}
		} else {
			panic!()
		}
	}

	fn into_pred(self) -> Predicate {
		use Predicate::*;
		if let Expr::Op { op, args } = self {
			match op.as_str() {
				"TRUE" => True,
				"FALSE" => False,
				"=" => Eq(args[0].clone(), args[1].clone()),
				"AND" => And(
					Box::new(args[0].clone().into_pred()),
					Box::new(args[1].clone().into_pred()),
				),
				"OR" => {
					Or(Box::new(args[0].clone().into_pred()), Box::new(args[1].clone().into_pred()))
				},
				"NOT" => Not(Box::new(args[0].clone().into_pred())),
				"IS NULL" => Null(args[0].clone()),
				"IS NOT NULL" => Not(Box::new(Null(args[0].clone()))),
				op => Pred(op.to_string(), args),
			}
		} else {
			panic!()
		}
	}
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Predicate {
	True,
	False,
	Null(Expr),
	Eq(Expr, Expr),
	Like(Expr, String),
	Exists(Box<Relation>),
	Pred(String, Vec<Expr>),
	And(Box<Predicate>, Box<Predicate>),
	Or(Box<Predicate>, Box<Predicate>),
	Not(Box<Predicate>),
}

impl Predicate {
	fn eval(self, env: &Env<VL>, schemas: &Env<Schema>, level: usize) -> UExpr {
		use shared::Predicate as Pred;
		use Predicate::*;
		match self {
			True => UExpr::One,
			False => UExpr::Zero,
			Null(e) => UExpr::Pred(Pred::Null(e.eval(env, level))),
			Eq(e1, e2) => UExpr::Pred(Pred::Eq(e1.eval(env, level), e2.eval(env, level))),
			Like(e, pat) => UExpr::Pred(Pred::Like(e.eval(env, level), pat)),
			Exists(rel) => {
				let (types, body) = rel.split(env, schemas, level);
				UExpr::squash(UExpr::sum(types, body))
			},
			Pred(p, es) => {
				UExpr::Pred(Pred::Pred(p, es.into_iter().map(|e| e.eval(env, level)).collect()))
			},
			And(p1, p2) => p1.eval(env, schemas, level) * p2.eval(env, schemas, level),
			Or(p1, p2) => {
				UExpr::squash(p1.eval(env, schemas, level) + p2.eval(env, schemas, level))
			},
			Not(p) => !p.eval(env, schemas, level),
		}
	}
}
