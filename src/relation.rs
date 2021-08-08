use std::ops::{Add, Mul};

use im::Vector;
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
		let level = schemas.size();
		let r1 = r1.eval(&Env::empty().shift_to(level), schemas);
		let r2 = r2.eval(&Env::empty().shift_to(level), schemas);
		Payload(env, r1, r2)
	}
}

impl Env<VL> {
	pub fn append_vars(&self, amount: usize) -> Self {
		self.shift_to(self.level + amount).append((0..amount).map(|l| VL(self.level + l)))
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
	fn eval(&self, env: &Env<VL>, schemas: &Env<Schema>) -> syntax::Relation {
		use shared::Expr::*;
		use shared::Predicate::*;
		use syntax::Relation as Rel;
		use Relation::*;
		match self {
			Singleton => Rel::lam(vec![], UExpr::One),
			Scan(table) => Rel::Var(*table),
			// Filter R(x, y) by P(x, y)
			// λ x, y. [P(x, y)] × R(x, y)
			Filter { condition, source } => {
				let (types, body) = source.split(env, schemas);
				let env = &env.append_vars(types.len());
				Rel::lam(types, condition.to_pred().eval(env, schemas) * body)
			},
			// Project f(x, y) from R(x, y)
			// λ a. ∑ x, y. [a = f(x, y)] × R(x, y)
			Project { columns, source } => {
				let (ref env, vars) = env.shift(columns.len());
				let (source_types, body) = source.split(env, schemas);
				let (exprs, types): (Vec<_>, Vec<_>) = columns.iter().cloned().unzip();
				let env = &env.append_vars(source_types.len());
				let new_body = vars
					.into_iter()
					.zip(exprs)
					.map(|(v, expr)| UExpr::Pred(Eq(Var(v), expr.eval(env))))
					.fold(body, UExpr::mul);
				Rel::lam(types, UExpr::sum(source_types, new_body))
			},
			// R(x) inner join S(y) on P(x, y)
			// λx, y. [P(x, y)] × R(x) × S(y)
			// R(x) full join S(y) on P(x, y)
			// λx, y. [P(x, y)] × R(x) × S(y)
			//        + ¬(∑ x'. P(x', y) × R(x')) × Null(x) × S(y)
			//        + ¬(∑ y'. P(x, y') × S(y')) × Null(y) × R(x)
			Join { condition, left, right, kind } => {
				let left_arity = left.arity(schemas);
				let right_arity = right.arity(schemas);
				let (left_env, ref left_vars) = env.shift(left_arity);
				let (ref body_env, ref right_vars) = left_env.shift(right_arity);
				let (left_types, left_body) =
					left.split_apply(body_env, schemas, left_vars.clone());
				let (right_types, right_body) =
					right.split_apply(body_env, schemas, right_vars.clone());
				let types = &left_types + &right_types;
				let cond = condition.to_pred();
				let cond_env = &env.append_vars(left_arity + right_arity);
				let match_pred = cond.eval(cond_env, schemas);
				let matching = match_pred * left_body.clone() * right_body.clone();
				let miss = |miss_left: bool| {
					let missing = if miss_left { left } else { right };
					let (inner_types, inner_body) = missing.split(body_env, schemas);
					let (ref inner_env, ref inner_vars) = body_env.shift(inner_types.len());
					let cond_vars =
						if miss_left { inner_vars + right_vars } else { left_vars + inner_vars };
					let cond_env = &inner_env.append(cond_vars);
					let inner_pred = cond.eval(cond_env, schemas);
					let null_vars = if miss_left { left_vars } else { right_vars };
					null_vars
						.iter()
						.map(|v| UExpr::Pred(Null(Var(*v))))
						.fold(!UExpr::sum(inner_types, inner_pred * inner_body), UExpr::mul)
				};
				let left_miss = miss(true) * right_body;
				let right_miss = miss(false) * left_body;
				match kind {
					JoinKind::Inner => Rel::lam(types, matching),
					JoinKind::Left => Rel::lam(types, matching + right_miss),
					JoinKind::Right => Rel::lam(types, matching + left_miss),
					JoinKind::Full => Rel::lam(types, matching + left_miss + right_miss),
				}
			},
			// S[x](y) correlated join R(x)
			// λx, y. R(x) × S[x](y)
			Correlate(left, right) => {
				let left_arity = left.arity(schemas);
				let right_arity = right.arity(schemas);
				let (left_env, left_vars) = env.shift(left_arity);
				let (ref body_env, _) = left_env.shift(right_arity);
				let (left_types, left_body) = left.split_apply(body_env, schemas, left_vars);
				let right_env = &env.append_vars(left_arity);
				let (right_types, right_body) = right.split(right_env, schemas);
				Rel::lam(left_types + right_types, left_body * right_body)
			},
			// R(x) union S(y)
			// λx. R(x) + S(x)
			Union(left, right) => {
				let (left_types, left_body) = left.split(env, schemas);
				let (right_types, right_body) = right.split(env, schemas);
				assert_eq!(left_types, right_types);
				Rel::lam(left_types, left_body + right_body)
			},
			// R(x) except S(y)
			// λx. R(x) × ¬S(x)
			Except(left, right) => {
				let (left_types, left_body) = left.split(env, schemas);
				let (right_types, right_body) = right.split(env, schemas);
				assert_eq!(left_types, right_types);
				Rel::lam(left_types, left_body * !right_body)
			},
			// Distinct R(x)
			// λx. ‖R(x)‖
			Distinct(relation) => {
				let (types, body) = relation.split(env, schemas);
				Rel::lam(types, UExpr::squash(body))
			},
			// Values ((a1, b1), (a2, b2), (a3, b3))
			// λx, y. [x = a1] × [y = b1] + [x = a2] × [y = b2] + [x = a3] × [y = b3]
			Values { schema, content } => {
				let (ref env, vars) = env.shift(schema.len());
				let body = content
					.iter()
					.map(|row| {
						vars.iter()
							.zip(row)
							.map(|(v, e)| UExpr::Pred(Eq(Var(*v), e.eval(env))))
							.fold(UExpr::One, UExpr::mul)
					})
					.fold(UExpr::Zero, UExpr::add);
				Rel::lam(schema.clone(), body)
			},
			// Agg1(f(x, y)), Agg2(g(x, y)) on R(x, y)
			// λa, b. [a = Agg1(λc. ∑x, y. [c = f(x, y)] × R(x, y))]
			//        × [b = Agg2(λc. ∑x, y. [c = g(x, y)] × R(x, y))]
			Aggregate { columns, source } => {
				let (ref env, out_vars) = env.shift(columns.len());
				let (aggs, types): (Vec<_>, Vec<_>) = columns.iter().cloned().unzip();
				// TODO: Better type handling
				let new_body = out_vars
					.into_iter()
					.zip(aggs)
					.zip(types.clone())
					.map(|((v, agg), ty)| {
						UExpr::Pred(Eq(Var(v), agg.eval_agg(source, env, schemas, ty)))
					})
					.fold(UExpr::One, UExpr::mul);
				Rel::lam(types, new_body)
			},
		}
	}

	fn split(&self, env: &Env<VL>, schemas: &Env<Schema>) -> (Vector<DataType>, UExpr) {
		use shared::Relation::*;
		match self.eval(env, schemas) {
			Var(l) => {
				let types = schemas.get(l).types.clone();
				let vars = (0..types.len()).map(|i| VL(env.level + i)).collect();
				(types.into(), UExpr::App(Var(l), vars))
			},
			Lam(types, body) => (types, *body),
		}
	}

	fn split_apply(
		&self,
		env: &Env<VL>,
		schemas: &Env<Schema>,
		vars: Vector<VL>,
	) -> (Vector<DataType>, UExpr) {
		let rel = self.eval(env, schemas);
		(rel.types(schemas), UExpr::App(rel, vars))
	}

	fn arity(&self, schemas: &Env<Schema>) -> usize {
		use Relation::*;
		match self {
			Singleton => 0,
			Scan(table) => schemas.get(*table).types.len(),
			Filter { source, .. } => source.arity(schemas),
			Project { columns, .. } | Aggregate { columns, .. } => columns.len(),
			Join { left, right, .. } | Correlate(left, right) => {
				left.arity(schemas) + right.arity(schemas)
			},
			Union(rel1, _) | Except(rel1, _) => rel1.arity(schemas),
			Distinct(rel) => rel.arity(schemas),
			Values { schema, .. } => schema.len(),
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
	fn eval(&self, env: &Env<VL>) -> syntax::Expr {
		use shared::Expr::*;
		match self {
			Expr::Col { column } => Var(*env.get(*column)),
			Expr::Op { op, args } if op == "CAST" => args[0].eval(env),
			Expr::Op { op, args } => Op(op.clone(), args.iter().map(|e| e.eval(env)).collect()),
		}
	}

	fn eval_agg(
		self,
		source: &Relation,
		env: &Env<VL>,
		schemas: &Env<Schema>,
		ty: DataType,
	) -> syntax::Expr {
		use shared::Expr::*;
		if let Expr::Op { op, args } = self {
			match op.as_str() {
				"COUNT" if args.is_empty() => Agg(op, Box::new(source.eval(env, schemas))),
				_ => Agg(
					op,
					Box::new(
						Relation::Project {
							columns: args.into_iter().map(|arg| (arg, ty.clone())).collect(),
							source: Box::new(source.clone()),
						}
						.eval(env, schemas),
					),
				),
			}
		} else {
			panic!()
		}
	}

	fn to_pred(&self) -> Predicate {
		use Predicate::*;
		if let Expr::Op { op, args } = self {
			match op.as_str() {
				"TRUE" => True,
				"FALSE" => False,
				"=" => Eq(args[0].clone(), args[1].clone()),
				"AND" => And(Box::new(args[0].to_pred()), Box::new(args[1].to_pred())),
				"OR" => Or(Box::new(args[0].to_pred()), Box::new(args[1].to_pred())),
				"NOT" => Not(Box::new(args[0].to_pred())),
				"IS NULL" => Null(args[0].clone()),
				"IS NOT NULL" => Not(Box::new(Null(args[0].clone()))),
				op => Pred(op.to_string(), args.clone()),
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
	fn eval(&self, env: &Env<VL>, schemas: &Env<Schema>) -> UExpr {
		use shared::Predicate as Pred;
		use Predicate::*;
		match self {
			True => UExpr::One,
			False => UExpr::Zero,
			Null(e) => UExpr::Pred(Pred::Null(e.eval(env))),
			Eq(e1, e2) => UExpr::Pred(Pred::Eq(e1.eval(env), e2.eval(env))),
			Like(e, pat) => UExpr::Pred(Pred::Like(e.eval(env), pat.clone())),
			Exists(rel) => {
				let (types, body) = rel.split(env, schemas);
				UExpr::squash(UExpr::sum(types, body))
			},
			Pred(p, es) => {
				UExpr::Pred(Pred::Pred(p.clone(), es.iter().map(|e| e.eval(env)).collect()))
			},
			And(p1, p2) => p1.eval(env, schemas) * p2.eval(env, schemas),
			Or(p1, p2) => UExpr::squash(p1.eval(env, schemas) + p2.eval(env, schemas)),
			Not(p) => !p.eval(env, schemas),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_full_join() {
		let schemas = vec![
			Schema { types: vec![DataType::Int, DataType::String], ..Schema::default() },
			Schema { types: vec![DataType::Int, DataType::Boolean], ..Schema::default() },
		];

		let input = Relation::Join {
			left: Box::new(t(0)),
			right: Box::new(t(1)),
			condition: Expr::Op { op: "=".to_string(), args: vec![c(0), c(2)] },
			kind: JoinKind::Full,
		};

		let output = input.eval(&Env::empty().shift_to(2), &Env::new(schemas));

		let expected = {
			use shared::Predicate::*;
			use syntax::UExpr::Pred;
			use DataType::*;
			let matching = Pred(Eq(v(2), v(4))) * app(r(0), [2, 3]) * app(r(1), [4, 5]);
			let left_miss =
				!UExpr::sum(vec![Int, String], Pred(Eq(v(6), v(4))) * app(r(0), [6, 7]))
					* Pred(Null(v(2))) * Pred(Null(v(3)))
					* app(r(1), [4, 5]);
			let right_miss =
				!UExpr::sum(vec![Int, Boolean], Pred(Eq(v(2), v(6))) * app(r(1), [6, 7]))
					* Pred(Null(v(4))) * Pred(Null(v(5)))
					* app(r(0), [2, 3]);
			lam([Int, String, Int, Boolean], matching + left_miss + right_miss)
		};

		assert_eq!(expected, output, "Expecting:\n{}\nActual result:\n{}", expected, output);
	}

	#[test]
	fn test_correlate() {
		use DataType::*;
		let schemas = vec![Schema { types: vec![Int, String], ..Schema::default() }, Schema {
			types: vec![Int, Boolean],
			..Schema::default()
		}];
		let input = corr(t(0), proj([(c(0) + c(2), Int)], t(1)));
		let output = input.eval(&Env::empty().shift_to(2), &Env::new(schemas));
		println!("{}", output);
	}

	impl Add for Expr {
		type Output = Expr;

		fn add(self, rhs: Self) -> Self::Output {
			Expr::Op { op: "+".to_string(), args: vec![self, rhs] }
		}
	}

	fn proj<C, R>(columns: C, source: R) -> Relation
	where
		C: IntoIterator<Item = (Expr, DataType)>,
		R: Into<Box<Relation>>,
	{
		Relation::Project { columns: columns.into_iter().collect(), source: source.into() }
	}

	fn corr<R1, R2>(r1: R1, r2: R2) -> Relation
	where
		R1: Into<Box<Relation>>,
		R2: Into<Box<Relation>>,
	{
		Relation::Correlate(r1.into(), r2.into())
	}

	fn app<A>(rel: syntax::Relation, args: A) -> UExpr
	where A: IntoIterator<Item = usize> {
		UExpr::App(rel, args.into_iter().map(VL).collect())
	}

	fn lam<T, U>(types: T, body: U) -> syntax::Relation
	where
		T: IntoIterator<Item = DataType>,
		U: Into<Box<UExpr>>,
	{
		shared::Relation::Lam(types.into_iter().collect(), body.into())
	}

	fn r(level: usize) -> syntax::Relation {
		shared::Relation::Var(VL(level))
	}

	fn v(level: usize) -> syntax::Expr {
		shared::Expr::Var(VL(level))
	}

	fn t(tab: usize) -> Relation {
		Relation::Scan(VL(tab))
	}

	fn c(col: usize) -> Expr {
		Expr::Col { column: VL(col) }
	}
}
