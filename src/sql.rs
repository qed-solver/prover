use serde::{Deserialize, Serialize};

use crate::evaluate::shared;
use crate::evaluate::shared::{DataType, Entry, Env, Schema, VL};
use crate::evaluate::syntax::{Payload, Relation, UExpr};

#[derive(Debug, Serialize, Deserialize)]
pub struct SQL {
	pub schemas: Vec<Schema>,
	pub tables: (Table, Table),
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Table {
	Var(VL),
	Join(Box<Table>, Box<Table>),
	OuterJoin(Box<Table>, Box<Table>, Predicate),
	Union(Box<Table>, Box<Table>),
	Except(Box<Table>, Box<Table>),
	Distinct(Box<Table>),
	Query { select: Vec<Expr>, from: Box<Table>, pred: Option<Predicate> },
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Expr {
	Col(usize),
	Op(String, Vec<Expr>),
}

impl Expr {
	fn shift_var(self, level: usize) -> shared::Expr {
		use Expr::*;
		match self {
			Col(i) => shared::Expr::Var(VL(level + i)),
			Op(op, exprs) => {
				shared::Expr::Op(op, exprs.into_iter().map(|e| e.shift_var(level)).collect())
			},
		}
	}
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Predicate {
	True,
	False,
	Eq(Expr, Expr),
	Pred(String, Vec<Expr>),
	And(Box<Predicate>, Box<Predicate>),
	Or(Box<Predicate>, Box<Predicate>),
	Not(Box<Predicate>),
	Like(Expr, String),
	Exists(Box<Table>),
}

impl Predicate {
	fn shift_var(self, schemas: &[Schema], level: usize) -> UExpr {
		use Predicate::*;
		match self {
			True => UExpr::One,
			False => UExpr::Zero,
			Eq(e1, e2) => {
				UExpr::Pred(shared::Predicate::Eq(e1.shift_var(level), e2.shift_var(level)))
			},
			Pred(p, es) => UExpr::Pred(shared::Predicate::Pred(
				p,
				es.into_iter().map(|e| e.shift_var(level)).collect(),
			)),
			And(p1, p2) => p1.shift_var(schemas, level) * p2.shift_var(schemas, level),
			Or(p1, p2) => {
				UExpr::Squash(Box::new(p1.shift_var(schemas, level) + p2.shift_var(schemas, level)))
			},
			Not(p) => UExpr::Not(Box::new(p.shift_var(schemas, level))),
			Like(e, pattern) => UExpr::Pred(shared::Predicate::Like(e.shift_var(level), pattern)),
			Exists(t) => {
				let rel = parse(*t, schemas, level);
				let (types, body) = extract(rel, schemas, level);
				UExpr::Sum(types, Box::new(body))
			},
		}
	}
}

// Extract the types of arguments and body from a relation.
// If the relation is already in the lambda function form, this is trivial.
// Otherwise the relation is represented by some variable R, and we need to eta-expand
// λ a, b, c. R(a, b, c)
fn extract(relation: Relation, schemas: &[Schema], level: usize) -> (Vec<DataType>, UExpr) {
	match relation {
		Relation::Var(l) => {
			let arity = schemas[l.0].types.len();
			// TODO: Properly convert String to DataType
			let vars = (0..arity).map(|i| VL(level + i)).collect();
			(vec![DataType::Any; arity], UExpr::App(relation, vars))
		},
		Relation::Lam(types, body) => (types, *body),
	}
}

fn types(relation: &Relation, schemas: &[Schema]) -> Vec<DataType> {
	match relation {
		Relation::Var(l) => schemas[l.0].types.iter().map(|ty| DataType::Any).collect(),
		Relation::Lam(types, _) => types.clone(),
	}
}

fn arity(table: &Table, schemas: &[Schema]) -> usize {
	match table {
		Table::Var(v) => schemas[v.0].types.len(),
		Table::Join(t1, t2) | Table::OuterJoin(t1, t2, _) => {
			arity(t1.as_ref(), schemas) + arity(t2.as_ref(), schemas)
		},
		Table::Union(t1, _) | Table::Except(t1, _) => arity(t1.as_ref(), schemas),
		Table::Distinct(t) => arity(t.as_ref(), schemas),
		Table::Query { select, .. } => select.len(),
	}
}

fn parse(table: Table, schemas: &[Schema], level: usize) -> Relation {
	match table {
		Table::Var(v) => Relation::Var(v),
		Table::Join(t1, t2) => {
			let arity1 = arity(t1.as_ref(), schemas);
			let arity2 = arity(t2.as_ref(), schemas);
			let new_level = level + arity1 + arity2;
			let left = parse(*t1, schemas, new_level);
			let right = parse(*t2, schemas, new_level);
			let types = [types(&left, schemas), types(&right, schemas)].concat();
			Relation::Lam(
				types,
				Box::new(
					UExpr::App(left, (0..arity1).map(|i| VL(level + i)).collect())
						* UExpr::App(right, (0..arity2).map(|i| VL(level + arity1 + i)).collect()),
				),
			)
		},
		Table::OuterJoin(t1, t2, pred) => {
			// TODO: Special handling for nulls
			let arity1 = arity(t1.as_ref(), schemas);
			let arity2 = arity(t2.as_ref(), schemas);
			let new_level = level + arity1 + arity2;
			let left = parse(*t1, schemas, new_level);
			let right = parse(*t2, schemas, new_level);
			let types = [types(&left, schemas), types(&right, schemas)].concat();
			let pred_term = pred.shift_var(schemas, level);
			Relation::Lam(
				types,
				Box::new(
					UExpr::App(left, (0..arity1).map(|i| VL(level + i)).collect())
						* UExpr::App(right, (0..arity2).map(|i| VL(level + arity1 + i)).collect())
						* pred_term,
				),
			)
		},
		Table::Union(t1, t2) => {
			let left = parse(*t1, schemas, level);
			let (left_types, left_body) = extract(left, schemas, level);
			let right = parse(*t2, schemas, level);
			let (right_types, right_body) = extract(right, schemas, level);
			assert_eq!(left_types, right_types);
			Relation::Lam(left_types, Box::new(left_body + right_body))
		},
		Table::Except(t1, t2) => {
			let left = parse(*t1, schemas, level);
			let (left_types, left_body) = extract(left, schemas, level);
			let right = parse(*t2, schemas, level + left_types.len());
			let (right_types, right_body) = extract(right, schemas, level);
			assert_eq!(left_types, right_types);
			Relation::Lam(left_types, Box::new(left_body * !right_body))
		},
		Table::Distinct(tab) => {
			let rel = parse(*tab, schemas, level);
			let (types, body) = extract(rel, schemas, level);
			Relation::Lam(types, Box::new(UExpr::Squash(Box::new(body))))
		},
		Table::Query { select, from, pred } => {
			let arity = select.len();
			let new_level = level + arity;
			let source = parse(*from, schemas, new_level);
			let (types, body) = extract(source, schemas, new_level);
			let preds = select
				.into_iter()
				.enumerate()
				.map(|(i, col)| {
					UExpr::Pred(shared::Predicate::Eq(
						shared::Expr::Var(VL(level + i)),
						col.shift_var(new_level),
					))
				})
				.fold(pred.map_or(UExpr::One, |p| p.shift_var(schemas, new_level)), |t, p| t * p);
			let sum = UExpr::Sum(types, Box::new(preds * body));
			// TODO: Properly convert String to DataType
			Relation::Lam(vec![DataType::Any; arity], Box::new(sum))
		},
	}
}

impl From<SQL> for Payload {
	fn from(SQL { schemas, tables }: SQL) -> Self {
		let r1 = parse(tables.0, &schemas, schemas.len());
		let r2 = parse(tables.1, &schemas, schemas.len());
		let env = Env::new(
			schemas
				.into_iter()
				.enumerate()
				.map(|(i, schema)| Entry::new_table(VL(i), schema))
				.collect(),
		);
		Payload(env, r1, r2)
	}
}
