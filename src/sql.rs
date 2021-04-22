use serde::{Deserialize, Serialize};

use crate::nbe::shared::{Expr as TExpr, Predicate as TPredicate, Schema, VL};

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
	Query { select: Vec<Expr>, from: Box<Table>, pred: Option<Predicate> },
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Expr {
	Col(usize),
	Op(String, Vec<Expr>),
}

impl Expr {
	pub fn convert(self, level: usize) -> TExpr {
		use Expr::*;
		match self {
			Col(i) => TExpr::Var(VL(level + i)),
			Op(op, exprs) => TExpr::Op(op, exprs.into_iter().map(|e| e.convert(level)).collect()),
		}
	}
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Predicate {
	Eq(Expr, Expr),
	Pred(String, Vec<Expr>),
	And(Box<Predicate>, Box<Predicate>),
	Or(Box<Predicate>, Box<Predicate>),
	Not(Box<Predicate>),
	Like(Expr, String),
}

impl Predicate {
	pub fn convert(self, level: usize) -> TPredicate {
		use Predicate::*;
		match self {
			Eq(e1, e2) => TPredicate::Eq(e1.convert(level), e2.convert(level)),
			Pred(p, es) => TPredicate::Pred(p, es.into_iter().map(|e| e.convert(level)).collect()),
			And(p1, p2) => {
				TPredicate::And(Box::new(p1.convert(level)), Box::new(p2.convert(level)))
			},
			Or(p1, p2) => TPredicate::Or(Box::new(p1.convert(level)), Box::new(p2.convert(level))),
			Not(p) => TPredicate::Not(Box::new(p.convert(level))),
			Like(e, pattern) => TPredicate::Like(e.convert(level), pattern),
		}
	}
}
