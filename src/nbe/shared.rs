use std::collections::{HashMap, VecDeque};
use std::hash::Hash;

use serde::{Deserialize, Serialize};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct VL(pub usize);

#[derive(Debug, Clone)]
pub enum Entry {
	Table(VL, Schema),
	Value(VL, DataType),
}

impl Entry {
	pub fn new_value(data: VL, ty: DataType) -> Entry {
		Entry::Value(data, ty)
	}

	pub fn new_table(data: VL, schema: Schema) -> Entry {
		Entry::Table(data, schema)
	}

	pub fn var(&self) -> VL {
		match self {
			Entry::Table(l, _) => *l,
			Entry::Value(l, _) => *l,
		}
	}
}

/// The environment of some expression, which maps every variable that occurs in the expression to some value.
#[derive(Debug, Clone, Default)]
pub struct Env {
	pub entries: VecDeque<Entry>,
}

impl Env {
	pub fn new(entries: Vec<Entry>) -> Self {
		Env { entries: entries.into() }
	}

	pub fn size(&self) -> usize {
		self.entries.len()
	}

	pub fn get(&self, level: VL) -> &Entry {
		&self.entries[level.0]
	}

	pub fn get_var(&self, level: VL) -> VL {
		self.get(level).var()
	}

	pub fn get_schema(&self, level: VL) -> &Schema {
		if let Entry::Table(_, schema) = self.get(level) {
			schema
		} else {
			panic!()
		}
	}

	pub fn get_type(&self, level: VL) -> &DataType {
		if let Entry::Value(_, ty) = &self.get(level) {
			ty
		} else {
			panic!()
		}
	}

	pub fn introduce(&mut self, entry: Entry) {
		self.entries.push_back(entry);
	}

	pub fn append(&mut self, entries: Vec<Entry>) {
		self.entries.extend(entries);
	}
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Expr {
	Var(VL),
	Op(String, Vec<Expr>),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Predicate {
	Eq(Expr, Expr),
	Pred(String, Vec<Expr>),
	And(Box<Predicate>, Box<Predicate>),
	Or(Box<Predicate>, Box<Predicate>),
	Not(Box<Predicate>),
	Like(Expr, String),
}

impl Env {
	pub fn read_args(&self, args: Vec<VL>) -> Vec<VL> {
		args.into_iter().map(|arg| self.get_var(arg)).collect()
	}

	pub fn read_val(&self, value: Expr) -> Expr {
		match value {
			Expr::Var(l) => Expr::Var(self.get_var(l)),
			Expr::Op(f, args) => Expr::Op(f, args.into_iter().map(|v| self.read_val(v)).collect()),
		}
	}

	pub fn read_pred(&self, pred: Predicate) -> Predicate {
		match pred {
			Predicate::Eq(v1, v2) => Predicate::Eq(self.read_val(v1), self.read_val(v2)),
			Predicate::Pred(r, args) => {
				Predicate::Pred(r, args.into_iter().map(|v| self.read_val(v)).collect())
			},
			Predicate::And(p1, p2) => {
				Predicate::And(Box::new(self.read_pred(*p1)), Box::new(self.read_pred(*p2)))
			},
			Predicate::Or(p1, p2) => {
				Predicate::Or(Box::new(self.read_pred(*p1)), Box::new(self.read_pred(*p2)))
			},
			Predicate::Not(p) => Predicate::Not(Box::new(self.read_pred(*p))),
			Predicate::Like(v, s) => Predicate::Like(self.read_val(v), s),
		}
	}

	pub fn read_sch(&self, schema: Schema) -> Schema {
		let foreign = schema.foreign.into_iter().map(|(col, t)| (col, self.get_var(t))).collect();
		Schema { types: schema.types, primary: schema.primary, foreign }
	}
}

impl Env {
	pub fn eval_expr(&self, value: Expr) -> Expr {
		match value {
			Expr::Var(l) => Expr::Var(self.get_var(l)),
			Expr::Op(f, args) => Expr::Op(f, args.into_iter().map(|v| self.eval_expr(v)).collect()),
		}
	}

	pub fn eval_pred(&self, pred: Predicate) -> Predicate {
		match pred {
			Predicate::Eq(v1, v2) => Predicate::Eq(self.eval_expr(v1), self.eval_expr(v2)),
			Predicate::Pred(r, args) => {
				Predicate::Pred(r, args.into_iter().map(|v| self.eval_expr(v)).collect())
			},
			Predicate::And(p1, p2) => {
				Predicate::And(Box::new(self.eval_pred(*p1)), Box::new(self.eval_pred(*p2)))
			},
			Predicate::Or(p1, p2) => {
				Predicate::Or(Box::new(self.eval_pred(*p1)), Box::new(self.eval_pred(*p2)))
			},
			Predicate::Not(p) => Predicate::Not(Box::new(self.eval_pred(*p))),
			Predicate::Like(v, s) => Predicate::Like(self.eval_expr(v), s),
		}
	}

	pub fn eval_sch(&self, schema: Schema) -> Schema {
		let foreign = schema.foreign.into_iter().map(|(col, t)| (col, self.get_var(t))).collect();
		Schema { types: schema.types, primary: schema.primary, foreign }
	}
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Schema {
	pub types: Vec<String>,
	pub primary: Option<usize>,
	pub foreign: HashMap<usize, VL>,
}

impl Schema {
	pub fn new(types: Vec<String>, primary: Option<usize>, foreign: HashMap<usize, VL>) -> Self {
		Schema { types, primary, foreign }
	}
}

/// SQL data types (adapted from sqlparser)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DataType {
	/// Fixed-length character type e.g. CHAR(10)
	Char(Option<u64>),
	/// Variable-length character type e.g. VARCHAR(10)
	Varchar(Option<u64>),
	/// Uuid type
	Uuid,
	/// Large character object e.g. CLOB(1000)
	Clob(u64),
	/// Fixed-length binary type e.g. BINARY(10)
	Binary(u64),
	/// Variable-length binary type e.g. VARBINARY(10)
	Varbinary(u64),
	/// Large binary object e.g. BLOB(1000)
	Blob(u64),
	/// Decimal type with optional precision and scale e.g. DECIMAL(10,2)
	Decimal(Option<u64>, Option<u64>),
	/// Floating point with optional precision e.g. FLOAT(8)
	Float(Option<u64>),
	/// Small integer
	SmallInt,
	/// Integer
	Int,
	/// Big integer
	BigInt,
	/// Floating point e.g. REAL
	Real,
	/// Double e.g. DOUBLE PRECISION
	Double,
	/// Boolean
	Boolean,
	/// Date
	Date,
	/// Time
	Time,
	/// Timestamp
	Timestamp,
	/// Interval
	Interval,
	/// Regclass used in postgresql serial
	Regclass,
	/// Text
	Text,
	/// String
	String,
	/// Bytea
	Bytea,
	/// Custom type such as enums
	Custom(String),
	/// Arrays
	Array(Box<DataType>),
	/// Any type
	Any,
}
