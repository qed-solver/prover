use std::collections::{HashMap, VecDeque};
use std::hash::Hash;
use std::iter::FromIterator;

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
	pub fn var(&self) -> VL {
		match self {
			Entry::Table(l, _) => *l,
			Entry::Value(l, _) => *l,
		}
	}

	pub fn sch(&self) -> Schema {
		if let Entry::Table(_, sch) = self {
			sch.clone()
		} else {
			panic!()
		}
	}

	pub fn ty(&self) -> DataType {
		if let Entry::Value(_, ty) = self {
			ty.clone()
		} else {
			panic!()
		}
	}
}

/// The environment of some expression, which maps every variable that occurs in the expression to some value.
#[derive(Debug, Clone, Default)]
pub struct Env<E> {
	pub entries: VecDeque<E>,
}

impl<E> Env<E> {
	pub fn empty() -> Self {
		Env { entries: VecDeque::new() }
	}

	pub fn new<T: IntoIterator<Item = E>>(entries: T) -> Self {
		Env { entries: VecDeque::from_iter(entries) }
	}

	pub fn size(&self) -> usize {
		self.entries.len()
	}

	pub fn get(&self, level: VL) -> &E {
		&self.entries[level.0]
	}

	pub fn introduce(&mut self, entry: E) {
		self.entries.push_back(entry);
	}

	pub fn extend<T: IntoIterator<Item = E>>(&mut self, entries: T) {
		self.entries.extend(entries);
	}
}

impl<E: Clone> Env<E> {
	pub fn append<T: IntoIterator<Item = E>>(&self, entries_iter: T) -> Env<E> {
		let mut entries = self.entries.clone();
		entries.extend(entries_iter);
		Env { entries }
	}
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Expr {
	Var(VL),
	Op(String, Vec<Expr>),
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Predicate {
	Eq(Expr, Expr),
	Pred(String, Vec<Expr>),
	Like(Expr, String),
	Null(Expr),
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Schema {
	pub types: Vec<DataType>,
	#[serde(skip)] // TODO: Multiple primary keys
	#[serde(rename = "primary_key")]
	pub primary: Option<usize>,
	#[serde(skip)] // TODO: Multiple primary keys
	#[serde(rename = "foreign_key")]
	pub foreign: HashMap<usize, VL>,
}

impl Env<Entry> {
	pub fn get_var(&self, level: VL) -> VL {
		self.get(level).var()
	}

	pub fn eval_args(&self, args: Vec<VL>) -> Vec<VL> {
		args.into_iter().map(|arg| self.get_var(arg)).collect()
	}

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
			Predicate::Like(v, s) => Predicate::Like(self.eval_expr(v), s),
			Predicate::Null(v) => Predicate::Null(self.eval_expr(v)),
		}
	}
}

/// SQL data types (adapted from sqlparser)
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "UPPERCASE")]
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
	#[serde(other)]
	Any,
}
