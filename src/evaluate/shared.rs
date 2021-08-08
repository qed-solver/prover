use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Write};
use std::hash::Hash;
use std::iter::FromIterator;

use im::Vector;
use indenter::indented;
use itertools::Itertools;
use serde::{Deserialize, Serialize};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct VL(pub usize);

impl Display for VL {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "${}", self.0)
	}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Entry {
	Table(VL, Schema),
	Value(VL, DataType),
}

impl Entry {
	pub fn var(&self) -> VL {
		match self {
			Entry::Table(l, _) | Entry::Value(l, _) => *l,
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
#[derive(Debug, Clone, Default, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Env<E: Clone> {
	pub entries: Vector<E>,
	pub level: usize,
}

impl<E: Clone> Env<E> {
	pub fn empty() -> Self {
		Env { entries: Vector::new(), level: 0 }
	}

	pub fn new<T: IntoIterator<Item = E>>(entries: T) -> Self {
		let entries = Vector::from_iter(entries);
		let level = entries.len();
		Env { entries, level }
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
}

impl<E: Clone> Env<E> {
	pub fn append<T: IntoIterator<Item = E>>(&self, entries_iter: T) -> Env<E> {
		let mut entries = self.entries.clone();
		entries.extend(entries_iter);
		Env { entries, level: self.level }
	}

	pub fn shift_to(&self, level: usize) -> Self {
		Env { entries: self.entries.clone(), level }
	}

	pub fn shift(&self, amount: usize) -> (Self, Vector<VL>) {
		(
			Env { entries: self.entries.clone(), level: self.level + amount },
			(0..amount).map(move |l| VL(self.level + l)).collect(),
		)
	}
}

impl Env<Entry> {
	pub fn get_var(&self, level: VL) -> VL {
		self.get(level).var()
	}

	pub fn eval_args(&self, args: Vector<VL>) -> Vector<VL> {
		args.into_iter().map(|arg| self.get_var(arg)).collect()
	}

	pub fn extend(&self, types: impl IntoIterator<Item = DataType>) -> Env<Entry> {
		let new_entries = Vector::from_iter(
			types.into_iter().enumerate().map(|(l, ty)| Entry::Value(VL(self.level + l), ty)),
		);
		let level = self.level + new_entries.len();
		let mut entries = self.entries.clone();
		entries.append(new_entries);
		Env { entries, level }
	}
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Expr<R> {
	Var(VL),
	Op(String, Vec<Expr<R>>),
	Agg(String, Box<R>),
}

impl<U: Display> Display for Expr<U> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Expr::Var(v) => write!(f, "{}", v),
			Expr::Op(op, args) if args.is_empty() => write!(f, "\"{}\"", op),
			Expr::Op(op, args) => {
				write!(f, "{}({})", op, args.iter().map(|arg| format!("{}", arg)).join(", "))
			},
			Expr::Agg(op, arg) => write!(f, "{}{}", op, arg),
		}
	}
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Predicate<R> {
	Eq(Expr<R>, Expr<R>),
	Pred(String, Vec<Expr<R>>),
	Like(Expr<R>, String),
	Null(Expr<R>),
}

impl<R: Display> Display for Predicate<R> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Predicate::Eq(e1, e2) => write!(f, "{} = {}", e1, e2),
			Predicate::Pred(p, args) => match p.as_str() {
				"<" | ">" | "<=" | ">=" => write!(f, "{} {} {}", args[0], p, args[1]),
				_ => {
					write!(f, "{}({})", p, args.iter().map(|arg| format!("{}", arg)).join(", "))
				},
			},
			Predicate::Like(e, pat) => write!(f, "Like({}, {})", e, pat),
			Predicate::Null(e) => write!(f, "Null({})", e),
		}
	}
}

#[derive(Debug, Clone, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Schema {
	pub types: Vec<DataType>,
	#[serde(skip)] // TODO: Multiple primary keys
	#[serde(rename = "primary_key")]
	pub primary: Option<usize>,
	#[serde(skip)]
	#[serde(rename = "foreign_key")]
	pub foreign: HashMap<usize, VL>,
}

pub trait Eval<T> {
	fn eval(self, env: &Env<Entry>) -> T;
}

impl<T, R: Eval<T>> Eval<Predicate<T>> for Predicate<R> {
	fn eval(self, env: &Env<Entry>) -> Predicate<T> {
		use Predicate::*;
		match self {
			Eq(v1, v2) => Eq(v1.eval(env), v2.eval(env)),
			Pred(r, args) => Pred(r, args.into_iter().map(|v| v.eval(env)).collect()),
			Like(v, s) => Like(v.eval(env), s),
			Null(v) => Null(v.eval(env)),
		}
	}
}

impl<T, R: Eval<T>> Eval<Expr<T>> for Expr<R> {
	fn eval(self, env: &Env<Entry>) -> Expr<T> {
		use Expr::*;
		match self {
			Var(l) => Var(env.get_var(l)),
			Op(f, args) => Op(f, args.into_iter().map(|v| v.eval(env)).collect()),
			Agg(f, arg) => Agg(f, Box::new(arg.eval(env))),
		}
	}
}

impl<T, U: Eval<T>> Eval<Relation<T>> for Relation<U> {
	fn eval(self, env: &Env<Entry>) -> Relation<T> {
		use Relation::*;
		match self {
			Var(l) => Var(env.get_var(l)),
			Lam(types, body) => Relation::lam(types.clone(), body.eval(&env.extend(types))),
		}
	}
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Relation<U> {
	Var(VL),
	Lam(Vector<DataType>, Box<U>),
}

impl<U> Relation<U> {
	pub fn lam<T: Into<Box<U>>>(types: impl IntoIterator<Item = DataType>, body: T) -> Self {
		Relation::Lam(types.into_iter().collect(), body.into())
	}

	pub fn types(&self, schemas: &Env<Schema>) -> Vector<DataType> {
		match self {
			Relation::Var(table) => schemas.get(*table).types.clone().into(),
			Relation::Lam(types, _) => types.clone(),
		}
	}
}

impl<U: Display> Display for Relation<U> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Relation::Var(table) => write!(f, "#{}", table.0),
			Relation::Lam(types, body) => {
				writeln!(f, "(λ {:?}", types)?;
				writeln!(indented(f).with_str("\t"), "{}", body)?;
				write!(f, ")")
			},
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
	#[serde(alias = "INTEGER")]
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
	#[serde(alias = "VARCHAR", alias = "CHAR")]
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

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Application {
	pub table: VL,
	pub args: Vector<VL>,
}

impl Application {
	pub fn new(table: VL, args: Vector<VL>) -> Self {
		Application { table, args }
	}
}

impl Display for Application {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"#{}({})",
			self.table.0,
			self.args.iter().map(|arg| format!("{}", arg)).join(", ")
		)
	}
}

impl Eval<Application> for Application {
	fn eval(mut self, env: &Env<Entry>) -> Application {
		self.table = env.get_var(self.table);
		self.args.iter_mut().for_each(|a| *a = env.get_var(*a));
		self
	}
}
