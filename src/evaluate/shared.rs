use std::collections::{HashMap, VecDeque};
use std::fmt::{Debug, Display, Formatter, Write};
use std::hash::Hash;
use std::iter::FromIterator;

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
#[derive(Debug, Clone, Default, Ord, PartialOrd, Eq, PartialEq)]
pub struct Env<E> {
	pub entries: VecDeque<E>,
	pub level: usize,
}

impl<E> Env<E> {
	pub fn empty() -> Self {
		Env { entries: VecDeque::new(), level: 0 }
	}

	pub fn new<T: IntoIterator<Item = E>>(entries: T) -> Self {
		let entries = VecDeque::from_iter(entries);
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

	pub fn shift_to(mut self, level: usize) -> Self {
		self.level = level;
		self
	}
}

impl<E: Clone> Env<E> {
	pub fn append<T: IntoIterator<Item = E>>(&self, entries_iter: T) -> Env<E> {
		let mut entries = self.entries.clone();
		entries.extend(entries_iter);
		Env { entries, level: self.level }
	}
}

impl Env<Entry> {
	pub fn get_var(&self, level: VL) -> VL {
		self.get(level).var()
	}

	pub fn eval_args(&self, args: Vec<VL>) -> Vec<VL> {
		args.into_iter().map(|arg| self.get_var(arg)).collect()
	}

	pub fn append_vars(&self, types: Vec<DataType>) -> Env<Entry> {
		let level = self.level + types.len();
		let mut entries = self.entries.clone();
		entries.extend(
			types.into_iter().enumerate().map(|(l, ty)| Entry::Value(VL(self.level + l), ty)),
		);
		Env { entries, level }
	}
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Expr<U> {
	Var(VL),
	Op(String, Vec<Expr<U>>),
	Agg(String, Box<Relation<U>>),
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
pub enum Predicate<U> {
	Eq(Expr<U>, Expr<U>),
	Pred(String, Vec<Expr<U>>),
	Like(Expr<U>, String),
	Null(Expr<U>),
}

impl<U: Display> Display for Predicate<U> {
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

pub trait Eval {
	type Output;

	fn eval(self, env: &Env<Entry>) -> Self::Output;
}

impl<U: Eval> Eval for Predicate<U> {
	type Output = Predicate<U::Output>;

	fn eval(self, env: &Env<Entry>) -> Self::Output {
		use Predicate::*;
		match self {
			Eq(v1, v2) => Eq(v1.eval(env), v2.eval(env)),
			Pred(r, args) => Pred(r, args.into_iter().map(|v| v.eval(env)).collect()),
			Like(v, s) => Like(v.eval(env), s),
			Null(v) => Null(v.eval(env)),
		}
	}
}

impl<U: Eval> Eval for Expr<U> {
	type Output = Expr<U::Output>;

	fn eval(self, env: &Env<Entry>) -> Self::Output {
		use Expr::*;
		match self {
			Var(l) => Var(env.get_var(l)),
			Op(f, args) => Op(f, args.into_iter().map(|v| v.eval(env)).collect()),
			Agg(f, arg) => Agg(f, Box::new(arg.eval(env))),
		}
	}
}

impl<U: Eval> Eval for Relation<U> {
	type Output = Relation<U::Output>;

	fn eval(self, env: &Env<Entry>) -> Self::Output {
		use Relation::*;
		match self {
			Var(l) => Var(env.get_var(l)),
			Lam(types, body) => Relation::lam(types.clone(), body.eval(&env.append_vars(types))),
		}
	}
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Relation<U> {
	Var(VL),
	Lam(Vec<DataType>, Box<U>),
}

impl<U> Relation<U> {
	pub fn lam<T: Into<Box<U>>>(types: Vec<DataType>, body: T) -> Self {
		Relation::Lam(types, body.into())
	}

	pub fn types(&self, schemas: &Env<Schema>) -> Vec<DataType> {
		match self {
			Relation::Var(table) => schemas.get(*table).types.clone(),
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
	#[serde(alias="INTEGER")]
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

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Application {
	pub table: VL,
	pub args: Vec<VL>,
}

impl Application {
	pub fn new(table: VL, args: Vec<VL>) -> Self {
		Application { table, args }
	}
}

impl Display for Application {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}({})", self.table, self.args.iter().map(|arg| format!("{}", arg)).join(", "))
	}
}

impl Eval for Application {
	type Output = Application;

	fn eval(mut self, env: &Env<Entry>) -> Self::Output {
		self.table = env.get_var(self.table);
		self.args.iter_mut().for_each(|a| *a = env.get_var(*a));
		self
	}
}
