use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Write};
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::{Add, Mul, Not};

use anyhow::bail;
use imbl::vector::{ConsumingIter, Iter};
use imbl::{vector, Vector};
use indenter::indented;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use z3::ast::{Ast, Datatype, Dynamic};
use z3::{Context, FuncDecl, Sort};

pub trait Eval<S, T> {
	fn eval(self, source: S) -> T;
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct VL(pub usize);

impl Display for VL {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "${}", self.0)
	}
}

#[derive(Debug, Clone, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Schema {
	pub types: Vec<DataType>,
	#[serde(rename = "key")]
	pub primary: Vec<HashSet<usize>>,
	#[serde(skip)]
	#[serde(rename = "foreign_key")]
	pub foreign: HashMap<usize, VL>,
	#[serde(rename = "strategy")]
	#[serde(default)]
	pub constraints: Vec<Constraint>,
	#[serde(default)]
	pub guaranteed: Vec<super::relation::Expr>,
}

#[derive(Debug, Clone, Default, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum Constraint {
	NotNullable,
	#[default]
	#[serde(other)]
	Nullable,
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Expr<R> {
	Var(VL, DataType),
	Op(String, Vec<Expr<R>>, DataType),
	HOp(String, Vec<Expr<R>>, Box<R>, DataType),
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Lambda<U>(pub Vector<DataType>, pub U);

impl<U: Display> Display for Lambda<U> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		writeln!(f, "(λ {:?}", self.0)?;
		writeln!(indented(f).with_str("\t"), "{})", self.1)
	}
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Logic<R, L, A> {
	Bool(Expr<R>),
	Eq(Expr<R>, Expr<R>),
	Pred(String, Vec<Expr<R>>),
	Neg(Box<Logic<R, L, A>>),
	And(Vector<Logic<R, L, A>>),
	Or(Vector<Logic<R, L, A>>),
	App(A),
	Exists(L),
}

impl<R, L, A> Logic<R, L, A> {
	pub fn tt() -> Self {
		Logic::And(vector![])
	}

	pub fn ff() -> Self {
		Logic::Or(vector![])
	}

	pub fn is_null(expr: Expr<R>) -> Self {
		let ty = expr.ty();
		Self::Eq(expr, Expr::Op("NULL".to_string(), vec![], ty))
	}
}

impl<R: Clone, L: Clone, A: Clone> Mul for Logic<R, L, A> {
	type Output = Self;

	fn mul(self, rhs: Self) -> Self::Output {
		use Logic::*;
		match (self, rhs) {
			(And(ls1), And(ls2)) => And(ls1 + ls2),
			(And(ls1), l2) => And(ls1 + vector![l2]),
			(l1, And(ls2)) => And(vector![l1] + ls2),
			(l1, l2) => And(vector![l1, l2]),
		}
	}
}

impl<R: Clone, L: Clone, A: Clone> Add for Logic<R, L, A> {
	type Output = Self;

	fn add(self, rhs: Self) -> Self::Output {
		use Logic::*;
		match (self, rhs) {
			(Or(ls1), Or(ls2)) => Or(ls1 + ls2),
			(Or(ls1), l2) => Or(ls1 + vector![l2]),
			(l1, Or(ls2)) => Or(vector![l1] + ls2),
			(l1, l2) => Or(vector![l1, l2]),
		}
	}
}

impl<R, L, A> Not for Logic<R, L, A> {
	type Output = Self;

	fn not(self) -> Self::Output {
		Logic::Neg(Box::new(self))
	}
}

impl<R: Display, L: Display, A: Display> Display for Logic<R, L, A> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		use Logic::*;
		match self {
			Bool(e) => write!(f, "{}", e),
			Eq(e1, e2) => write!(f, "({} = {})", e1, e2),
			Pred(p, args) => write!(f, "{}({})", p, args.iter().join(", ")),
			Neg(l) => write!(f, "¬{}", l),
			And(ls) if ls.is_empty() => write!(f, "true"),
			And(ls) => write!(f, "({})", ls.iter().format(" ∧ ")),
			Or(ls) if ls.is_empty() => write!(f, "false"),
			Or(ls) => write!(f, "({})", ls.iter().format(" ∨ ")),
			App(app) => write!(f, "{}", app),
			Exists(rel) => write!(f, "∃({})", rel),
		}
	}
}

impl<E, S, T, L, M, A, B> Eval<Logic<S, L, A>, Logic<T, M, B>> for E
where
	E: Eval<Expr<S>, Expr<T>> + Eval<L, M> + Eval<A, Logic<T, M, B>> + Clone,
	S: Clone,
	T: Clone,
	L: Clone,
	M: Clone,
	A: Clone,
	B: Clone,
{
	fn eval(self, source: Logic<S, L, A>) -> Logic<T, M, B> {
		use Logic::*;
		match source {
			Bool(e) => Bool(self.eval(e)),
			Eq(e1, e2) => Eq(self.clone().eval(e1), self.eval(e2)),
			Pred(p, args) => Pred(p, self.eval(args)),
			Neg(l) => Neg(self.eval(l)),
			And(ls) => And(self.eval(ls)),
			Or(ls) => Or(self.eval(ls)),
			App(app) => self.eval(app),
			Exists(rel) => Exists(self.eval(rel)),
		}
	}
}

impl<R> Expr<R> {
	pub fn ty(&self) -> DataType {
		use Expr::*;
		match self {
			Var(_, ty) | Op(_, _, ty) | HOp(_, _, _, ty) => ty.clone(),
		}
	}
}

impl<R: Clone> Expr<R> {
	pub fn vars(level: usize, scopes: Vector<DataType>) -> Vector<Expr<R>> {
		scopes.into_iter().enumerate().map(|(l, ty)| Expr::<R>::Var(VL(level + l), ty)).collect()
	}
}

impl<R: Display> Display for Expr<R> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Expr::Var(v, _) => write!(f, "{}", v),
			Expr::Op(op, args, _) if args.is_empty() => write!(f, "\"{}\"", op),
			Expr::Op(op, args, _) => {
				write!(f, "{}({})", op, args.iter().join(", "))
			},
			Expr::HOp(op, args, rel, _) => write!(f, "{}({}, {})", op, args.iter().join(", "), rel),
		}
	}
}

impl<U> From<u32> for Expr<U> {
	fn from(n: u32) -> Self {
		Expr::Op(n.to_string(), vec![], DataType::Integer)
	}
}

impl<U> From<usize> for Expr<U> {
	fn from(n: usize) -> Self {
		Expr::Op(n.to_string(), vec![], DataType::Integer)
	}
}

impl<U> From<String> for Expr<U> {
	fn from(s: String) -> Self {
		Expr::Op(s, vec![], DataType::String)
	}
}

impl<E, S, T> Eval<Expr<S>, Expr<T>> for E
where E: Eval<(VL, DataType), Expr<T>> + Eval<S, T> + Clone
{
	fn eval(self, source: Expr<S>) -> Expr<T> {
		use Expr::*;
		match source {
			Var(l, ty) => self.eval((l, ty)),
			Op(f, args, ty) => Op(f, self.eval(args), ty),
			HOp(f, args, rel, ty) => HOp(f, self.clone().eval(args), self.eval(rel), ty),
		}
	}
}

impl<E, S: Clone, T: Clone> Eval<Neutral<S>, Neutral<T>> for E
where E: Eval<Head<S>, Head<T>> + Eval<Vector<Expr<S>>, Vector<Expr<T>>> + Clone
{
	fn eval(self, source: Neutral<S>) -> Neutral<T> {
		let head = self.clone().eval(source.head);
		let args = self.eval(source.args);
		Neutral { head, args }
	}
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Relation<U>(pub Vector<DataType>, pub Box<U>);

impl<U: Display> Display for Relation<U> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		writeln!(f, "λ {:?}", self.0)?;
		writeln!(indented(f).with_str("\t"), "{}", self.1)
	}
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Head<R> {
	Var(VL),
	HOp(String, Vec<Expr<R>>, Box<R>),
}

impl<R: Display> Display for Head<R> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Head::Var(VL(l)) => write!(f, "#{}", l),
			Head::HOp(op, op_args, rel) => {
				writeln!(f, "#{}({}, {})", op, op_args.iter().format(", "), rel)
			},
		}
	}
}

impl<E, S: Clone, T: Clone> Eval<Head<S>, Head<T>> for E
where E: Eval<Vec<Expr<S>>, Vec<Expr<T>>> + Eval<Box<S>, Box<T>> + Clone
{
	fn eval(self, source: Head<S>) -> Head<T> {
		use Head::*;
		match source {
			Var(v) => Var(v),
			HOp(op, args, rel) => HOp(op, self.clone().eval(args), self.eval(rel)),
		}
	}
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Neutral<R> {
	pub head: Head<R>,
	pub args: Vector<Expr<R>>,
}

impl<R> Neutral<R> {
	pub fn new(head: Head<R>, args: Vector<Expr<R>>) -> Self {
		Neutral { head, args }
	}
}

impl<R: Display> Display for Neutral<R> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}({})", self.head, self.args.iter().format(", "))
	}
}

/// SQL data types (adapted from sqlparser)
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "UPPERCASE")]
pub enum DataType {
	/// Uuid type
	Uuid,
	/// Integer
	#[serde(alias = "INT", alias = "SMALLINT", alias = "BIGINT", alias = "TINYINT")]
	#[serde(alias = "TIMESTAMP", alias = "DATE", alias = "TIME")]
	Integer,
	/// Real number
	#[serde(alias = "FLOAT", alias = "DOUBLE", alias = "DECIMAL")]
	Real,
	/// Boolean
	Boolean,
	/// Interval
	Interval,
	/// Regclass used in postgresql serial
	Regclass,
	/// String
	#[serde(alias = "VARCHAR", alias = "CHAR", alias = "TEXT")]
	String,
	/// Custom type such as enums
	Custom(String),
	/// Arrays
	Array(Box<DataType>),
	/// Any type
	#[serde(other)]
	Any,
}

#[derive(Clone, Debug, Default, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Terms<T>(pub Vector<T>);

impl<T> Terms<T> {
	pub fn zero() -> Self {
		Terms(vector![])
	}

	pub fn iter(&self) -> Iter<'_, T> {
		self.0.iter()
	}
}

impl<T: Clone> Terms<T> {
	pub fn term(term: T) -> Self {
		Terms(vector![term])
	}

	pub fn into_iter(self) -> ConsumingIter<T> {
		self.0.into_iter()
	}
}

impl<T: Clone + Default> Terms<T> {
	pub fn one() -> Self {
		Terms::term(T::default())
	}
}

impl<T: Clone> IntoIterator for Terms<T> {
	type Item = T;
	type IntoIter = ConsumingIter<T>;

	fn into_iter(self) -> Self::IntoIter {
		self.into_iter()
	}
}

impl<'a, T> IntoIterator for &'a Terms<T> {
	type Item = &'a T;
	type IntoIter = Iter<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.iter()
	}
}

impl<T: Clone> FromIterator<T> for Terms<T> {
	fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
		Terms(iter.into_iter().collect())
	}
}

impl<T: Clone> Add for Terms<T> {
	type Output = Terms<T>;

	fn add(self, rhs: Self) -> Self::Output {
		Terms(self.0 + rhs.0)
	}
}

impl<T: Clone + Mul> Mul for Terms<T>
where T::Output: Clone
{
	type Output = Terms<T::Output>;

	fn mul(self, rhs: Self) -> Self::Output {
		self.into_iter().flat_map(|t1| rhs.iter().map(move |t2| t1.clone() * t2.clone())).collect()
	}
}

impl<T: Clone + Mul> Mul<T> for Terms<T>
where T::Output: Clone
{
	type Output = Terms<T::Output>;

	fn mul(self, rhs: T) -> Self::Output {
		self.into_iter().map(|term| term * rhs.clone()).collect()
	}
}

impl<T: Display> Display for Terms<T> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.iter().join("\n+ "))
	}
}

impl<E, S: Clone, T: Clone> Eval<Vector<S>, Vector<T>> for E
where E: Eval<S, T> + Clone
{
	fn eval(self, source: Vector<S>) -> Vector<T> {
		source.into_iter().map(|item| self.clone().eval(item)).collect()
	}
}

impl<'a, E, S: Clone, T: Clone> Eval<&'a Vector<S>, Vector<T>> for E
where E: Eval<&'a S, T> + Clone
{
	fn eval(self, source: &'a Vector<S>) -> Vector<T> {
		source.iter().map(|item| self.clone().eval(item)).collect()
	}
}

impl<E, S, T> Eval<Vec<S>, Vec<T>> for E
where E: Eval<S, T> + Clone
{
	fn eval(self, source: Vec<S>) -> Vec<T> {
		source.into_iter().map(|item| self.clone().eval(item)).collect()
	}
}

impl<E, S, T> Eval<Box<S>, Box<T>> for E
where E: Eval<S, T>
{
	fn eval(self, source: Box<S>) -> Box<T> {
		self.eval(*source).into()
	}
}

impl<E, S, T> Eval<Option<S>, Option<T>> for E
where E: Eval<S, T>
{
	fn eval(self, source: Option<S>) -> Option<T> {
		source.map(|item| self.eval(item))
	}
}

pub use super::null::Ctx;

impl<'c> Ctx<'c> {
	pub fn z3_ctx(&self) -> &'c Context {
		self.solver.get_context()
	}

	pub fn none(&self, ty: &DataType) -> anyhow::Result<Dynamic<'c>> {
		use DataType::*;
		Ok(match ty {
			Integer => self.int_none(),
			Real => self.real_none(),
			Boolean => self.bool_none(),
			String => self.string_none(),
			_ => bail!("unsupported type {:?} for null", ty),
		})
	}

	pub fn sort(&self, ty: &DataType) -> Sort<'c> {
		use DataType::*;
		match ty {
			Boolean => &self.bool.sort,
			String => &self.string.sort,
			Integer => &self.int.sort,
			Real => &self.real.sort,
			_ => panic!("unsupported type {:?}", ty),
		}
		.clone()
	}

	pub fn strict_sort(&self, ty: &DataType) -> Sort<'c> {
		let z3_ctx = self.z3_ctx();
		use DataType::*;
		match ty {
			Boolean => Sort::bool(z3_ctx),
			String => Sort::string(z3_ctx),
			Integer => Sort::int(z3_ctx),
			Real => Sort::real(z3_ctx),
			_ => panic!("unsupported type {:?}", ty),
		}
	}

	pub fn var(&self, ty: &DataType, prefix: &str) -> Dynamic<'c> {
		Datatype::fresh_const(self.solver.get_context(), prefix, &self.sort(ty)).into()
	}

	pub fn app(
		&self,
		name: &str,
		args: &[&Dynamic<'c>],
		range: &DataType,
		nullable: bool,
	) -> Dynamic<'c> {
		let ctx = self.solver.get_context();
		let domain = args.iter().map(|arg| arg.get_sort()).collect_vec();
		let args = args.iter().map(|&arg| arg as &dyn Ast).collect_vec();
		let range = if nullable { self.sort(range) } else { self.strict_sort(range) };
		let f = FuncDecl::new(ctx, name, &domain.iter().collect_vec(), &range);
		f.apply(&args)
	}
}
