use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Write};
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::{Add, Mul, Not};
use std::time::Duration;

use anyhow::bail;
use imbl::vector::{ConsumingIter, Iter};
use imbl::{vector, Vector};
use indenter::indented;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use serde_enum_str::{Deserialize_enum_str, Serialize_enum_str};
use z3::ast::{Ast, Dynamic};
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
	#[serde(rename = "nullable")]
	#[serde(default)]
	pub nullabilities: Vec<bool>,
	#[serde(default)]
	pub guaranteed: Vec<super::relation::Expr>,
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Expr<U, R, A> {
	Var(VL, DataType),
	Log(Box<Logic<U, Expr<U, R, A>>>),
	Agg(A),
	Op(String, Vec<Expr<U, R, A>>, DataType),
	HOp(String, Vec<Expr<U, R, A>>, Box<R>, DataType),
}

pub trait Typed {
	fn ty(&self) -> DataType;
}

impl<U, R, A: Typed> Typed for Expr<U, R, A> {
	fn ty(&self) -> DataType {
		use Expr::*;
		match self {
			Var(_, ty) | Op(_, _, ty) | HOp(_, _, _, ty) => ty.clone(),
			Log(_) => DataType::Boolean,
			Agg(agg) => agg.ty(),
		}
	}
}

impl<U, R, A: Typed> Expr<U, R, A> {
	pub fn is_null(self) -> Logic<U, Self> {
		Logic::Eq(Self::Op("NULL".to_string(), vec![], self.ty()), self)
	}
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Lambda<U>(pub Vector<DataType>, pub U);

impl<U: Display> Display for Lambda<U> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		writeln!(f, "(λ {:?}", self.0)?;
		writeln!(indented(f).with_str("\t"), "{})", self.1)
	}
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Sigma<U>(pub Vector<DataType>, pub U);

impl<U: Display> Display for Sigma<U> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		writeln!(f, "∑ {:?} {{", self.0)?;
		writeln!(indented(f).with_str("\t"), "{}", self.1)?;
		writeln!(f, "}}")
	}
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Logic<U, E> {
	Bool(E),
	Eq(E, E),
	Pred(String, Vec<E>),
	Neg(Box<Logic<U, E>>),
	And(Vector<Logic<U, E>>),
	Or(Vector<Logic<U, E>>),
	Squash(Box<U>),
}

impl<U, E> Logic<U, E> {
	pub fn tt() -> Self {
		Logic::And(vector![])
	}

	pub fn ff() -> Self {
		Logic::Or(vector![])
	}

	pub fn squash(u: impl Into<Box<U>>) -> Self {
		Logic::Squash(u.into())
	}
}

impl<U: Clone, E: Clone> Mul for Logic<U, E> {
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

impl<U: Clone, E: Clone> Add for Logic<U, E> {
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

impl<U, E> Not for Logic<U, E> {
	type Output = Self;

	fn not(self) -> Self::Output {
		Logic::Neg(Box::new(self))
	}
}

impl<E: Display, U: Display> Display for Logic<U, E> {
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
			Squash(u) => write!(f, "{}", u),
		}
	}
}

impl<Env, U: Clone, V: Clone, S: Clone, T: Clone> Eval<Logic<U, S>, Logic<V, T>> for Env
where Env: Eval<S, T> + Eval<U, V> + Clone
{
	fn eval(self, source: Logic<U, S>) -> Logic<V, T> {
		use Logic::*;
		match source {
			Bool(e) => Bool(self.eval(e)),
			Eq(e1, e2) => Eq(self.clone().eval(e1), self.eval(e2)),
			Pred(p, args) => Pred(p, self.eval(args)),
			Neg(l) => Neg(self.eval(l)),
			And(ls) => And(self.eval(ls)),
			Or(ls) => Or(self.eval(ls)),
			Squash(u) => Squash(self.eval(u)),
		}
	}
}

impl<U: Clone, R: Clone, A: Clone> Expr<U, R, A> {
	pub fn vars(level: usize, scope: Vector<DataType>) -> Vector<Self> {
		scope.into_iter().enumerate().map(|(l, ty)| Expr::Var(VL(level + l), ty)).collect()
	}
}

impl<U: Display, R: Display, A: Display> Display for Expr<U, R, A> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Expr::Var(v, _) => write!(f, "{}", v),
			Expr::Log(u) => write!(f, "‖{}‖", u),
			Expr::Agg(agg) => write!(f, "{}", agg),
			Expr::Op(op, args, _) if args.is_empty() => write!(f, "\"{}\"", op),
			Expr::Op(op, args, _) => {
				write!(f, "{}({})", op, args.iter().join(", "))
			},
			Expr::HOp(op, args, rel, _) => write!(f, "{}({}, {})", op, args.iter().join(", "), rel),
		}
	}
}

impl<U, R, A> From<u32> for Expr<U, R, A> {
	fn from(n: u32) -> Self {
		Expr::Op(n.to_string(), vec![], DataType::Integer)
	}
}

impl<U, R, A> From<usize> for Expr<U, R, A> {
	fn from(n: usize) -> Self {
		Expr::Op(n.to_string(), vec![], DataType::Integer)
	}
}

impl<U, R, A> From<String> for Expr<U, R, A> {
	fn from(s: String) -> Self {
		Expr::Op(s, vec![], DataType::String)
	}
}

impl<Env, U: Clone, V: Clone, R: Clone, S: Clone, A: Clone, B: Clone>
	Eval<Expr<U, R, A>, Expr<V, S, B>> for Env
where Env: Eval<(VL, DataType), Expr<V, S, B>>
		+ Eval<U, V>
		+ Eval<R, S>
		+ Eval<A, Expr<V, S, B>>
		+ Clone
{
	fn eval(self, source: Expr<U, R, A>) -> Expr<V, S, B> {
		use Expr::*;
		match source {
			Var(l, ty) => self.eval((l, ty)),
			Log(l) => Log(self.eval(l)),
			Agg(agg) => self.eval(agg),
			Op(f, args, ty) => Op(f, self.eval(args), ty),
			HOp(f, args, rel, ty) => HOp(f, self.clone().eval(args), self.eval(rel), ty),
		}
	}
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Head<R, E> {
	Var(VL),
	HOp(String, Vec<E>, Box<R>),
}

impl<R: Display, E: Display> Display for Head<R, E> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Head::Var(VL(l)) => write!(f, "#{}", l),
			Head::HOp(op, op_args, rel) => {
				writeln!(f, "#{}({}, {})", op, op_args.iter().format(", "), rel)
			},
		}
	}
}

impl<Env, R: Clone, S: Clone, E: Clone, F: Clone> Eval<Head<R, E>, Head<S, F>> for Env
where Env: Eval<R, S> + Eval<Vec<E>, Vec<F>> + Clone
{
	fn eval(self, source: Head<R, E>) -> Head<S, F> {
		use Head::*;
		match source {
			Var(v) => Var(v),
			HOp(op, args, rel) => HOp(op, self.clone().eval(args), self.eval(*rel).into()),
		}
	}
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Neutral<R, E>(pub Head<R, E>, pub Vector<E>);

impl<R: Display, E: Display> Display for Neutral<R, E> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}({})", self.0, self.1.iter().format(", "))
	}
}

impl<Env, R: Clone, S: Clone, E: Clone, F: Clone> Eval<Neutral<R, E>, Neutral<S, F>> for Env
where Env: Eval<Head<R, E>, Head<S, F>> + Eval<Vector<E>, Vector<F>> + Clone
{
	fn eval(self, Neutral(head, args): Neutral<R, E>) -> Neutral<S, F> {
		let head = self.clone().eval(head);
		let args = self.eval(args);
		Neutral(head, args)
	}
}

/// SQL data types (adapted from sqlparser)
#[derive(
	Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize_enum_str, Deserialize_enum_str,
)]
#[serde(rename_all = "UPPERCASE")]
pub enum DataType {
	/// Integer
	#[serde(alias = "INT", alias = "SMALLINT", alias = "BIGINT", alias = "TINYINT")]
	#[serde(alias = "TIMESTAMP", alias = "DATE", alias = "TIME")]
	Integer,
	/// Real number
	#[serde(alias = "FLOAT", alias = "DOUBLE", alias = "DECIMAL")]
	Real,
	/// Boolean
	#[serde(alias = "BOOL")]
	Boolean,
	/// String
	#[serde(alias = "VARCHAR", alias = "CHAR", alias = "TEXT")]
	String,
	/// Custom type such as enums
	#[serde(other)]
	Custom(String),
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
		let z3_ctx = self.z3_ctx();
		use DataType::*;
		match ty {
			Boolean => self.bool.sort.clone(),
			String => self.string.sort.clone(),
			Integer => self.int.sort.clone(),
			Real => self.real.sort.clone(),
			Custom(ty) => Sort::uninterpreted(z3_ctx, z3::Symbol::String(ty.clone())),
		}
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
		Dynamic::fresh_const(self.solver.get_context(), prefix, &self.sort(ty))
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

	pub fn timeout() -> Duration {
		if let Some(t) =
			std::env::var("COSETTE_SMT_TIMEOUT").ok().and_then(|t| t.parse::<u64>().ok())
		{
			Duration::from_millis(t)
		} else {
			Duration::from_secs(10)
		}
	}
}
