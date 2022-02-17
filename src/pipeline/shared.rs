use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Write};
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::{Add, Mul};

use imbl::vector::{ConsumingIter, Iter};
use imbl::{vector, Vector};
use indenter::indented;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use z3::ast::{Ast, Dynamic};
use z3::{ast, Context, FuncDecl, Solver, Sort};

use crate::pipeline::null::Nullable;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct VL(pub usize);

impl Display for VL {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "${}", self.0)
	}
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Expr<R> {
	Var(VL, DataType),
	Op(String, Vec<Expr<R>>, DataType),
	HOp(String, Vec<Expr<R>>, Box<R>, DataType),
}

impl<R> Expr<R> {
	pub fn ty(&self) -> DataType {
		match self {
			Expr::Var(_, ty) => ty,
			Expr::Op(_, _, ty) => ty,
			Expr::HOp(_, _, _, ty) => ty,
		}
		.clone()
	}
}

impl<R: Clone> Expr<R> {
	pub fn vars(level: usize, scopes: Vector<DataType>) -> Vector<Expr<R>> {
		scopes.into_iter().enumerate().map(|(l, ty)| Expr::<R>::Var(VL(level + l), ty)).collect()
	}
}

impl<U: Display> Display for Expr<U> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Expr::Var(v, _) => write!(f, "{}", v),
			Expr::Op(op, args, _) if args.is_empty() => write!(f, "\"{}\"", op),
			Expr::Op(op, args, _) => {
				write!(f, "{}({})", op, args.iter().map(|arg| format!("{}", arg)).join(", "))
			},
			Expr::HOp(op, args, rel, _) => write!(
				f,
				"{}({}, {})",
				op,
				args.iter().map(|arg| format!("{}", arg)).join(", "),
				rel
			),
		}
	}
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Predicate<R> {
	Eq(Expr<R>, Expr<R>),
	Pred(String, Vec<Expr<R>>),
	Like(Expr<R>, String),
	Null(Expr<R>),
	Bool(Expr<R>),
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
			Predicate::Bool(e) => write!(f, "{}", e),
		}
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
}

pub trait Eval<S, T> {
	fn eval(self, source: S) -> T;
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

impl<E, S, T> Eval<Predicate<S>, Predicate<T>> for E
where E: Eval<Expr<S>, Expr<T>> + Clone
{
	fn eval(self, source: Predicate<S>) -> Predicate<T> {
		use Predicate::*;
		match source {
			Eq(v1, v2) => Eq(self.clone().eval(v1), self.eval(v2)),
			Pred(r, args) => Pred(r, args.into_iter().map(|v| self.clone().eval(v)).collect()),
			Like(v, s) => Like(self.eval(v), s),
			Null(v) => Null(self.eval(v)),
			Bool(v) => Bool(self.eval(v)),
		}
	}
}

impl<E, S: Clone, T: Clone> Eval<AppHead<S>, AppHead<T>> for E
where E: Eval<Vec<Expr<S>>, Vec<Expr<T>>> + Eval<Box<S>, Box<T>> + Clone
{
	fn eval(self, source: AppHead<S>) -> AppHead<T> {
		use AppHead::*;
		match source {
			Var(v) => Var(v),
			HOp(op, args, rel) => HOp(op, self.clone().eval(args), self.eval(rel)),
		}
	}
}

impl<E, S: Clone, T: Clone> Eval<Application<S>, Application<T>> for E
where E: Eval<AppHead<S>, AppHead<T>> + Eval<Vector<Expr<S>>, Vector<Expr<T>>> + Clone
{
	fn eval(self, source: Application<S>) -> Application<T> {
		let head = self.clone().eval(source.head);
		let args = self.eval(source.args);
		Application { head, args }
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

impl<E, S: Clone, T: Clone> Eval<Terms<S>, Terms<T>> for E
where E: Eval<S, T> + Clone
{
	fn eval(self, source: Terms<S>) -> Terms<T> {
		source.into_iter().map(|item| self.clone().eval(item)).collect()
	}
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Relation<U> {
	Var(VL),
	Lam(Vector<DataType>, Box<U>),
	HOp(String, Vec<Expr<Relation<U>>>, Box<Relation<U>>),
}

impl<U> Relation<U> {
	pub fn lam(scopes: impl IntoIterator<Item = DataType>, body: U) -> Self {
		Relation::Lam(scopes.into_iter().collect(), Box::new(body))
	}

	pub fn scopes(&self, schemas: &Vector<Schema>) -> Vector<DataType> {
		match self {
			Relation::Var(table) => schemas[table.0].types.clone().into(),
			Relation::Lam(scopes, _) => scopes.clone(),
			Relation::HOp(_, _, rel) => rel.scopes(schemas),
		}
	}
}

impl<U: Display> Display for Relation<U> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Relation::Var(table) => write!(f, "#{}", table.0),
			Relation::Lam(scopes, body) => {
				writeln!(f, "λ {:?}", scopes)?;
				writeln!(indented(f).with_str("\t"), "{}", body)
			},
			Relation::HOp(op, args, rel) => {
				writeln!(
					f,
					"{}({}, {})",
					op,
					args.iter().map(|arg| format!("{}", arg)).join(", "),
					rel
				)
			},
		}
	}
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum AppHead<R> {
	Var(VL),
	HOp(String, Vec<Expr<R>>, Box<R>),
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Application<R> {
	pub head: AppHead<R>,
	pub args: Vector<Expr<R>>,
}

impl<R: Display> Display for Application<R> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let args = self.args.iter().map(|arg| format!("{}", arg)).join(", ");
		match &self.head {
			AppHead::Var(VL(l)) => write!(f, "#{}({})", l, args),
			AppHead::HOp(op, op_args, rel) => writeln!(
				f,
				"{}({}, {})({})",
				op,
				op_args.iter().map(|arg| format!("{}", arg)).join(", "),
				rel,
				args
			),
		}
	}
}

/// SQL data types (adapted from sqlparser)
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "UPPERCASE")]
pub enum DataType {
	/// Uuid type
	Uuid,
	/// Integer
	#[serde(alias = "INT", alias = "SMALLINT", alias = "BIGINT")]
	Integer,
	/// Real number
	#[serde(alias = "FLOAT", alias = "DOUBLE", alias = "DECIMAL")]
	Real,
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
		write!(f, "{}", self.iter().map(|term| format!("{}", term)).join("\n+ "))
	}
}

pub fn var<'c>(ctx: &'c Context, ty: DataType, prefix: &str) -> Dynamic<'c> {
	use z3::ast::{Bool, Int, Real as Re, String as Str};
	use DataType::*;
	match ty {
		Boolean => Bool::fresh_const(ctx, prefix).into(),
		String => Str::fresh_const(ctx, prefix).into(),
		Integer | Timestamp => Int::fresh_const(ctx, prefix).into(),
		Real => Re::fresh_const(ctx, prefix).into(),
		_ => panic!("unsupported type {:?}", ty),
	}
}

fn sort(ctx: &Context, ty: DataType) -> Sort {
	use DataType::*;
	match ty {
		Boolean => Sort::bool(ctx),
		String => Sort::string(ctx),
		Integer | Timestamp => Sort::int(ctx),
		Real => Sort::real(ctx),
		_ => panic!("unsupported type {:?}", ty),
	}
}

pub fn func_app<'c>(
	ctx: &'c Context,
	name: String,
	args: Vec<Dynamic<'c>>,
	range: DataType,
) -> Dynamic<'c> {
	let domain = args.iter().map(|arg| arg.get_sort()).collect_vec();
	let args = args.iter().map(|arg| arg as &dyn Ast).collect_vec();
	let f = FuncDecl::new(ctx, name, &domain.iter().collect_vec(), &sort(ctx, range));
	f.apply(&args)
}

pub struct Ctx<'c> {
	context: &'c Context,
	null_int: Nullable<'c, ast::Int<'c>>,
	null_real: Nullable<'c, ast::Real<'c>>,
	null_bool: Nullable<'c, ast::Bool<'c>>,
	null_str: Nullable<'c, ast::String<'c>>,
}

impl<'c> Ctx<'c> {
	pub fn new(solver: &Solver<'c>) -> Self {
		let null_int = Nullable::<ast::Int>::setup(solver);
		let null_real = Nullable::<ast::Real>::setup(solver);
		let null_bool = Nullable::<ast::Bool>::setup(solver);
		let null_str = Nullable::<ast::String>::setup(solver);
		Ctx { context: solver.get_context(), null_int, null_real, null_bool, null_str }
	}
}
