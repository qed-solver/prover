use std::iter::FromIterator;
use std::ops::{Add, Mul};

use im::{vector, Vector};

use crate::evaluate::shared::{Application, DataType, Entry, Env, VL};
use crate::evaluate::{shared, syntax as syn};

pub type Relation = shared::Relation<Closure>;
type Predicate = shared::Predicate<Relation>;
type Expr = shared::Expr<Relation>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Closure {
	pub body: syn::UExpr,
	pub env: Env<Entry>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UExpr(pub Vector<Term>);

impl UExpr {
	pub fn into_terms(self) -> impl Iterator<Item = Term> {
		self.0.into_iter()
	}

	pub fn zero() -> Self {
		UExpr::default()
	}

	pub fn one() -> Self {
		UExpr(vector![Term::default()])
	}

	pub fn squash<T: Into<Box<UExpr>>>(squash: T) -> Self {
		UExpr(vector![Term { squash: Some(*squash.into()), ..Term::default() }])
	}

	pub fn not<T: Into<Box<UExpr>>>(not: T) -> Self {
		UExpr(vector![Term { not: Some(*not.into()), ..Term::default() }])
	}

	pub fn preds(preds: impl Into<Vector<Predicate>>) -> Self {
		UExpr(vector![Term { preds: preds.into(), ..Term::default() }])
	}

	pub fn app(table: VL, args: Vector<VL>) -> Self {
		UExpr(vector![Term { apps: vector![Application { table, args }], ..Term::default() }])
	}

	pub fn sum(types: Vector<DataType>, summand: Closure) -> Self {
		UExpr(vector![Term { sums: vector![Summation { types, summand }], ..Term::default() }])
	}
}

impl FromIterator<Term> for UExpr {
	fn from_iter<T: IntoIterator<Item = Term>>(iter: T) -> Self {
		UExpr(iter.into_iter().collect())
	}
}

impl Add for UExpr {
	type Output = UExpr;

	fn add(self, rhs: Self) -> Self::Output {
		UExpr(self.0 + rhs.0)
	}
}

impl Mul for UExpr {
	type Output = UExpr;

	fn mul(self, rhs: Self) -> Self::Output {
		self.into_terms()
			.flat_map(|t1| rhs.0.iter().map(move |t2| t1.clone() * t2.clone()))
			.collect()
	}
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Term {
	pub preds: Vector<Predicate>,
	pub squash: Option<UExpr>,
	pub not: Option<UExpr>,
	pub apps: Vector<Application>,
	pub sums: Vector<Summation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Summation {
	pub types: Vector<DataType>,
	pub summand: Closure,
}

impl Mul for Term {
	type Output = Term;

	fn mul(self, rhs: Self) -> Self::Output {
		let preds = self.preds + rhs.preds;
		let squash = match (self.squash, rhs.squash) {
			(Some(t1), Some(t2)) => Some(t1 * t2),
			(s, None) | (None, s) => s,
		};
		let not = match (self.not, rhs.not) {
			(Some(t1), Some(t2)) => Some(t1 + t2),
			(s, None) | (None, s) => s,
		};
		let apps = self.apps + rhs.apps;
		let sums = self.sums + rhs.sums;
		Term { preds, squash, not, apps, sums }
	}
}
