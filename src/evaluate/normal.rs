use std::iter::FromIterator;
use std::ops::{Add, Mul};

use crate::evaluate::shared::{Application, DataType, Entry, Env, VL};
use crate::evaluate::{shared, syntax as syn};
use std::fmt::{Display, Formatter};
use itertools::Itertools;

type Relation = shared::Relation<UExpr>;
type Predicate = shared::Predicate<UExpr>;
type Expr = shared::Expr<UExpr>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Closure {
	pub body: syn::UExpr,
	pub env: Env<Entry>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UExpr(pub Vec<Term>);

impl UExpr {
	pub fn into_terms(self) -> impl Iterator<Item = Term> {
		self.0.into_iter()
	}

	pub fn one() -> Self {
		UExpr(vec![Term::default()])
	}

	pub fn term(term: Term) -> Self {
		UExpr(vec![term])
	}

	pub fn squash<T: Into<Box<UExpr>>>(squash: T) -> Self {
		UExpr(vec![Term { squash: Some(*squash.into()), ..Term::default() }])
	}

	pub fn not<T: Into<Box<UExpr>>>(not: T) -> Self {
		UExpr(vec![Term { not: Some(*not.into()), ..Term::default() }])
	}

	pub fn preds(preds: Vec<Predicate>) -> Self {
		UExpr(vec![Term { preds, ..Term::default() }])
	}

	pub fn app(table: VL, args: Vec<VL>) -> Self {
		UExpr(vec![Term { apps: vec![Application { table, args }], ..Term::default() }])
	}

	pub fn sum(types: Vec<DataType>, summand: Closure) -> Self {
		UExpr(vec![Term { sums: vec![Summation { types, summand }], ..Term::default() }])
	}
}

impl Display for UExpr {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0.iter().map(|term| format!("{}", term)).join("\n+ "))
	}
}

impl FromIterator<Term> for UExpr {
	fn from_iter<T: IntoIterator<Item = Term>>(iter: T) -> Self {
		UExpr(iter.into_iter().collect())
	}
}

impl Add for UExpr {
	type Output = UExpr;

	fn add(mut self, rhs: Self) -> Self::Output {
		self.0.extend(rhs.0);
		self
	}
}

impl Mul for UExpr {
	type Output = UExpr;

	fn mul(self, rhs: Self) -> Self::Output {
		let terms = self
			.into_terms()
			.flat_map(|p1| rhs.0.iter().map(move |p2| p1.clone() * p2.clone()))
			.collect();
		UExpr(terms)
	}
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Term {
	pub preds: Vec<Predicate>,
	pub squash: Option<UExpr>,
	pub not: Option<UExpr>,
	pub apps: Vec<Application>,
	pub sums: Vec<Summation>,
}

impl Display for Term {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let exps = self
			.preds
			.iter()
			.map(|pred| format!("⟦{}⟧", pred))
			.chain(self.not.iter().map(|n| format!("not({})", n)))
			.chain(self.squash.iter().map(|sq| format!("‖{}‖", sq)))
			.chain(self.apps.iter().map(|app| format!("{}", app)))
			.chain(self.sums.iter().map(|sum| {
				format!("∑ {:?} {{\n{}\n}}", sum.types, sum.summand.body)
			}))
			.join(" × ");
		write!(f, "{}", if exps.is_empty() { "1".to_string() } else { exps })
	}
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Summation {
	pub types: Vec<DataType>,
	pub summand: Closure,
}

impl Mul for Term {
	type Output = Term;

	fn mul(mut self, rhs: Self) -> Self::Output {
		self.preds.extend(rhs.preds);
		self.squash = match (self.squash, rhs.squash) {
			(Some(t1), Some(t2)) => Some(t1 * t2),
			(Some(t1), None) => Some(t1),
			(None, s) => s,
		};
		self.not = match (self.not, rhs.not) {
			(Some(t1), Some(t2)) => Some(t1 + t2),
			(Some(t1), None) => Some(t1),
			(None, s) => s,
		};
		self.apps.extend(rhs.apps);
		self.sums.extend(rhs.sums);
		self
	}
}
