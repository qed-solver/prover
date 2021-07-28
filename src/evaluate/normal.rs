use std::cmp::min;
use std::collections::HashMap;
use std::ops::{Add, Mul};

use ena::unify::{InPlaceUnificationTable, NoError, UnifyKey, UnifyValue};

use crate::evaluate::shared::{DataType, Entry, Env, Expr, Predicate, VL};
use crate::evaluate::syntax as syn;

#[derive(Clone, Debug)]
pub struct Closure {
	pub body: syn::UExpr,
	pub env: Env<Entry>,
}

#[derive(Clone, Debug, Default)]
pub struct UExpr(pub Vec<Term>);

impl UExpr {
	pub fn into_terms(self) -> impl Iterator<Item = Term> {
		self.0.into_iter()
	}

	pub fn one() -> Self {
		UExpr(vec![Term::default()])
	}

	pub fn with_term(term: Term) -> Self {
		UExpr(vec![term])
	}

	pub fn with_squash<T: Into<Box<UExpr>>>(squash: T) -> Self {
		UExpr(vec![Term { squash: Some(squash.into()), ..Term::default() }])
	}

	pub fn with_not<T: Into<Box<UExpr>>>(not: T) -> Self {
		UExpr(vec![Term { not: Some(not.into()), ..Term::default() }])
	}

	pub fn with_preds(preds: Vec<Predicate>) -> Self {
		UExpr(vec![Term { preds, ..Term::default() }])
	}

	pub fn with_app(table: VL, args: Vec<VL>) -> Self {
		UExpr(vec![Term { apps: vec![Application { table, args }], ..Term::default() }])
	}

	pub fn with_sum(types: Vec<DataType>, summand: Closure) -> Self {
		UExpr(vec![Term { sums: vec![Summation { types, summand }], ..Term::default() }])
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

#[derive(Clone, Debug, Default)]
pub struct Term {
	pub preds: Vec<Predicate>,
	pub squash: Option<Box<UExpr>>,
	pub not: Option<Box<UExpr>>,
	pub apps: Vec<Application>,
	pub sums: Vec<Summation>,
}

// a * b * SUM(c + d)
// a * b * SUM(c) + a * b * SUM(d)

// SUM(a, c) * SUM(b, d)
// SUM(a b, c * d)

#[derive(Clone, Debug)]
pub struct Summation {
	pub types: Vec<DataType>,
	pub summand: Closure,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Application {
	pub table: VL,
	pub args: Vec<VL>,
}

impl Application {
	pub fn new(table: VL, args: Vec<VL>) -> Self {
		Application { table, args }
	}
}

impl Term {
	pub fn extract_equiv(&self) -> EquivClass {
		let mut equiv = EquivClass::default();
		for pred in &self.preds {
			if let Predicate::Eq(e1, e2) = pred {
				equiv.equate(e1.clone(), e2.clone());
			}
		}
		equiv
	}
}

impl Mul for Term {
	type Output = Term;

	fn mul(mut self, rhs: Self) -> Self::Output {
		self.preds.extend(rhs.preds);
		self.squash = match (self.squash, rhs.squash) {
			(Some(t1), Some(t2)) => Some(Box::new(*t1 * *t2)),
			(Some(t1), None) => Some(t1),
			(None, s) => s,
		};
		self.not = match (self.not, rhs.not) {
			(Some(t1), Some(t2)) => Some(Box::new(*t1 + *t2)),
			(Some(t1), None) => Some(t1),
			(None, s) => s,
		};
		self.apps.extend(rhs.apps);
		self.sums.extend(rhs.sums);
		self
	}
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
struct UniKey(u32);

impl UnifyKey for UniKey {
	type Value = Expr;

	fn index(&self) -> u32 {
		self.0
	}

	fn from_index(u: u32) -> Self {
		UniKey(u)
	}

	fn tag() -> &'static str {
		"UniKey"
	}
}

impl UnifyValue for Expr {
	type Error = NoError;

	fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
		Ok(min(value1.clone(), value2.clone()))
	}
}

#[derive(Clone, Debug, Default)]
pub struct EquivClass {
	uni: InPlaceUnificationTable<UniKey>,
	map: HashMap<Expr, UniKey>,
}

impl EquivClass {
	pub fn equate(&mut self, e1: Expr, e2: Expr) {
		let uni = &mut self.uni;
		let k1 = *self.map.entry(e1).or_insert_with_key(|e| uni.new_key(e.clone()));
		let k2 = *self.map.entry(e2).or_insert_with_key(|e| uni.new_key(e.clone()));
		self.uni.union(k1, k2);
	}

	pub fn equal(&mut self, e1: &Expr, e2: &Expr) -> bool {
		let k1 = self.map.get(e1);
		let k2 = self.map.get(e2);
		if let (Some(&k1), Some(&k2)) = (k1, k2) {
			self.uni.unioned(k1, k2)
		} else {
			false
		}
	}

	pub fn get(&mut self, e: &Expr) -> Option<Expr> {
		let uni = &mut self.uni;
		self.map.get(e).map(|&k| uni.probe_value(k))
	}

	pub fn into_pairs(self) -> impl Iterator<Item = (Expr, Expr)> {
		let map = self.map;
		let mut uni = self.uni;
		map.into_iter().map(move |(expr, k)| (expr, uni.probe_value(k)))
	}
}
