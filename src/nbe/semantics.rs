use std::cmp::min;
use std::collections::HashMap;
use std::ops::{Add, Mul};

use ena::unify::{InPlaceUnificationTable, NoError, UnifyKey, UnifyValue};

use crate::nbe::shared::{DataType, Env, Expr, Predicate, VL};
use crate::nbe::syntax as syn;

#[derive(Clone, Debug)]
pub struct Closure {
	pub body: syn::UExpr,
	pub env: Env,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct UExpr(pub Vec<Term>);

impl UExpr {
	pub(crate) fn into_terms(self) -> impl Iterator<Item = Term> {
		self.0.into_iter()
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
pub(crate) struct Term {
	pub preds: Vec<Predicate>,
	pub squash: Option<Box<UExpr>>,
	pub not: Option<Box<UExpr>>,
	pub apps: Vec<Application>,
	pub sums: Vec<Summation>,
}

#[derive(Clone, Debug)]
pub(crate) struct Summation {
	pub types: Vec<DataType>,
	pub summand: Closure,
}

#[derive(Clone, Debug)]
pub(crate) struct Application {
	pub table: VL,
	pub args: Vec<VL>,
}

impl Application {
	pub fn new(table: VL, args: Vec<VL>) -> Self {
		Application { table, args }
	}
}

impl Term {
	pub fn with_squash<T: Into<Box<UExpr>>>(squash: T) -> Self {
		Term { squash: Some(squash.into()), ..Term::default() }
	}

	pub fn with_not<T: Into<Box<UExpr>>>(not: T) -> Self {
		Term { not: Some(not.into()), ..Term::default() }
	}

	pub fn with_preds(preds: Vec<Predicate>) -> Self {
		Term { preds, ..Term::default() }
	}

	pub fn with_app(table: VL, args: Vec<VL>) -> Self {
		Term { apps: vec![Application { table, args }], ..Term::default() }
	}

	pub fn with_sum(types: Vec<DataType>, summand: Closure) -> Self {
		Term { sums: vec![Summation { types, summand }], ..Term::default() }
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

#[derive(Clone, Debug)]
pub(crate) enum Relation {
	Var(VL),
	Lam(Vec<DataType>, Box<UExpr>),
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
pub(crate) struct EquivClass {
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

#[derive(Clone, Debug, Default)]
pub(crate) struct StableTerm {
	pub preds: Vec<Predicate>,
	pub equiv: EquivClass,
	pub squash: Option<Box<UExpr>>,
	pub not: Option<Box<UExpr>>,
	pub apps: Vec<Application>,
	pub scopes: Vec<DataType>,
}

impl StableTerm {
	pub fn from(term: Term, scopes: Vec<DataType>) -> Self {
		let mut equiv = EquivClass::default();
		let mut preds = Vec::new();
		for pred in term.preds {
			if let Predicate::Eq(e1, e2) = pred {
				equiv.equate(e1, e2);
			} else {
				preds.push(pred);
			}
		}
		StableTerm { preds, equiv, squash: term.squash, not: term.not, apps: term.apps, scopes }
	}
}
