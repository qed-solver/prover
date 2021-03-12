use std::ops::{Add, Mul};

use crate::nbe::shared::{Env, Predicate, Schema, Tuple, VLevel};
use crate::nbe::syntax as syn;

#[derive(Clone, Debug)]
pub struct Closure {
	pub body: syn::Term,
	pub env: Env<VLevel>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Term(pub Vec<Product>);

impl Add for Term {
	type Output = Term;

	fn add(mut self, rhs: Self) -> Self::Output {
		self.0.extend(rhs.0);
		self
	}
}

impl Mul for Term {
	type Output = Term;

	fn mul(self, rhs: Self) -> Self::Output {
		let prods = self
			.0
			.into_iter()
			.flat_map(|p1| rhs.0.iter().map(move |p2| p1.clone() * p2.clone()))
			.collect();
		Term(prods)
	}
}

#[derive(Clone, Debug)]
pub(crate) struct Summation {
	pub schema: Schema,
	pub summand: Closure,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Product {
	pub preds: Vec<Predicate<VLevel>>,
	pub squash: Option<Box<Term>>,
	pub not: Option<Box<Term>>,
	pub apps: Vec<(VLevel, Tuple<VLevel>)>,
	pub sums: Vec<Summation>,
}

impl Product {
	pub fn with_squash<T: Into<Box<Term>>>(squash: T) -> Self {
		Product { squash: Some(squash.into()), ..Product::default() }
	}

	pub fn with_not<T: Into<Box<Term>>>(not: T) -> Self {
		Product { not: Some(not.into()), ..Product::default() }
	}

	pub fn with_preds(preds: Vec<Predicate<VLevel>>) -> Self {
		Product { preds, ..Product::default() }
	}

	pub fn with_app(f: VLevel, tup: Tuple<VLevel>) -> Self {
		Product { apps: vec![(f, tup)], ..Product::default() }
	}

	pub fn with_sum(schema: Schema, summand: Closure) -> Self {
		Product { sums: vec![Summation { schema, summand }], ..Product::default() }
	}
}

impl Mul for Product {
	type Output = Product;

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
