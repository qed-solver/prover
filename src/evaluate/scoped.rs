use std::cmp::min;
use std::collections::HashMap;
use std::iter::FromIterator;

use ena::unify::{InPlaceUnificationTable, NoError, UnifyKey, UnifyValue};

use crate::evaluate::shared;
use crate::evaluate::shared::{Application, DataType};
use std::fmt::{Write, Display, Formatter};
use itertools::Itertools;
use indenter::indented;

type Relation = shared::Relation<UExpr>;
type Predicate = shared::Predicate<UExpr>;
type Expr = shared::Expr<UExpr>;

#[derive(Clone, Debug, Default, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct UExpr(pub Vec<Term>);

impl UExpr {
	pub fn into_terms(self) -> impl Iterator<Item = Term> {
		self.0.into_iter()
	}

	pub fn one() -> Self {
		UExpr(vec![Term::default()])
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

#[derive(Clone, Debug, Default, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Term {
	pub preds: Vec<Predicate>,
	pub squash: Option<UExpr>,
	pub not: Option<UExpr>,
	pub apps: Vec<Application>,
	pub scopes: Vec<DataType>,
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

impl Display for Term {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let exps = self
			.preds
			.iter()
			.map(|pred| format!("⟦{}⟧", pred))
			.chain(self.not.iter().map(|n| format!("not({})", n)))
			.chain(self.squash.iter().map(|sq| format!("‖{}‖", sq)))
			.chain(self.apps.iter().map(|app| format!("{}", app)))
			.join(" × ");
		writeln!(f, "∑ {:?} {{", self.scopes)?;
		writeln!(indented(f).with_str("\t"), "{}", exps)?;
		write!(f, "}}")
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
