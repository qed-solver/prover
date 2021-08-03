use std::fmt::{Debug, Display, Formatter, Write};
use std::iter::FromIterator;

use indenter::indented;
use itertools::Itertools;

use crate::evaluate::shared;
use crate::evaluate::shared::{Application, DataType};

pub type Relation = shared::Relation<UExpr>;
pub type Predicate = shared::Predicate<UExpr>;
pub type Expr = shared::Expr<UExpr>;

#[derive(Debug, Clone, Default, Eq, PartialEq, Hash)]
pub struct UExpr(pub Vec<Term>);

impl UExpr {
	pub fn into_terms(self) -> impl Iterator<Item = Term> {
		self.0.into_iter()
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

// SUM(v1 v2..., [p] * R(a, b) * |..|)
#[derive(Debug, Clone, Default, Eq, PartialEq, Hash)]
pub struct Term {
	pub preds: Vec<Predicate>,
	pub squash: Option<UExpr>,
	pub not: Option<UExpr>,
	pub apps: Vec<Application>,
	pub scopes: Vec<DataType>,
}

impl Term {
	pub fn new(
		preds: Vec<Predicate>,
		squash: Option<UExpr>,
		not: Option<UExpr>,
		apps: Vec<Application>,
		scopes: Vec<DataType>,
	) -> Self {
		Term { preds, squash, not, apps, scopes }
	}
}

impl Display for Term {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let preds = self
			.preds
			.iter()
			.map(|pred| format!("⟦{}⟧", pred))
			.chain(self.not.iter().map(|n| format!("not({})", n)))
			.chain(self.squash.iter().map(|sq| format!("‖{}‖", sq)))
			.chain(self.apps.iter().map(|app| format!("{}", app)))
			.join(" × ");
		writeln!(f, "∑ {:?} {{", self.scopes)?;
		writeln!(indented(f).with_str("\t"), "{}", preds)?;
		write!(f, "}}")
	}
}
