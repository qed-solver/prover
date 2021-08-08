use std::fmt::{Debug, Display, Formatter, Write};
use std::iter::FromIterator;

use im::Vector;
use indenter::indented;
use itertools::Itertools;

use crate::evaluate::shared;
use crate::evaluate::shared::{Application, DataType};

pub type Relation = shared::Relation<UExpr>;
pub type Predicate = shared::Predicate<Relation>;
pub type Expr = shared::Expr<Relation>;

#[derive(Debug, Clone, Default, Eq, PartialEq, Hash)]
pub struct UExpr(pub Vector<Term>);

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
	pub preds: Vector<Predicate>,
	pub squash: Option<UExpr>,
	pub not: Option<UExpr>,
	pub apps: Vector<Application>,
	pub scopes: Vector<DataType>,
}

impl Display for Term {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let preds = self
			.preds
			.iter()
			.map(|pred| format!("⟦{}⟧", pred))
			.chain(self.not.iter().map(|n| format!("¬({})", n)))
			.chain(self.squash.iter().map(|sq| format!("‖{}‖", sq)))
			.chain(self.apps.iter().map(|app| format!("{}", app)))
			.format(" × ");
		writeln!(f, "∑ {:?} {{", self.scopes)?;
		writeln!(indented(f).with_str("\t"), "{}", preds)?;
		write!(f, "}}")
	}
}
