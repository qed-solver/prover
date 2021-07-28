use crate::evaluate::normal::Application;
use crate::evaluate::shared::{DataType, Predicate};

// SUM(v1 v2..., [p] * R(a, b) * |..|)
#[derive(Clone, Debug, Default)]
pub struct Term {
	pub preds: Vec<Predicate>,
	pub squash: Option<Box<UExpr>>,
	pub not: Option<Box<UExpr>>,
	pub apps: Vec<Application>,
	pub scopes: Vec<DataType>,
}

impl Term {
	pub fn new(
		preds: Vec<Predicate>,
		squash: Option<Box<UExpr>>,
		not: Option<Box<UExpr>>,
		apps: Vec<Application>,
		scopes: Vec<DataType>,
	) -> Self {
		Term { preds, squash, not, apps, scopes }
	}
}

#[derive(Clone, Debug, Default)]
pub struct UExpr(pub Vec<Term>);
