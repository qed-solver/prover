use crate::evaluate::normal::{Application, EquivClass};
use crate::evaluate::shared::{DataType, Predicate};

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

	pub fn extract_equiv(&mut self) -> EquivClass {
		let mut equiv = EquivClass::default();
		self.preds.retain(|pred| {
			if let Predicate::Eq(e1, e2) = pred {
				equiv.equate(e1.clone(), e2.clone());
				false
			} else {
				true
			}
		});
		equiv
	}
}

#[derive(Clone, Debug, Default)]
pub struct UExpr(pub Vec<Term>);

impl UExpr {
	pub fn terms_mut(&mut self) -> impl Iterator<Item = &mut Term> {
		self.0.iter_mut()
	}
}
