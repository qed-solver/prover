use std::fmt::{Debug, Display, Formatter, Write};
use std::ops::{Add, Mul, Not};

use imbl::{vector, Vector};
use indenter::indented;
use itertools::Itertools;
use UExpr::*;

use super::shared::{Lambda, Neutral, Typed};
use crate::pipeline::shared;
use crate::pipeline::shared::DataType;

pub type Relation = Lambda<UExpr>;
pub type Expr = shared::Expr<UExpr, Relation, Aggr>;
pub type Logic = shared::Logic<UExpr, Expr>;

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Aggr(pub String, pub Vector<DataType>, pub UExpr, pub Box<Expr>);

impl Display for Aggr {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let Aggr(name, scope, uexpr, expr) = self;
		write!(f, "⨿{} {:?} {{", name, scope)?;
		writeln!(indented(f).with_str("\t"), "{},", uexpr)?;
		writeln!(indented(f).with_str("\t"), "{}", expr)?;
		write!(f, "}}")
	}
}

impl Typed for Aggr {
	fn ty(&self) -> DataType {
		self.3.ty()
	}
}

/// An expression that evaluates to a U-semiring value.
/// This include all constants and operation defined over the U-semiring,
/// as well as the result of a predicate and application of a relation with some arguments.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum UExpr {
	// Addition
	Add(Vector<UExpr>),
	// Multiplication
	Mul(Vector<UExpr>),
	// Squash operator
	Squash(Box<UExpr>),
	// Not operator
	Not(Box<UExpr>),
	// Summation that ranges over tuples of certain schema
	Sum(Vector<DataType>, Box<UExpr>),
	// Predicate that can be evaluated to 0 or 1
	Pred(Box<Logic>),
	// Application of a lambda with arguments
	App(Box<Relation>, Vector<Expr>),
	// Neutral application
	Neu(Neutral<Relation, Expr>),
}

impl UExpr {
	pub fn zero() -> Self {
		UExpr::Add(vector![])
	}

	pub fn one() -> Self {
		UExpr::Mul(vector![])
	}

	pub fn sum(scope: impl Into<Vector<DataType>>, body: impl Into<Box<UExpr>>) -> Self {
		Sum(scope.into(), body.into())
	}

	pub fn squash(body: impl Into<Box<UExpr>>) -> Self {
		Squash(body.into())
	}

	pub fn pred(l: Logic) -> Self {
		Pred(l.into())
	}

	pub fn app(rel: impl Into<Box<Relation>>, args: Vector<Expr>) -> Self {
		App(rel.into(), args)
	}
}

impl Display for UExpr {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Add(us) if us.is_empty() => write!(f, "0"),
			Add(us) => write!(f, "({})", us.iter().format(" + ")),
			Mul(us) if us.is_empty() => write!(f, "1"),
			Mul(us) => write!(f, "({})", us.iter().format(" × ")),
			Squash(u) => write!(f, "‖{}‖", u),
			Not(u) => write!(f, "¬({})", u),
			Sum(scope, body) => {
				writeln!(f, "∑ {:?} {{", scope)?;
				writeln!(indented(f).with_str("\t"), "{}", body)?;
				write!(f, "}}")
			},
			Pred(logic) => write!(f, "⟦{}⟧", logic),
			App(rel, args) => {
				write!(f, "{}({})", rel, args.iter().join(", "))
			},
			Neu(Neutral(head, args)) => {
				write!(f, "{}({})", head, args.iter().join(", "))
			},
		}
	}
}

// The following overload the +, *, and ! operators for UExpr, so that we can construct an expression
// in a natural way.

impl Add<UExpr> for UExpr {
	type Output = UExpr;

	fn add(self, rhs: UExpr) -> Self::Output {
		match (self, rhs) {
			(Add(us1), Add(us2)) => Add(us1 + us2),
			(Add(us1), u2) => Add(us1 + vector![u2]),
			(u1, Add(us2)) => Add(vector![u1] + us2),
			(t1, t2) => Add(vector![t1] + vector![t2]),
		}
	}
}

impl Mul<UExpr> for UExpr {
	type Output = UExpr;

	fn mul(self, rhs: UExpr) -> Self::Output {
		match (self, rhs) {
			(Mul(us1), Mul(us2)) => Mul(us1 + us2),
			(Mul(us1), u2) => Mul(us1 + vector![u2]),
			(u1, Mul(us2)) => Mul(vector![u1] + us2),
			(t1, t2) => Mul(vector![t1] + vector![t2]),
		}
	}
}

impl Not for UExpr {
	type Output = UExpr;

	fn not(self) -> Self::Output {
		Not(self.into())
	}
}
