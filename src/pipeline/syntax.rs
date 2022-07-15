use std::fmt::{Debug, Display, Formatter, Write};
use std::ops::{Add, Mul, Not};

use imbl::{Vector, vector};
use indenter::indented;
use itertools::Itertools;
use UExpr::*;

use super::shared::VL;
use crate::pipeline::shared;
use crate::pipeline::shared::DataType;

/// A relation in the U-semiring formalism is a function that maps a tuple to a U-semiring value.
/// It can be represented as a variable for an unknown relation, or encoded as a lambda function
/// when having the explict definition.
/// Here the lambda term uses a vector of data types to bind every components of the input tuple.
/// That is, each component is treated as a unique variable that might appear in the function body.
pub type Expr = shared::Expr<Relation>;
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Application(pub Relation, pub Vector<Expr>);

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Relation {
	Var(VL),
	HOp(String, Vec<Expr>, Box<Relation>),
	Lam(Vector<DataType>, Box<UExpr>),
}

pub type Logic = shared::Logic<Relation, Relation, Application>;

impl Relation {
	pub fn lam(scopes: Vector<DataType>, body: impl Into<Box<UExpr>>) -> Relation {
		Relation::Lam(scopes, body.into())
	}
}

impl Display for Relation {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Relation::Var(table) => write!(f, "#{}", table.0),
			Relation::Lam(scopes, body) => {
				writeln!(f, "(λ {:?}", scopes)?;
				writeln!(indented(f).with_str("\t"), "{})", body)
			},
			Relation::HOp(op, args, rel) => {
				writeln!(f, "{}({}, {})", op, args.iter().join(", "), rel)
			},
		}
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
	Pred(Logic),
	// Application of a relation with arguments.
	// Here each argument are required to be a single variable.
	App(Relation, Vector<Expr>),
}

impl UExpr {
	pub fn zero() -> Self {
		UExpr::Add(vector![])
	}

	pub fn one() -> Self {
		UExpr::Mul(vector![])
	}

	pub fn sum(scopes: impl Into<Vector<DataType>>, body: impl Into<Box<UExpr>>) -> Self {
		Sum(scopes.into(), body.into())
	}

	pub fn squash(body: impl Into<Box<UExpr>>) -> Self {
		Squash(body.into())
	}

	pub fn as_logic(self) -> Logic {
		match self {
			Add(us) => Logic::Or(us.into_iter().map(UExpr::as_logic).collect()),
			Mul(us) => Logic::And(us.into_iter().map(UExpr::as_logic).collect()),
			Squash(u) => u.as_logic(),
			Not(u) => !u.as_logic(),
			Sum(scopes, body) => Logic::Exists(Relation::Lam(scopes, body)),
			Pred(logic) => logic,
			App(table, args) => Logic::App(Application(table, args)),
		}
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
			Sum(scopes, body) => {
				writeln!(f, "∑ {:?} {{", scopes)?;
				writeln!(indented(f).with_str("\t"), "{}", body)?;
				write!(f, "}}")
			},
			Pred(logic) => write!(f, "⟦{}⟧", logic),
			App(rel, args) => {
				write!(f, "{}({})", rel, args.iter().join(", "))
			},
		}
	}
}

impl Display for Application {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let Application(rel, args) = self;
		write!(f, "{}({})", rel, args.iter().join(", "))
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
