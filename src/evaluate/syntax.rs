use std::fmt::{Debug, Display, Formatter, Write};
use std::ops::{Add, AddAssign, Mul, MulAssign, Not};

use indenter::indented;
use itertools::Itertools;

use crate::evaluate::shared;
use crate::evaluate::shared::{DataType, VL};

/// A relation in the U-semiring formalism is a function that maps a tuple to a U-semiring value.
/// It can be represented as a variable for an unknown relation, or encoded as a lambda function
/// when having the explict definition.
/// Here the lambda term uses a vector of data types to bind every components of the input tuple.
/// That is, each component is treated as a unique variable that might appear in the function body.
pub type Relation = shared::Relation<UExpr>;
pub type Predicate = shared::Predicate<UExpr>;
pub type Expr = shared::Expr<UExpr>;

/// An expression that evaluates to a U-semiring value.
/// This include all constants and operation defined over the U-semiring,
/// as well as the result of a predicate and application of a relation with some arguments.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum UExpr {
	Zero,
	One,
	// Addition
	Add(Box<UExpr>, Box<UExpr>),
	// Multiplication
	Mul(Box<UExpr>, Box<UExpr>),
	// Squash operator
	Squash(Box<UExpr>),
	// Not operator
	Not(Box<UExpr>),
	// Summation that ranges over tuples of certain schema
	Sum(Vec<DataType>, Box<UExpr>),
	// Predicate that can be evaluated to 0 or 1
	Pred(Predicate),
	// Application of a relation with arguments.
	// Here each argument are required to be a single variable.
	App(Relation, Vec<VL>),
}

impl UExpr {
	pub fn sum<T: Into<Box<UExpr>>>(types: Vec<DataType>, body: T) -> Self {
		UExpr::Sum(types, body.into())
	}

	pub fn squash<T: Into<Box<UExpr>>>(body: T) -> Self {
		UExpr::Squash(body.into())
	}
}

impl Display for UExpr {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			UExpr::Zero => write!(f, "0"),
			UExpr::One => write!(f, "1"),
			UExpr::Add(u1, u2) => write!(f, "({} + {})", u1, u2),
			UExpr::Mul(u1, u2) => write!(f, "({} × {})", u1, u2),
			UExpr::Squash(u) => write!(f, "‖{}‖", u),
			UExpr::Not(u) => write!(f, "not({})", u),
			UExpr::Sum(types, body) => {
				writeln!(f, "∑ {:?} {{", types)?;
				writeln!(indented(f).with_str("\t"), "{}", body)?;
				write!(f, "}}")
			},
			UExpr::Pred(pred) => write!(f, "⟦{}⟧", pred),
			UExpr::App(rel, args) => {
				write!(f, "{}({})", rel, args.iter().map(|arg| format!("{}", arg)).join(", "))
			},
		}
	}
}

// The following overload the +, *, and ! operators for UExpr, so that we can construct an expression
// in a natural way.

impl<T: Into<Box<UExpr>>> Add<T> for UExpr {
	type Output = UExpr;

	fn add(self, rhs: T) -> Self::Output {
		match (self, *rhs.into()) {
			(UExpr::Zero, t) | (t, UExpr::Zero) => t,
			(t1, t2) => UExpr::Add(Box::new(t1), Box::new(t2)),
		}
	}
}

impl<T: Into<Box<UExpr>>> AddAssign<T> for UExpr {
	fn add_assign(&mut self, rhs: T) {
		*self = self.clone() + rhs;
	}
}

impl<T: Into<Box<UExpr>>> Mul<T> for UExpr {
	type Output = UExpr;

	fn mul(self, rhs: T) -> Self::Output {
		match (self, *rhs.into()) {
			(UExpr::One, t) | (t, UExpr::One) => t,
			(t1, t2) => UExpr::Mul(Box::new(t1), Box::new(t2)),
		}
	}
}

impl<T: Into<Box<UExpr>>> MulAssign<T> for UExpr {
	fn mul_assign(&mut self, rhs: T) {
		*self = self.clone() * rhs;
	}
}

impl Not for UExpr {
	type Output = UExpr;

	fn not(self) -> Self::Output {
		UExpr::Not(self.into())
	}
}
