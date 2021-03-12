use std::ops::{Add, AddAssign, Mul, MulAssign, Not};

use crate::nbe::shared::{Predicate, Schema, Tuple, VIndex};

#[derive(Clone, Debug)]
pub enum Term {
	Zero,
	One,
	// Addition
	Add(Box<Term>, Box<Term>),
	// Multiplication
	Mul(Box<Term>, Box<Term>),
	// Squash operator
	Squash(Box<Term>),
	// Not operator
	Not(Box<Term>),
	// Summation that ranges over tuples of certain schema
	Sum(Schema, Box<Term>),
	// Predicate that can be evaluated to 0 or 1
	Pred(Predicate<VIndex>),
	App(Table, Tuple<VIndex>),
}

impl<T: Into<Box<Term>>> Add<T> for Term {
	type Output = Term;

	fn add(self, rhs: T) -> Self::Output {
		match (self, *rhs.into()) {
			(Term::Zero, t) | (t, Term::Zero) => t,
			(t1, t2) => Term::Add(Box::new(t1), Box::new(t2)),
		}
	}
}

impl<T: Into<Box<Term>>> AddAssign<T> for Term {
	fn add_assign(&mut self, rhs: T) {
		*self = self.clone() + rhs;
	}
}

impl<T: Into<Box<Term>>> Mul<T> for Term {
	type Output = Term;

	fn mul(self, rhs: T) -> Self::Output {
		match (self, *rhs.into()) {
			(Term::One, t) | (t, Term::One) => t,
			(t1, t2) => Term::Mul(Box::new(t1), Box::new(t2)),
		}
	}
}

impl<T: Into<Box<Term>>> MulAssign<T> for Term {
	fn mul_assign(&mut self, rhs: T) {
		*self = self.clone() * rhs;
	}
}

impl Not for Term {
	type Output = Term;

	fn not(self) -> Self::Output {
		Term::Not(self.into())
	}
}

#[derive(Clone, Debug)]
pub enum Table {
	Var(VIndex),
	Lam(Schema, Box<Term>),
}
