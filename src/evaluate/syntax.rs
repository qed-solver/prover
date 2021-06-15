use std::ops::{Add, AddAssign, Mul, MulAssign, Not};

use crate::evaluate::evaluate;
use crate::evaluate::shared::{DataType, Entry, Env, Predicate, VL};
use crate::unify::unify;

/// An expression that evaluates to a U-semiring value.
/// This include all constants and operation defined over the U-semiring,
/// as well as the result of a predicate and application of a relation with some arguments.
#[derive(Clone, Debug)]
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

/// A relation in the U-semiring formalism is a function that maps a tuple to a U-semiring value.
/// It can be represented as a variable for an unknown relation, or encoded as a lambda function
/// when having the explict definition.
/// Here the lambda term uses a vector of data types to bind every components of the input tuple.
/// That is, each component is treated as a unique variable that might appear in the function body.
#[derive(Clone, Debug)]
pub enum Relation {
	Var(VL),
	Lam(Vec<DataType>, Box<UExpr>),
}

/// The collection of all data in a request.
/// We need to check the equivalence of the two relations under the given environment.
#[derive(Clone, Debug)]
pub struct Payload(pub Env<Entry>, pub Relation, pub Relation);

impl Payload {
	pub fn check(self) -> bool {
		let Payload(mut env, r1, r2) = self;
		match (r1, r2) {
			(Relation::Lam(tys1, uexpr1), Relation::Lam(tys2, uexpr2)) if tys1 == tys2 => {
				let level = env.size();
				for (i, ty) in tys1.into_iter().enumerate() {
					env.introduce(Entry::Value(VL(level + i), ty))
				}
				// println!("{:?}\n{:?}", evaluate(uexpr1.as_ref().clone(), &env), evaluate(uexpr2.as_ref().clone(), &env));
				unify(&evaluate(*uexpr1, &env), &evaluate(*uexpr2, &env), &env)
			},
			(Relation::Var(v1), Relation::Var(v2)) => v1 == v2,
			_ => false,
		}
	}
}
