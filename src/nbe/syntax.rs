use std::ops::{Add, AddAssign, Mul, MulAssign, Not};

use crate::nbe::shared::{DataType, Entry, Env, Expr, Predicate, Schema, VL};
use crate::sql::{Table, SQL};

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
pub struct Payload(pub Env, pub Relation, pub Relation);

impl From<SQL> for Payload {
	fn from(SQL { schemas, tables }: SQL) -> Self {
		fn parse(table: Table, schemas: &[Schema], level: usize) -> Relation {
			// Extract the types of arguments and body from a relation.
			// If the relation is already in the lambda function form, this is trivial.
			// Otherwise the relation is represented by some variable R, and we need to eta-expand
			// λ a, b, c. R(a, b, c)
			let extract = |relation| match relation {
				Relation::Var(l) => {
					let arity = schemas[l.0].types.len();
					// TODO: Properly convert String to DataType
					let vars = (0..arity).map(|i| VL(level + i)).collect();
					(vec![DataType::Any; arity], UExpr::App(relation, vars))
				},
				Relation::Lam(types, term) => (types, *term),
			};
			match table {
				Table::Var(v) => Relation::Var(v),
				Table::Join(t1, t2) => {
					let left = parse(*t1, schemas, level);
					let (mut types, left_term) = extract(left);
					let right = parse(*t2, schemas, level + types.len());
					let (right_types, right_term) = extract(right);
					types.extend(right_types);
					Relation::Lam(types, Box::new(left_term * right_term))
				},
				Table::OuterJoin(t1, t2, pred) => {
					// TODO: Special handling for nulls
					let left = parse(*t1, schemas, level);
					let (mut types, left_term) = extract(left);
					let right = parse(*t2, schemas, level + types.len());
					let (right_types, right_term) = extract(right);
					types.extend(right_types);
					let pred_term = UExpr::Pred(pred.convert(level));
					Relation::Lam(types, Box::new(left_term * right_term * pred_term))
				},
				Table::Query { select, from, pred } => {
					let arity = select.len();
					let source = parse(*from, schemas, level + arity);
					let (types, term) = extract(source);
					let preds = select
						.into_iter()
						.enumerate()
						.map(|(i, col)| {
							UExpr::Pred(Predicate::Eq(Expr::Var(VL(level + i)), col.convert(level)))
						})
						.fold(
							pred.map_or(UExpr::One, |p| UExpr::Pred(p.convert(level))),
							|t, p| t * p,
						);
					let sum = UExpr::Sum(types, Box::new(preds * term));
					// TODO: Properly convert String to DataType
					Relation::Lam(vec![DataType::Any; arity], Box::new(sum))
				},
			}
		}

		let r1 = parse(tables.0, &schemas, schemas.len());
		let r2 = parse(tables.1, &schemas, schemas.len());
		let env = Env::new(
			schemas
				.into_iter()
				.enumerate()
				.map(|(i, schema)| Entry::new_table(VL(i), schema))
				.collect(),
		);
		Payload(env, r1, r2)
	}
}
