use std::collections::HashMap;

use crate::nbe::normalize;
use crate::nbe::shared::{Env, Predicate, Schema, Tuple, VIndex, VLevel, Value};
use crate::nbe::syntax::{Table, Term};

mod nbe;

fn main() {
	use Term::*;
	// let ast = Sum(
	// 	Schema::new(vec![], Some(1), HashMap::new()),
	// 	Box::new(
	// 		App(Table::Var(VIndex(1)), Tuple::Var(VIndex(2))) * (One + One)
	// 			* App(Table::Var(VIndex(1)), Tuple::Var(VIndex(0)))
	// 	)
	// ) * Sum(
	// 	Schema::new(vec![], Some(2), HashMap::new()),
	// 	Box::new(One)
	// );
	let ast = Sum(
		Schema::new(vec![], Some(1), HashMap::new()),
		Box::new(Sum(
			Schema::new(vec![], Some(2), HashMap::new()),
			Box::new(
				Pred(Predicate::TupEq(Tuple::Var(VIndex(0)), Tuple::Var(VIndex(2))))
					* Sum(
						Schema::new(vec![], Some(3), HashMap::new()),
						Box::new(
							Pred(Predicate::ValEq(
								Value::Attr(Tuple::Var(VIndex(0)), 1),
								Value::Attr(Tuple::Var(VIndex(2)), 1),
							)) * Pred(Predicate::ValEq(
								Value::Attr(Tuple::Var(VIndex(0)), 2),
								Value::Attr(Tuple::Var(VIndex(2)), 2),
							)) * App(Table::Var(VIndex(4)), Tuple::Var(VIndex(0))),
						),
					) * App(Table::Var(VIndex(3)), Tuple::Var(VIndex(0)))
					* Pred(Predicate::ValEq(
						Value::Attr(Tuple::Var(VIndex(1)), 1),
						Value::Attr(Tuple::Var(VIndex(0)), 1),
					)) * Pred(Predicate::Rel(">".to_string(), vec![
					Value::Attr(Tuple::Var(VIndex(1)), 2),
					Value::Op("2".to_string(), vec![]),
				])),
			),
		)),
	);

	println!("{:?}", normalize(ast, Env::new(vec![VLevel(0), VLevel(1)])))
}
