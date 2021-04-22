use std::fs::File;
use std::io::{BufReader, Read};

use crate::nbe::normalize;
use crate::nbe::syntax::{Payload, Relation};
use crate::sql::SQL;

pub mod nbe;
pub mod sql;

fn main() {
	let file = File::open("input.json").unwrap();
	let mut buf_reader = BufReader::new(file);
	let mut contents = String::new();
	buf_reader.read_to_string(&mut contents).unwrap();
	let sql: SQL = serde_json::from_str(&contents).unwrap();
	let Payload(env, r1, r2) = Payload::from(sql);
	if let (Relation::Lam(_, uexpr1), Relation::Lam(_, uexpr2)) = (r1, r2) {
		let uexpr1 = normalize(*uexpr1, &env);
		let uexpr2 = normalize(*uexpr2, &env);
		println!("Expression 1: {:#?}\nExpression 2: {:#?}", uexpr1, uexpr2);
	}
}
