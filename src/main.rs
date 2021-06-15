use std::fs::File;
use std::io::{BufReader, Read};
use std::path::Path;
use std::{fs, io};

use crate::evaluate::syntax::Payload;
use crate::sql::SQL;

pub mod evaluate;
pub mod sql;
pub mod unify;

fn visit<P: AsRef<Path>>(dir: P, cb: &dyn Fn(&Path)) -> io::Result<()> {
	let path = dir.as_ref();
	if path.is_dir() {
		for entry in fs::read_dir(path)? {
			let entry = entry?;
			let path = entry.path();
			if path.is_file() && path.extension() == Some("json".as_ref()) {
				cb(path.as_path())
			}
		}
	} else if path.is_file() && path.extension() == Some("json".as_ref()) {
		cb(path)
	}
	Ok(())
}

fn main() {
	visit("tests", &|path| {
		let file = File::open(&path).unwrap();
		let mut buf_reader = BufReader::new(file);
		let mut contents = String::new();
		buf_reader.read_to_string(&mut contents).unwrap();
		let sql: SQL = serde_json::from_str(&contents).unwrap();
		let payload = Payload::from(sql);
		println!(
			"Equivalence is {}provable for {}",
			if payload.check() { "" } else { "not " },
			path.file_name().unwrap().to_str().unwrap()
		);
	})
	.unwrap();
}
