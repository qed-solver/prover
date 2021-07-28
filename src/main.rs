use std::fs::File;
use std::io::{BufReader, Read};
use std::path::Path;
use std::{fs, io};

use crate::relation::Input;
use crate::solver::Payload;

mod evaluate;
mod relation;
mod solver;
mod unify;

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
	for arg in std::env::args() {
		visit(arg, &|path| {
			let file = File::open(&path).unwrap();
			let mut buf_reader = BufReader::new(file);
			let mut contents = String::new();
			println!("\n{}", path.to_str().unwrap());
			buf_reader.read_to_string(&mut contents).unwrap();
			let result = std::panic::catch_unwind(|| match serde_json::from_str::<Input>(&contents) {
				Ok(rel) => {
					let payload = Payload::from(rel);
					println!(
						"Equivalence is {}provable for {}",
						if payload.check() { "" } else { "not " },
						path.file_name().unwrap().to_str().unwrap()
					);
				},
				Err(e) => {
					println!("Not successfully parsed.\n{}", e);
				},
			});
			if let Err(r) = result {
				eprintln!("{:?}", r);
			}
		});
	}
}
