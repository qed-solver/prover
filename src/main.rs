use std::fs::File;
use std::io::{BufReader, Read, Write};
use std::path::Path;
use std::{fs, io};
use std::any::Any;
use std::collections::HashMap;

use env_logger::{Builder, Env, Target};

use crate::relation::Input;
use crate::solver::Payload;

mod evaluate;
mod relation;
mod solver;
mod unify;

fn visit<P: AsRef<Path>>(dir: P, mut cb: impl FnMut(&Path)) -> io::Result<()> {
	let path = dir.as_ref();
	if path.is_dir() {
		for entry in fs::read_dir(path)? {
			let entry = entry?;
			let path = entry.path();
			if path.is_file() && path.extension() == Some("json".as_ref()) {
				cb(path.as_path());
			}
		}
	} else if path.is_file() && path.extension() == Some("json".as_ref()) {
		cb(path);
	}
	Ok(())
}

#[derive(Debug)]
enum CosetteResult {
	Provable,
	NotProvable,
	ParseErr(serde_json::Error),
	Panic(Box<dyn Any + Send>),
}

fn main() -> io::Result<()> {
	Builder::from_env(Env::default().default_filter_or("off"))
		.format(|buf, record| writeln!(buf, "{}", record.args()))
		.target(Target::Stdout)
		.init();
	let mut stats = HashMap::new();
	for arg in std::env::args() {
		visit(arg, |path| {
			use CosetteResult::*;
			let file = File::open(&path).unwrap();
			let mut buf_reader = BufReader::new(file);
			let mut contents = String::new();
			let name = path.file_name().unwrap().to_str().unwrap().to_owned();
			println!("\n{}", path.to_str().unwrap());
			buf_reader.read_to_string(&mut contents).unwrap();
			let result =
				std::panic::catch_unwind(|| match serde_json::from_str::<Input>(&contents) {
					Ok(rel) => {
						let payload = Payload::from(rel);
						println!(
							"Equivalence is {}provable for {}",
							if payload.check() { "" } else { "not " },
							path.file_name().unwrap().to_str().unwrap()
						);
						Provable
					},
					Err(e) => {
						log::error!("Not successfully parsed.\n{}", e);
						ParseErr(e)
					},
				});
			let result = match result {
				Ok(res) => res,
				Err(e) => {
					log::error!("{:?}", e);
					Panic(e)
				}
			};
			stats.insert(name, result);
		})?;
	}
	println!("\n\nSTATISTICS");
	for (name, result) in stats {
		println!("{}\t{:?}", name, result);
	}
	Ok(())
}
