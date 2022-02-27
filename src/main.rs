#![feature(type_ascription)]
extern crate core;

use std::any::Any;
use std::collections::BTreeMap;
use std::fs::File;
use std::io::{BufReader, Read, Write};
use std::os::unix::fs::MetadataExt;
use std::path::Path;
use std::time::Instant;
use std::{fs, io};

use env_logger::{Builder, Env, Target};
use itertools::Itertools;

use crate::pipeline::relation::Input;
use crate::solver::Payload;

mod pipeline;
mod solver;

fn visit<P: AsRef<Path>>(dir: P, mut cb: impl FnMut(usize, &Path)) -> io::Result<()> {
	let path = dir.as_ref();
	let mut i = 0;
	if path.is_dir() {
		for entry in fs::read_dir(path)?
			.sorted_by_cached_key(|entry| entry.as_ref().unwrap().metadata().unwrap().size())
		{
			let entry = entry?;
			let path = entry.path();
			if path.is_file() && path.extension() == Some("json".as_ref()) {
				cb(i, path.as_path());
				i += 1;
			}
		}
	} else if path.is_file() && path.extension() == Some("json".as_ref()) {
		cb(i, path);
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
	let mut stats = BTreeMap::new();
	for arg in std::env::args() {
		visit(arg, |i, path| {
			use CosetteResult::*;
			let file = File::open(&path).unwrap();
			let mut buf_reader = BufReader::new(file);
			let mut contents = String::new();
			let name = path.file_name().unwrap().to_str().unwrap().to_owned();
			println!("#{}: {}", i, path.to_str().unwrap());
			let old_time = Instant::now();
			buf_reader.read_to_string(&mut contents).unwrap();
			let result =
				std::panic::catch_unwind(|| match serde_json::from_str::<Input>(&contents) {
					Ok(rel) => {
						let payload = Payload::from(rel);
						let provable = payload.check();
						println!(
							"Equivalence is {}provable for {}",
							if provable { "" } else { "not " },
							path.file_name().unwrap().to_str().unwrap(),
						);
						if provable {
							Provable
						} else {
							NotProvable
						}
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
				},
			};
			let duration = Instant::now() - old_time;
			let mut result_file = File::create(path.with_extension("res")).unwrap();
			write!(result_file, "{}\n{}", matches!(result, CosetteResult::Provable), duration.as_secs_f32());
			stats.insert(name, result);
		})?;
	}
	println!("\n\nSTATISTICS");
	let (a, b): (Vec<_>, _) = stats.values().partition(|v| matches!(v, CosetteResult::Provable));
	let (al, bl) = (a.len(), b.len());
	for (name, result) in stats {
		println!("{}\t{:?}", name, result);
	}
	println!("Provable: {} / {}", al, al + bl);
	Ok(())
}
