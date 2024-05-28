#![feature(slice_as_chunks)]
#![feature(if_let_guard)]
#![feature(let_chains)]
use std::any::Any;
use std::collections::BTreeMap;
use std::fs::File;
use std::io;
use std::io::{BufReader, Read, Write};
use std::os::unix::fs::MetadataExt;
use std::path::Path;
use std::time::Instant;

use env_logger::{Builder, Env, Target};
use itertools::Itertools;
use walkdir::WalkDir;

use crate::pipeline::{unify, Input, Stats};

mod pipeline;

fn visit<P: AsRef<Path>>(dir: P, mut cb: impl FnMut(usize, &Path)) -> io::Result<()> {
	WalkDir::new(dir)
		.into_iter()
		.filter_map(|f| {
			f.ok().filter(|f| f.path().is_file() && f.path().extension() == Some("json".as_ref()))
		})
		.sorted_by_cached_key(|e| e.metadata().unwrap().size())
		.enumerate()
		.for_each(|(i, e)| cb(i, e.path()));
	Ok(())
}

#[derive(Debug)]
enum CosetteResult {
	Provable(Stats),
	NotProvable(Stats),
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
			let file = File::open(path).unwrap();
			let mut buf_reader = BufReader::new(file);
			let mut contents = String::new();
			println!("#{}: {}", i, path.to_string_lossy().as_ref());
			let start_time = Instant::now();
			buf_reader.read_to_string(&mut contents).unwrap();
			let result =
				std::panic::catch_unwind(|| match serde_json::from_str::<Input>(&contents) {
					Ok(rel) => {
						let (provable, case_stats) = unify(rel);
						println!(
							"Equivalence is {}provable for {}",
							if provable { "" } else { "not " },
							path.file_name().unwrap().to_str().unwrap(),
						);
						if provable {
							Provable(case_stats)
						} else {
							NotProvable(case_stats)
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
			let result_file = File::create(path.with_extension("result")).unwrap();
			let case_stats = match &result {
				Provable(stats) | NotProvable(stats) => {
					let mut stats = stats.clone();
					stats.provable = matches!(result, Provable(_));
					stats.total_duration = start_time.elapsed();
					stats
				},
				_ => {
					let mut stats = Stats::default();
					stats.panicked = true;
					stats.total_duration = start_time.elapsed();
					stats
				},
			};
			serde_json::to_writer(result_file, &case_stats).unwrap();
			stats.insert(path.to_string_lossy().to_string(), result);
		})?;
	}
	println!("\n\nSTATISTICS");
	let (a, b): (Vec<_>, _) = stats.values().partition(|v| matches!(v, CosetteResult::Provable(_)));
	let (al, bl) = (a.len(), b.len());
	for (name, result) in stats {
		println!("{}\t{:?}", name, result);
	}
	println!("Provable: {} / {}", al, al + bl);
	Ok(())
}
