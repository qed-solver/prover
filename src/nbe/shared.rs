use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use sqlparser::ast::DataType;

#[derive(Copy, Clone, Debug)]
pub struct VIndex(pub usize);

#[derive(Copy, Clone, Debug)]
pub struct VLevel(pub usize);

#[derive(Debug, Clone, Default)]
pub struct Env<E> {
	pub(crate) entries: VecDeque<E>,
}

impl<E: Copy> Env<E> {
	pub fn new(entries: Vec<E>) -> Self {
		Env { entries: entries.into() }
	}

	pub fn size(&self) -> usize {
		self.entries.len()
	}

	pub fn get_by_index(&self, index: VIndex) -> E {
		self.entries[self.size() - index.0 - 1]
	}

	pub fn get_by_level(&self, level: VLevel) -> E {
		self.entries[level.0]
	}

	pub fn add_inner(&mut self, entry: E) {
		self.entries.push_back(entry);
	}

	pub fn add_outer(&mut self, entry: E) {
		self.entries.push_front(entry);
	}
}

#[derive(Clone, Debug)]
pub enum Tuple<V> {
	Var(V),
	Proj(V, Vec<usize>),
}

#[derive(Clone, Debug)]
pub enum Value<V> {
	Attr(Tuple<V>, usize),
	Op(String, Vec<Value<V>>),
}

#[derive(Clone, Debug)]
pub enum Predicate<V> {
	TupEq(Tuple<V>, Tuple<V>),
	ValEq(Value<V>, Value<V>),
	Rel(String, Vec<Value<V>>),
	And(Box<Predicate<V>>, Box<Predicate<V>>),
	Or(Box<Predicate<V>>, Box<Predicate<V>>),
	Not(Box<Predicate<V>>),
}

impl Env<VIndex> {
	pub fn read_tup(&self, tuple: Tuple<VLevel>) -> Tuple<VIndex> {
		match tuple {
			Tuple::Var(l) => Tuple::Var(self.get_by_level(l)),
			Tuple::Proj(l, p) => Tuple::Proj(self.get_by_level(l), p),
		}
	}

	pub fn read_val(&self, value: Value<VLevel>) -> Value<VIndex> {
		match value {
			Value::Attr(tup, a) => Value::Attr(self.read_tup(tup), a),
			Value::Op(f, args) => {
				Value::Op(f, args.into_iter().map(|v| self.read_val(v)).collect())
			},
		}
	}

	pub fn read_pred(&self, pred: Predicate<VLevel>) -> Predicate<VIndex> {
		match pred {
			Predicate::TupEq(t1, t2) => Predicate::TupEq(self.read_tup(t1), self.read_tup(t2)),
			Predicate::ValEq(v1, v2) => Predicate::ValEq(self.read_val(v1), self.read_val(v2)),
			Predicate::Rel(r, args) => {
				Predicate::Rel(r, args.into_iter().map(|v| self.read_val(v)).collect())
			},
			Predicate::And(p1, p2) => {
				Predicate::And(Box::new(self.read_pred(*p1)), Box::new(self.read_pred(*p2)))
			},
			Predicate::Or(p1, p2) => {
				Predicate::Or(Box::new(self.read_pred(*p1)), Box::new(self.read_pred(*p2)))
			},
			Predicate::Not(p) => Predicate::Not(Box::new(self.read_pred(*p))),
		}
	}

	pub fn transpose(&self) -> Env<VLevel> {
		let entries = self.entries.iter().map(|VIndex(l)| VLevel(self.size() - l - 1)).collect();
		Env { entries }
	}
}

impl Env<VLevel> {
	pub fn eval_tup(&self, tuple: Tuple<VIndex>) -> Tuple<VLevel> {
		match tuple {
			Tuple::Var(l) => Tuple::Var(self.get_by_index(l)),
			Tuple::Proj(l, p) => Tuple::Proj(self.get_by_index(l), p),
		}
	}

	pub fn eval_val(&self, value: Value<VIndex>) -> Value<VLevel> {
		match value {
			Value::Attr(tup, a) => Value::Attr(self.eval_tup(tup), a),
			Value::Op(f, args) => {
				Value::Op(f, args.into_iter().map(|v| self.eval_val(v)).collect())
			},
		}
	}

	pub fn eval_pred(&self, pred: Predicate<VIndex>) -> Predicate<VLevel> {
		match pred {
			Predicate::TupEq(t1, t2) => Predicate::TupEq(self.eval_tup(t1), self.eval_tup(t2)),
			Predicate::ValEq(v1, v2) => Predicate::ValEq(self.eval_val(v1), self.eval_val(v2)),
			Predicate::Rel(r, args) => {
				Predicate::Rel(r, args.into_iter().map(|v| self.eval_val(v)).collect())
			},
			Predicate::And(p1, p2) => {
				Predicate::And(Box::new(self.eval_pred(*p1)), Box::new(self.eval_pred(*p2)))
			},
			Predicate::Or(p1, p2) => {
				Predicate::Or(Box::new(self.eval_pred(*p1)), Box::new(self.eval_pred(*p2)))
			},
			Predicate::Not(p) => Predicate::Not(Box::new(self.eval_pred(*p))),
		}
	}

	pub fn transpose(&self) -> Env<VIndex> {
		let entries = self.entries.iter().map(|VLevel(l)| VIndex(self.size() - l - 1)).collect();
		Env { entries }
	}
}

#[derive(Clone, Debug, Default)]
pub struct Schema {
	types: Vec<DataType>,
	key: Option<usize>,
	foreign_keys: HashMap<usize, Rc<Schema>>,
}

impl Schema {
	pub fn new(
		types: Vec<DataType>,
		key: Option<usize>,
		foreign_keys: HashMap<usize, Rc<Schema>>,
	) -> Self {
		Schema { types, key, foreign_keys }
	}
}
