use std::ops::{Add, Mul, Not};

use imbl::{vector, Vector};
use serde::{Deserialize, Serialize};

use crate::pipeline::shared::{Constraint, DataType, Eval, Schema, VL};
use crate::pipeline::syntax::{AppHead, UExpr};
use crate::pipeline::{shared, syntax as syn};
use crate::solver::Payload;

#[derive(Serialize, Deserialize)]
pub struct Input {
	schemas: Vec<Schema>,
	queries: (Relation, Relation),
	help: (String, String),
}

impl From<Input> for Payload {
	fn from(input: Input) -> Self {
		let Input { schemas, queries: (r1, r2), help } = input;
		let subst = vector![];
		let env = Env(&schemas, &subst, 0);
		log::info!("Schemas:\n{:?}", schemas);
		log::info!("Input:\n{}\n{}", help.0, help.1);
		Payload(schemas.clone(), env.eval(r1), env.eval(r2))
	}
}

#[derive(Copy, Clone)]
struct Env<'e>(&'e [Schema], &'e Vector<syn::Expr>, usize);

fn vars(level: usize, types: Vector<DataType>) -> Vector<syn::Expr> {
	types.into_iter().enumerate().map(|(i, ty)| syn::Expr::Var(VL(level + i), ty)).collect()
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Relation {
	Singleton,
	Scan(VL),
	Filter {
		condition: Expr,
		source: Box<Relation>,
	},
	Project {
		#[serde(alias = "target")]
		columns: Vec<Expr>,
		source: Box<Relation>,
	},
	Join {
		condition: Expr,
		left: Box<Relation>,
		right: Box<Relation>,
		kind: JoinKind,
	},
	Correlate(Box<Relation>, Box<Relation>),
	Union(Box<Relation>, Box<Relation>),
	Except(Box<Relation>, Box<Relation>),
	Distinct(Box<Relation>),
	Values {
		schema: Vec<DataType>,
		content: Vec<Vec<Expr>>,
	},
	Aggregate {
		#[serde(alias = "function")]
		columns: Vec<Expr>,
		source: Box<Relation>,
	},
	Sort {
		collation: Vec<(usize, DataType, String)>,
		offset: Option<Expr>,
		limit: Option<Expr>,
		source: Box<Relation>,
	},
}

impl Relation {
	fn scopes(&self, schemas: &[Schema]) -> Vector<DataType> {
		use Relation::*;
		match self {
			Singleton => Vector::new(),
			Scan(table) => schemas[table.0].types.clone().into(),
			Filter { source, .. } => source.scopes(schemas),
			Project { columns, .. } | Aggregate { columns, .. } => {
				columns.iter().map(|expr| expr.ty()).collect()
			},
			Join { left, kind: JoinKind::Semi | JoinKind::Anti, .. } => left.scopes(schemas),
			Join { left, right, .. } | Correlate(left, right) => {
				left.scopes(schemas) + right.scopes(schemas)
			},
			Union(rel1, _) | Except(rel1, _) => rel1.scopes(schemas),
			Distinct(rel) => rel.scopes(schemas),
			Values { schema, .. } => schema.clone().into(),
			Sort { source, .. } => source.scopes(schemas),
		}
	}
}

impl<'e> Eval<Relation, syn::Relation> for Env<'e> {
	fn eval(self, source: Relation) -> syn::Relation {
		use shared::Predicate::*;
		use syn::Relation as Rel;
		use Relation::*;
		let Env(schemas, subst, lvl) = self;
		let scopes = source.scopes(schemas);
		match source {
			Singleton => Rel::new(vector![], UExpr::One),
			Scan(table) => {
				let head = AppHead::Var(table);
				let vars = vars(lvl, scopes.clone());
				let conds = schemas[table.0]
					.guaranteed
					.iter()
					.map(|cond| Env(schemas, &vars, lvl + scopes.len()).eval(cond.to_pred()));
				let body = schemas[table.0]
					.constraints
					.iter()
					.zip(vars.clone())
					.filter_map(|(constr, v)| match constr {
						Constraint::NotNullable => {
							Some(UExpr::Not(UExpr::Pred(shared::Predicate::null(v)).into()))
						},
						_ => None,
					})
					.chain(conds)
					.fold(UExpr::App(head, vars.clone()), UExpr::mul);
				Rel::new(scopes, body)
			},
			// Filter R(x, y) by P[x, y]
			// λ x, y. [P[x, y]] × R(x, y)
			Filter { condition, source } => {
				let vars = vars(lvl, scopes.clone());
				let body_lvl = lvl + scopes.len();
				let cond_subst = subst + &vars;
				let condition = Env(schemas, &cond_subst, body_lvl).eval(condition.to_pred());
				let source = Env(schemas, subst, body_lvl).eval(*source);
				Rel::new(scopes, condition * source.app(vars))
			},
			// Project f[x, y] from R(x, y)
			// λ a. ∑ x, y. [a = f[x, y]] × R(x, y)
			Project { columns, source } => {
				let proj_vars = vars(lvl, scopes.clone());
				let inner_scopes = source.scopes(schemas);
				let inner_vars = vars(lvl + scopes.len(), inner_scopes.clone());
				let inner_lvl = lvl + scopes.len() + inner_scopes.len();
				let source = Env(schemas, subst, inner_lvl).eval(*source);
				let cols_subst = subst + &inner_vars;
				let cols_env = Env(schemas, &(cols_subst), inner_lvl);
				let body = proj_vars
					.into_iter()
					.zip(columns)
					.map(|(var, col)| UExpr::Pred(Eq(var, cols_env.eval(col))))
					.fold(source.app(inner_vars), UExpr::mul);
				Rel::new(scopes, UExpr::sum(inner_scopes, body))
			},
			// R(x) semi join S(y) on P[x, y]
			// λ x. R(x) × ‖∑ y. [P[x, y]] × S(y)‖
			Join { condition, left, right, kind: kind @ (JoinKind::Semi | JoinKind::Anti) } => {
				let left_vars = vars(lvl, scopes.clone());
				let body_lvl = lvl + scopes.len();
				let inner_scopes = right.scopes(schemas);
				let inner_lvl = body_lvl + inner_scopes.len();
				let right_vars = vars(body_lvl, inner_scopes.clone());
				let cond_subst = subst + &(&left_vars + &right_vars);
				let cond = Env(schemas, &cond_subst, inner_lvl).eval(condition.to_pred());
				let right_body = Env(schemas, subst, inner_lvl).eval(*right).app(right_vars);
				let left_body = Env(schemas, subst, body_lvl).eval(*left).app(left_vars);
				let wrapper = match kind {
					JoinKind::Semi => UExpr::squash,
					JoinKind::Anti => UExpr::not,
					_ => unreachable!(),
				};
				Rel::new(scopes, left_body * wrapper(UExpr::sum(inner_scopes, cond * right_body)))
			},
			// R(x) inner join S(y) on P[x, y]
			// λ x, y. [P[x, y]] × R(x) × S(y)
			// R(x) full join S(y) on P[x, y]
			// λ x, y. [P[x, y]] × R(x) × S(y)
			//        + ¬(∑ x'. P[x', y] × R(x')) × Null(x) × S(y)
			//        + ¬(∑ y'. P[x, y'] × S(y')) × Null(y) × R(x)
			Join { condition, left, right, kind } => {
				let left_scopes = left.scopes(schemas);
				let right_scopes = right.scopes(schemas);
				let right_vars = &vars(lvl + left_scopes.len(), right_scopes);
				let left_vars = &vars(lvl, left_scopes);
				let body_lvl = lvl + scopes.len();
				let body_env = Env(schemas, subst, body_lvl);
				let left_body = body_env.eval(*left.clone()).app(left_vars.clone());
				let right_body = body_env.eval(*right.clone()).app(right_vars.clone());
				let cond_subst = subst + &(left_vars + right_vars);
				let cond_env = Env(schemas, &cond_subst, body_lvl);
				let cond = condition.to_pred();
				let matching = cond_env.eval(cond.clone()) * left_body.clone() * right_body.clone();
				let miss = |miss_left| {
					let missing = *if miss_left { left.clone() } else { right.clone() };
					let inner_scopes = missing.scopes(schemas);
					let inner_vars = vars(body_lvl, inner_scopes.clone());
					let inner_lvl = body_lvl + inner_scopes.len();
					let inner_cond_vars =
						if miss_left { &inner_vars + right_vars } else { left_vars + &inner_vars };
					let inner_cond_subst = subst + &inner_cond_vars;
					let inner_cond = Env(schemas, &inner_cond_subst, inner_lvl).eval(cond.clone());
					let missing = Env(schemas, subst, inner_lvl).eval(missing);
					let inner_body = inner_cond * missing.app(inner_vars);
					let other_body = if miss_left { right_body.clone() } else { left_body.clone() };
					if miss_left { left_vars } else { right_vars }
						.iter()
						.map(|v| UExpr::Pred(shared::Predicate::null(v.clone())))
						.fold(other_body * !UExpr::sum(inner_scopes, inner_body), UExpr::mul)
				};
				match kind {
					JoinKind::Inner => Rel::new(scopes, matching),
					JoinKind::Left => Rel::new(scopes, matching + miss(false)),
					JoinKind::Right => Rel::new(scopes, matching + miss(true)),
					JoinKind::Full => Rel::new(scopes, matching + miss(true) + miss(false)),
					_ => unreachable!(),
				}
			},
			// R(x) correlate join S[x](y)
			// λx, y. R(x) × S[x](y)
			Correlate(left, right) => {
				let left_scopes = left.scopes(schemas);
				let right_scopes = right.scopes(schemas);
				let right_vars = vars(lvl + left_scopes.len(), right_scopes);
				let left_vars = vars(lvl, left_scopes);
				let body_lvl = lvl + scopes.len();
				let left = Env(schemas, subst, body_lvl).eval(*left);
				let right_subst = subst + &left_vars;
				let right = Env(schemas, &right_subst, body_lvl).eval(*right);
				Rel::new(scopes, left.app(left_vars) * right.app(right_vars))
			},
			// R(x) union S(y)
			// λx. R(x) + S(x)
			Union(left, right) => {
				let body_lvl = lvl + scopes.len();
				let vars = vars(lvl, scopes.clone());
				let left = Env(schemas, subst, body_lvl).eval(*left);
				let right = Env(schemas, subst, body_lvl).eval(*right);
				Rel::new(scopes, left.app(vars.clone()) + right.app(vars))
			},
			// R(x) except S(y)
			// λx. R(x) × ¬S(x)
			Except(left, right) => {
				let body_lvl = lvl + scopes.len();
				let vars = vars(lvl, scopes.clone());
				let left = Env(schemas, subst, body_lvl).eval(*left);
				let right = Env(schemas, subst, body_lvl).eval(*right);
				Rel::new(scopes, left.app(vars.clone()) * !right.app(vars))
			},
			// Distinct R(x)
			// λx. ‖R(x)‖
			Distinct(source) => {
				let source = Env(schemas, subst, lvl + scopes.len()).eval(source);
				Rel::new(scopes.clone(), UExpr::squash(source.app(vars(lvl, scopes))))
			},
			// Values ((a1, b1), (a2, b2), (a3, b3))
			// λx, y. [x = a1] × [y = b1] + [x = a2] × [y = b2] + [x = a3] × [y = b3]
			Values { schema, content } => {
				let vars = vars(lvl, scopes.clone());
				let env = Env(schemas, subst, lvl + scopes.len());
				let body = content
					.into_iter()
					.map(|row| {
						vars.iter()
							.zip(row)
							.map(|(v, e)| UExpr::Pred(Eq(v.clone(), env.eval(e))))
							.fold(UExpr::One, UExpr::mul)
					})
					.fold(UExpr::Zero, UExpr::add);
				Rel::new(scopes, body)
			},
			// Agg1(f[x, y]), Agg2(g[x, y]) on R(x, y)
			// λa, b. [a = Agg1(λc. ∑x, y. [c = f[x, y]] × R(x, y))]
			//        × [b = Agg2(λc. ∑x, y. [c = g[x, y]] × R(x, y))]
			Aggregate { columns, source } => {
				let vars = vars(lvl, scopes.clone());
				let env = Env(schemas, subst, lvl + scopes.len());
				let new_body = vars
					.into_iter()
					.zip(columns)
					.map(|(v, agg)| UExpr::Pred(Eq(v, agg.eval_agg(&source, env))))
					.fold(UExpr::One, UExpr::mul);
				Rel::new(scopes, new_body)
			},
			Sort { mut collation, offset, limit, source } => {
				// TODO: Better way to handle multiple sort columns.
				let env = Env(schemas, subst, lvl + scopes.len());
				let head = if let Some((col, _, ord)) = collation.pop() {
					let col = col.into();
					let ord = ord.into();
					AppHead::HOp(
						"sort".to_string(),
						vec![col, ord],
						env.eval(Sort { collation, offset, limit, source }.into()),
					)
				} else {
					let source = env.eval(source);
					let offset = offset.map(|n| env.eval(n)).unwrap_or(0u32.into());
					if let Some(count) = limit {
						AppHead::HOp("limit".to_string(), vec![env.eval(count), offset], source)
					} else {
						AppHead::HOp("offset".to_string(), vec![offset], source)
					}
				};
				let vars = vars(lvl, scopes.clone());
				Rel::new(scopes, UExpr::App(head, vars))
			},
		}
	}
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "UPPERCASE")]
pub enum JoinKind {
	Inner,
	Left,
	Right,
	Full,
	Semi,
	Anti,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[serde(untagged)]
pub enum Expr {
	Col {
		column: VL,
		#[serde(alias = "type")]
		ty: DataType,
	},
	HOp {
		#[serde(rename = "operator")]
		op: String,
		#[serde(rename = "operand")]
		args: Vec<Expr>,
		#[serde(rename = "query")]
		rel: Box<Relation>,
		#[serde(alias = "type")]
		ty: DataType,
	},
	Op {
		#[serde(rename = "operator")]
		op: String,
		#[serde(rename = "operand")]
		args: Vec<Expr>,
		#[serde(alias = "type")]
		ty: DataType,
	},
}

impl Expr {
	fn ty(&self) -> DataType {
		match self {
			Expr::Col { ty, .. } => ty,
			Expr::Op { ty, .. } => ty,
			Expr::HOp { ty, .. } => ty,
		}
		.clone()
	}

	fn eval_agg(self, source: &Relation, env: Env) -> syn::Expr {
		use shared::Expr::*;
		if let Expr::Op { op, args, ty } = self {
			let source = match op.as_str() {
				"COUNT" if args.is_empty() => source.clone(),
				_ => Relation::Project { columns: args, source: Box::new(source.clone()) },
			};
			HOp(op, vec![], Box::new(env.eval(source)), ty)
		} else {
			panic!()
		}
	}

	fn to_pred(&self) -> Predicate {
		use Predicate::*;
		match self {
			Expr::Op { op, args, ty: DataType::Boolean } => match op.as_str() {
				"TRUE" => True,
				"FALSE" => False,
				"=" => Eq(args[0].clone(), args[1].clone()),
				"<>" => Not(Box::new(Eq(args[0].clone(), args[1].clone()))),
				"AND" => And(args.iter().map(|arg| arg.to_pred()).collect()),
				"OR" => Or(args.iter().map(|arg| arg.to_pred()).collect()),
				"NOT" => Not(Box::new(args[0].to_pred())),
				"IS NULL" => Null(args[0].clone()),
				"IS NOT NULL" => Not(Box::new(Null(args[0].clone()))),
				op => Pred(op.to_string(), args.clone()),
			},
			expr @ Expr::Col { ty: DataType::Boolean, .. } => Bool(expr.clone()),
			expr @ Expr::HOp { op, args, rel, ty: DataType::Boolean } => match op.as_str() {
				"IN" => In(args.clone(), rel.clone()),
				"EXISTS" => Exists(rel.clone()),
				_ => Bool(expr.clone()),
			},
			_ => panic!("wrong type for predicate"),
		}
	}
}

impl<'e> Eval<Expr, syn::Expr> for Env<'e> {
	fn eval(self, source: Expr) -> syn::Expr {
		use shared::Expr::*;
		match source {
			Expr::Col { column, ty } => self.1[column.0].clone(),
			Expr::Op { op, args, ty } if op == "CAST" && args.len() == 1 => {
				let args = self.eval(args);
				if args[0].ty() == ty {
					args[0].clone()
				} else {
					Op(op, args, ty)
				}
			},
			Expr::Op { op, args, ty } => Op(op, self.eval(args), ty),
			Expr::HOp { op, args, rel, ty } => HOp(op, self.eval(args), self.eval(rel), ty),
		}
	}
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Predicate {
	True,
	False,
	Null(Expr),
	Bool(Expr),
	Eq(Expr, Expr),
	Like(Expr, String),
	Exists(Box<Relation>),
	In(Vec<Expr>, Box<Relation>),
	Pred(String, Vec<Expr>),
	And(Vec<Predicate>),
	Or(Vec<Predicate>),
	Not(Box<Predicate>),
}

impl<'e> Eval<Predicate, UExpr> for Env<'e> {
	fn eval(self, source: Predicate) -> UExpr {
		use shared::Predicate as Pred;
		use Predicate::*;
		let Env(schemas, subst, lvl) = self;
		match source {
			True => UExpr::One,
			False => UExpr::Zero,
			Null(e) => UExpr::Pred(Pred::null(self.eval(e))),
			Bool(e) => UExpr::Pred(Pred::Bool(self.eval(e))),
			Eq(e1, e2) => UExpr::Pred(Pred::Eq(self.eval(e1), self.eval(e2))),
			Like(e, pat) => UExpr::Pred(Pred::Like(self.eval(e), pat)),
			Exists(rel) => {
				let scopes = rel.scopes(schemas);
				let rel = Env(schemas, subst, lvl + scopes.len()).eval(*rel);
				UExpr::squash(UExpr::sum(scopes.clone(), UExpr::app(rel, vars(lvl, scopes))))
			},
			In(vals, rel) => UExpr::squash(UExpr::app(self.eval(*rel), self.eval(vals).into())),
			Pred(op, args) => {
				UExpr::Pred(Pred::Bool(self.eval(Expr::Op { op, args, ty: DataType::Boolean })))
			},
			And(ps) => ps.into_iter().map(|p| self.eval(p)).fold(UExpr::One, UExpr::mul),
			Or(ps) => {
				UExpr::squash(ps.into_iter().map(|p| self.eval(p)).fold(UExpr::Zero, UExpr::add))
			},
			Not(p) => !self.eval(*p),
		}
	}
}
