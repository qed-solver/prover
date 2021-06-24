use crate::evaluate::evaluate;
use crate::evaluate::shared::{Entry, Env, VL};
use crate::evaluate::syntax::Relation;
use crate::unify::unify;

/// The collection of all data in a request.
/// We need to check the equivalence of the two relations under the given environment.
#[derive(Clone, Debug)]
pub struct Payload(pub Env<Entry>, pub Relation, pub Relation);

impl Payload {
	pub fn check(self) -> bool {
		let Payload(mut env, r1, r2) = self;
		match (r1, r2) {
			(Relation::Lam(tys1, uexpr1), Relation::Lam(tys2, uexpr2)) if tys1 == tys2 => {
				let level = env.size();
				for (i, ty) in tys1.into_iter().enumerate() {
					env.introduce(Entry::Value(VL(level + i), ty))
				}
				unify(&evaluate(*uexpr1, &env), &evaluate(*uexpr2, &env), &env)
			},
			(Relation::Var(v1), Relation::Var(v2)) => v1 == v2,
			_ => false,
		}
	}
}
