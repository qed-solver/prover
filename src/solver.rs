use crate::evaluate::evaluate;
use crate::evaluate::shared::{Entry, Env};
use crate::evaluate::syntax::Relation;
use crate::unify::unify;

/// The collection of all data in a request.
/// We need to check the equivalence of the two relations under the given environment.
#[derive(Clone, Debug)]
pub struct Payload(pub Env<Entry>, pub Relation, pub Relation);

impl Payload {
	pub fn check(self) -> bool {
		let Payload(ref env, r1, r2) = self;
		unify(&evaluate(r1, env), &evaluate(r2, env), env)
	}
}
