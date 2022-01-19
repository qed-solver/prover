use crate::pipeline::shared::Schema;
use crate::pipeline::syntax::Relation;
use crate::pipeline::{evaluate, unify};

/// The collection of all data in a request.
/// We need to check the equivalence of the two relations under the given environment.
#[derive(Clone, Debug)]
pub struct Payload(pub Vec<Schema>, pub Relation, pub Relation);

impl Payload {
	pub fn check(self) -> bool {
		let Payload(schemas, r1, r2) = self;
		unify(evaluate(r1, &schemas), evaluate(r2, &schemas))
	}
}
