use super::*;

#[test]
fn test_syntax_to_normal() {
	let env = &Env::empty();
	let syn = {
		use syn::UExpr::*;
		(One + One) * (One + One)
	};
	let nom = nom::UExpr(vec![nom::Term::default(); 4]);
	assert_eq!(syn.eval(env), nom);
}
