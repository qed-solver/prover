use super::*;

#[test]
fn test_syntax_to_normal() {
	let env = &Env::empty();
	let syn = {
		use syn::UExpr;
		use syn::UExpr::*;
		use DataType::*;
		use Expr::*;
		use Predicate::*;
		UExpr::sum(vec![Int], UExpr::One)
			* UExpr::sum(
				vec![Int],
				UExpr::squash(
					UExpr::sum(
						vec![Int],
						UExpr::Pred(Null(Var(VL(0)))) * UExpr::Pred(Null(Var(VL(1)))),
					) * UExpr::Pred(Null(Expr::Agg(
						"SUM".to_string(),
						Box::new(syn::Relation::lam(
							vec![Int],
							UExpr::Pred(Eq(Var(VL(0)), Var(VL(1)))),
						)),
					))),
				),
			) * UExpr::sum(vec![Int], UExpr::One)
	};
	println!("{}", syn);
	// let nom = nom::UExpr(vec![nom::Term::default(); 4]);
	// assert_eq!(syn.eval(env).eval(env), nom);
	println!("{}", syn.eval(env).eval(env));
}

#[test]
fn test_squashes() {
	let syn = {
		use syn::UExpr;
		use syn::UExpr::*;
		use DataType::*;
		use Expr::*;
		use Predicate::*;
		// UExpr::squash()
	};
}
