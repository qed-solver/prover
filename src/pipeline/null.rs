use paste::paste;
use z3::ast::{forall_const, Ast, Bool, Datatype, Dynamic, Int, Real, String};
use z3::{DatatypeAccessor, DatatypeBuilder, DatatypeSort, FuncDecl, Pattern, Solver, Sort};

macro_rules! repeat_with {
	($_t:tt $sub:expr) => {
		$sub
	};
}

macro_rules! optional_op {
    ($($env:tt),*; $name:ident ($($v:ident),*)) => {
		optional_op!($($env)*; fix $name $($v)*)
	};
    ($($env:tt),*; $name:ident [$($v:ident),*]) => {
		optional_op!($($env)*; var $name $($v)*)
	};
	($solver:ident $sort:ident $ilsort:ident $olsort:ident; $mode:ident $name:ident $($v:ident)*) => {
		let input_sort = &$ilsort.sort;
		let output_sort = &$olsort.sort;
		let ctx = $solver.get_context();
		let func = FuncDecl::new(
			ctx,
			format!("n-{}-{}", stringify!($ilsort), stringify!($name)),
			&[$(repeat_with!($v input_sort)),*],
			output_sort
		);
		$(let $v = &Datatype::fresh_const(ctx, "v", input_sort) as &dyn Ast;)*
		let vars = &[$($v),*];
		let f_vs = &func.apply(vars);
		let input_none = &$ilsort.variants[0];
		let input_some = &$ilsort.variants[1];
		let output_none = &$olsort.variants[0];
		let output_some = &$olsort.variants[1];
		let body = f_vs._eq(optional_op!(ctx $sort input_none input_some output_none output_some; $mode ($($v)*) ($name $($v)*)));
		let p = Pattern::new(ctx, &[f_vs]);
		let f_def = forall_const(ctx, vars, &[&p], &body);
		$solver.assert(&f_def);
	};
	($ctx:ident $sort:ident $inone:ident $isome:ident $onone:ident $osome:ident; $mode:ident ($v:ident $($tail:ident)*) ($name:ident $($vs:ident)*)) => {
		&$inone.tester.apply(&[$v]).as_bool().unwrap().ite(
			&$onone.constructor.apply(&[]),
			optional_op!($ctx $sort $inone $isome $onone $osome; $mode ($($tail)*) ($name $($vs)*))
		)
	};
	($ctx:ident $sort:ident $inone:ident $isome:ident $onone:ident $osome:ident; fix () ($name:ident $($v:ident)*)) => {
		{
			paste!($(let $v = &$isome.accessors[0].apply(&[$v]).[<as_$sort:snake>]().unwrap();)*);
			&$osome.constructor.apply(&[&$sort::$name($(&$v),*)])
		}
	};
	($ctx:ident $sort:ident $inone:ident $isome:ident $onone:ident $osome:ident; var () ($name:ident $($v:ident)*)) => {
		{
			paste!($(let $v = &$isome.accessors[0].apply(&[$v]).[<as_$sort:snake>]().unwrap();)*);
			&$osome.constructor.apply(&[&$sort::$name($ctx, &[$(&$v),*])])
		}
	}
}

macro_rules! optional_fn {
    ($ilsort:ident $olsort:ident $name:ident ($($v:ident),* $(,)*)) => {
        paste!(
			#[allow(non_snake_case)]
			#[allow(dead_code)]
			pub fn [<$ilsort _ $name>] (&self, $($v: &Dynamic<'c>),*) -> Dynamic<'c> {
            let input_sort = &self.$ilsort.sort;
			let output_sort = &self.$olsort.sort;
            let func = FuncDecl::new(
				self.solver.get_context(),
				format!("n-{}-{}", stringify!($ilsort), stringify!($name)),
				&[$(repeat_with!($v input_sort)),*],
				output_sort
			);
            func.apply(&[$($v),*])
        });
    };
    ($ilsort:ident $olsort:ident $name:ident [$($v:ident),* $(,)*]) => {
        optional_fn!($ilsort $olsort $name ($($v),*));
    };
}

macro_rules! ctx_impl {
    ($($sort:ident {$($def:ident $args:tt -> $ret:ident);* $(;)*});* $(;)*) => {
        paste!(ctx_impl!($($sort [<$sort:snake>] $($def $args [<$ret:snake>]),*);*););
    };
    ($($sort:ident $lsort:ident $($def:ident $args:tt $olsort:ident),*);*) => {
		pub struct Ctx<'c> {
			pub solver: Solver<'c>,
			$(pub $lsort: DatatypeSort<'c>),*
		}

        impl<'c> Ctx<'c> {
            pub fn new(solver: Solver<'c>) -> Self {
                let ctx = solver.get_context();
                $(let $lsort = DatatypeBuilder::new(ctx, format!("Option<{}>", stringify!($sort)))
                    .variant(&format!("None{}", stringify!($sort)), vec![])
                    .variant("Some", vec![("val", DatatypeAccessor::Sort(Sort::$lsort(ctx)))])
                    .finish();)*
				$($(optional_op!(solver, $sort, $lsort, $olsort; $def $args));*);*;
                Self { solver, $($lsort),* }
            }
            $($(optional_fn!($lsort $olsort $def $args);)*)*
			paste!($(
			pub fn [<$lsort _none>](&self) -> Dynamic<'c> {
				self.$lsort.variants[0].constructor.apply(&[])
			}
			pub fn [<$lsort _some>](&self, val: $sort<'c>) -> Dynamic<'c> {
				self.$lsort.variants[1].constructor.apply(&[&val])
			}
			)*);
        }
    }
}

ctx_impl!(
	Real {
		add[a, b] -> Real;
		sub[a, b] -> Real;
		mul[x, y] -> Real;
		unary_minus(x) -> Real;
		div(x, y) -> Real;
		// power(x, y) -> Real;
		lt(x, y) -> Bool;
		le(x, y) -> Bool;
		gt(x, y) -> Bool;
		ge(x, y) -> Bool;
		_eq(x, y) -> Bool;
	};
	Int {
		add[a, b] -> Int;
		sub[x, y] -> Int;
		mul[x, y] -> Int;
		unary_minus(x) -> Int;
		div(x, y) -> Int;
		// rem(x, y) -> Int;
		modulo(x, y) -> Int;
		// power(x, y) -> Int;
		lt(x, y) -> Bool;
		le(x, y) -> Bool;
		gt(x, y) -> Bool;
		ge(x, y) -> Bool;
		_eq(x, y) -> Bool;
		to_real(x) -> Real;
	};
	Bool {
		not(x) -> Bool;
		_eq(x, y) -> Bool;
	};
	String {
		concat[x, y] -> String;
		contains(x, y) -> Bool;
		prefix(x, y) -> Bool;
		suffix(x, y) -> Bool;
		lt(x, y) -> Bool;
		le(x, y) -> Bool;
		gt(x, y) -> Bool;
		ge(x, y) -> Bool;
		_eq(x, y) -> Bool;
	};
);

impl<'c> Ctx<'c> {
	pub fn int_add_v(&self, args: &[&Dynamic<'c>]) -> Dynamic<'c> {
		args.iter().fold(self.int_some(Int::from_i64(self.solver.get_context(), 0)), |a, b| {
			self.int_add(&a, b)
		})
	}

	pub fn int_sub_v(&self, args: &[&Dynamic<'c>]) -> Dynamic<'c> {
		match *args {
			[] => self.int_some(Int::from_i64(self.solver.get_context(), 0)),
			[arg] => self.int_unary_minus(arg),
			[arg, ref args @ ..] => args.iter().fold(arg.clone(), |a, b| self.int_sub(&a, b)),
		}
	}

	pub fn int_mul_v(&self, args: &[&Dynamic<'c>]) -> Dynamic<'c> {
		args.iter().fold(self.int_some(Int::from_i64(self.solver.get_context(), 1)), |a, b| {
			self.int_mul(&a, b)
		})
	}

	pub fn real_add_v(&self, args: &[&Dynamic<'c>]) -> Dynamic<'c> {
		args.iter()
			.fold(self.real_some(Real::from_real(self.solver.get_context(), 0, 1)), |a, b| {
				self.real_add(&a, b)
			})
	}

	pub fn real_sub_v(&self, args: &[&Dynamic<'c>]) -> Dynamic<'c> {
		match *args {
			[] => self.real_some(Real::from_real(self.solver.get_context(), 0, 1)),
			[arg] => self.real_unary_minus(arg),
			[arg, ref args @ ..] => args.iter().fold(arg.clone(), |a, b| self.real_sub(&a, b)),
		}
	}

	pub fn real_mul_v(&self, args: &[&Dynamic<'c>]) -> Dynamic<'c> {
		args.iter()
			.fold(self.real_some(Real::from_real(self.solver.get_context(), 1, 1)), |a, b| {
				self.real_mul(&a, b)
			})
	}

	pub fn bool_is_true(&self, expr: &Dynamic<'c>) -> Bool<'c> {
		let ctx = self.solver.get_context();
		self.bool.variants[0].tester.apply(&[expr]).as_bool().unwrap().ite(
			&Bool::from_bool(ctx, false),
			&self.bool.variants[1].accessors[0].apply(&[expr]).as_bool().unwrap(),
		)
	}

	pub fn bool_and_v(&self, args: &[&Dynamic<'c>]) -> Dynamic<'c> {
		args.iter()
			.fold(self.bool_some(Bool::from_bool(self.solver.get_context(), true)), |a, b| {
				self.bool_and(&a, b)
			})
	}

	pub fn bool_or_v(&self, args: &[&Dynamic<'c>]) -> Dynamic<'c> {
		args.iter()
			.fold(self.bool_some(Bool::from_bool(self.solver.get_context(), false)), |a, b| {
				self.bool_or(&a, b)
			})
	}

	pub fn bool_and(&self, e1: &Dynamic<'c>, e2: &Dynamic<'c>) -> Dynamic<'c> {
		let ctx = self.solver.get_context();
		self.bool.variants[0].tester.apply(&[e1]).as_bool().unwrap().ite(
			// NULL, b
			&self.bool.variants[0].tester.apply(&[e2]).as_bool().unwrap().ite(
				// NULL, NULL
				e2,
				// NULL, Some(b)
				&self.bool.variants[1].accessors[0].apply(&[e2]).as_bool().unwrap().ite(
					// NULL, Some(True)
					&self.bool_none(),
					// NULL, Some(False)
					e2,
				),
			),
			// Some(a), b
			&self.bool.variants[1].accessors[0].apply(&[e1]).as_bool().unwrap().ite(
				// Some(True), b
				e2,
				// Some(False), b
				&self.bool_some(Bool::from_bool(ctx, false)),
			),
		)
	}

	pub fn bool_or(&self, e1: &Dynamic<'c>, e2: &Dynamic<'c>) -> Dynamic<'c> {
		let ctx = self.solver.get_context();
		self.bool.variants[0].tester.apply(&[e1]).as_bool().unwrap().ite(
			// NULL, b
			&self.bool.variants[0].tester.apply(&[e2]).as_bool().unwrap().ite(
				// NULL, NULL
				e2,
				// NULL, Some(b)
				&self.bool.variants[1].accessors[0].apply(&[e2]).as_bool().unwrap().ite(
					// NULL, Some(True)
					e2,
					// NULL, Some(False)
					&self.bool_none(),
				),
			),
			// Some(a), b
			&self.bool.variants[1].accessors[0].apply(&[e1]).as_bool().unwrap().ite(
				// Some(True), b
				&self.bool_some(Bool::from_bool(ctx, true)),
				// Some(False), b
				e2,
			),
		)
	}
}
