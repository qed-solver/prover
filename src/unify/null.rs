use std::marker::PhantomData;

use paste::paste;
use z3::ast::{forall_const, Ast, Bool, Datatype, Dynamic, Int, Real, String};
use z3::{
	Context, DatatypeAccessor, DatatypeBuilder, DatatypeSort, DatatypeVariant, FuncDecl, Pattern,
	Solver, Sort,
};

pub struct Nullable<'ctx, T> {
	ctx: &'ctx Context,
	datatype: DatatypeSort<'ctx>,
	_v: PhantomData<T>,
}

impl<'ctx, T: Into<Dynamic<'ctx>>> Nullable<'ctx, T> {
	fn new(ctx: &'ctx Context, datatype: DatatypeSort<'ctx>) -> Self {
		Nullable { ctx, datatype, _v: PhantomData }
	}

	pub fn some(&self, val: T) -> Dynamic {
		self.datatype.variants[1].constructor.apply(&[&val.into()])
	}

	pub fn null(&self) -> Dynamic {
		self.datatype.variants[0].constructor.apply(&[])
	}
}

macro_rules! optional_op {
	($($env:tt),*; $name:ident ($($v:ident),*)) => {
		optional_op!($($env)*; fix $name $($v)*)
	};
	($($env:tt),*; $name:ident [$($v:ident),*]) => {
		optional_op!($($env)*; var $name $($v)*)
	};
	($solver:ident $sort:tt $osort:ident $some:ident $none:ident; $mode:ident $name:ident $($v:ident)*) => {
		let ctx = $solver.get_context();
		let func =
			FuncDecl::new(ctx, format!("n-{}", stringify!($name)), &[$osort], $osort);
		$(let $v = &Datatype::fresh_const(ctx, "v", $osort) as &dyn Ast;)*
		let vars = &[$($v),*];
		let f_vs = &func.apply(vars);
		let body = f_vs._eq(optional_op!(ctx $sort $some $none; $mode ($($v)*) ($name $($v)*)));
		let p = Pattern::new(ctx, &[f_vs]);
		let f_def = forall_const(ctx, vars, &[&p], &body);
		$solver.assert(&f_def);
	};
    ($ctx:ident $sort:tt $some:ident $none:ident; $mode:ident ($v:ident $($tail:ident)*) ($name:ident $($vs:ident)*)) => {
		&$none.tester.apply(&[$v]).as_bool().unwrap().ite(
			&$none.constructor.apply(&[]),
			optional_op!($ctx $sort $some $none; $mode ( $($tail)* ) ($name $($vs)*))
		)
	};
	($ctx:ident $sort:tt $some:ident $none:ident; fix () ($name:ident $($v:ident)*)) => {
		{
			paste!($(let $v = &$some.accessors[0].apply(&[$v]).[<as_ $sort:snake>]().unwrap();)*);
			&$some.constructor.apply(&[&$sort::$name($(&$v),*)])
		}
	};
	($ctx:ident $sort:tt $some:ident $none:ident; var () ($name:ident $($v:ident)*)) => {
		{
			paste!($(let $v = &$some.accessors[0].apply(&[$v]).[<as_ $sort:snake>]().unwrap();)*);
			&$some.constructor.apply(&[&$sort::$name($ctx, &[$($v),*])])
		}
	};
}

macro_rules! optional_fn {
	($name:ident ($($v:ident),* $(,)*)) => {
		fn $name(&self, $($v: &Dynamic<'ctx>),*) -> Dynamic<'ctx> {
			let sort = &self.datatype.sort;
			let func = FuncDecl::new(self.ctx, format!("n-{}", stringify!($name)), &[sort], sort);
			func.apply(&[$($v),*])
		}
	};
	($name:ident [$($v:ident),* $(,)*]) => {
		optional_fn!($name ($($v),*));
	};
}

macro_rules! nullable {
	($sort:tt {$($def:ident $args:tt);* $(;)*}) => {
		paste!(nullable!($sort [<$sort:snake>] $($def $args),*););
	};
	($sort:tt $lsort:ident $($def:ident $args:tt),*) => {
		impl<'ctx> Nullable<'ctx, $sort<'ctx>> {
			pub fn setup(solver: &Solver<'ctx>) -> Self {
				let ctx = solver.get_context();
				let optional = DatatypeBuilder::new(ctx, format!("Option{}", stringify!($sort)))
					.variant("none", vec![])
					.variant("some", vec![("val", DatatypeAccessor::Sort(Sort::$lsort(ctx)))])
					.finish();
				let none = &optional.variants[0];
				let some = &optional.variants[1];
				let optional_sort = &optional.sort;
				$(optional_op!(solver, $sort, optional_sort, some, none; $def $args);)*
				Nullable::new(ctx, optional)
			}

			$(optional_fn!($def $args);)*
		}
	};
}

nullable!(Real {
	add[x, y];
	sub[x, y];
	mul[x, y];
	unary_minus(x);
	div(x, y);
	power(x, y);
	lt(x, y);
	le(x, y);
	gt(x, y);
	ge(x, y);
});

nullable!(Int {
	add[x, y];
	sub[x, y];
	mul[x, y];
	unary_minus(x);
	div(x, y);
	rem(x, y);
	modulo(x, y);
	power(x, y);
	lt(x, y);
	le(x, y);
	gt(x, y);
	ge(x, y);
});

nullable!(Bool {
	not(x);
});

nullable!(String {
	concat[x, y];
	contains(x, y);
	prefix(x, y);
	suffix(x, y);
});
