# The QED Prover

This is a SQL query equivalence prover in Rust aiming for high performance and large SQL feature coverage.
The project starts as a successor of the Cosette prover, which is described in [this paper](https://www.vldb.org/pvldb/vol11/p1482-chu.pdf).

## Install

### Build from source manually

The project relies on a nightly Rust compiler toolchain,
and additionally, `libclang` and header files for `z3` are needed as build-time dependencies.
Build the prover with
```sh
cargo build --release
```
would produce an executable `./target/release/qed-prover`.
The current setup of the prover has the Z3 *and* CVC5 solver as a runtime dependency,
so you need to have both the `z3` *and* `cvc5` executable in the `PATH` when running `qed-solver`.

### Build with Nix

Alternatively, if one has Nix and Nix flake in their environment, this project contains a flake for easy reproducibility.
Simply use
```sh
nix run github:qed-solver/prover -- <args>
```
to run the prover with arguments `<args>`.

To have a development environment with all the build-time and runtime dependencies, run `nix shell .` in the project's root.
For `direnv` users, a `.envrc` file is also prepared, so simply `cd` into the project directory, and `direnv` will try to reproduce the development environment.
(NOTICE: For first-time use, you need to explicitly trust the `.envrc` file, by executing `direnv allow .`)

## Usage

Normally, one invoke the parser as
```sh
qed-prover [input-path]...
```
where every `input-path` is a JSON file that represents a case to prove, or a directory containing such files.
Currently one can generate conforming JSON files using [this parser](https://github.com/qed-solver/parser) by passing in SQL statements.

During execution, the results will simply be printed out, with the names of every files followed by their result (provable/not provable).
One can use the environment variable `QED_SMT_TIMEOUT` to set a timeout for each SMT request the prover makes in milliseconds, which is defaulted to 10,000.
Setting the environment variable `RUST_LOG=info` when running would give a (very) verbose output.
This is useful for debugging as it prints out how expressions are simplified in the solver at various stages.

### Test cases

For convience, the directory `tests/calcite/` contains JSON files representing the query rewrite pairs use in the optimizer test suite of the [Calcite](https://calcite.apache.org/) project.
You may try out running these inputs by
```sh
qed-prover tests/calcite/
```
WARNING: some test cases in this folder contain features that we haven't support yet.
Now ~290 out of all ~440 cases are actually provable.

## Feature coverage

### Supported features

- Basic `SELECT-FROM-WHERE` queries
- Set operations (`UNION`, `UNION ALL`, `INTERSECT` (but not `INTERSECT ALL`), `EXCEPT`, and `EXCEPT ALL`)
- Joins (`INNER JOIN`, `LEFT`/`RIGHT`/`FULL` `OUTER JOIN`, `SEMI`/`ANTI` `JOIN`, and lateral/correlated join)
- `DISTINCT`
- `VALUES`
- Aggretation (as uninterpreted functions)
- `ORDER BY` and `LIMIT` (as uninterpreted operators)
- Value operations with subquery (`IN` and `EXISTS`)
- Unique key constraint
- Arbitrary `CHECK` constraints

### Planned features

- Foreign key constraint
- Law of excluded middle ($A + \neg A = 1$)

### Unsupported features

- Semantics of aggretations, such as understanding them as algebras over a monad
- Semantics of `ORDER BY` and `LIMIT` (requires temporarily modelling a table as list?)
