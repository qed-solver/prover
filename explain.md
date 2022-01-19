# Documentation

## Introduction

The purpose of this program is to check the equivalence between SQL queries based on normalization.
That is, we translate two SQL queries into two U-semiring expression and normalize them.
If the normalized forms agree, we know that the two SQL queries have the same semantics.

We follow the main idea of [normalization by evaluation](https://en.wikipedia.org/wiki/Normalisation_by_evaluation) (NBE) in order to normalize efficiently. When normalizing terms, we are picking a canonical term among an equivalence
class of syntactic terms that are considered to have the same "meaning", or semantics.
In other words, we define several rewrite rules that are intent to preserve semantics of terms and call terms to be
equivalent when there are a sequence of rewrites that relates them.
Hence one way of normalizing is to find out a proper way to apply rewrite rules such that an arbitrary term can be
rewritten to a normalized term.
NBE takes a different approach by designing a different domain of terms, called the semantic domain.
Terms in the semantic domain are meant to encode the semantics, such that syntactic terms with the same "meaning" are
encoded with the same semantic term.
We can then view normalization as a two state process:

1. Evaluate the input syntactic expression to a semantic value.
2. Read back a syntactic expression from the semantic value.

The tricky part of this process is the design of the semantic domain. Terms in the semantic domain should be designed to
conveniently encode meaning of terms and can have very different structure than a syntactic term. This vastly depends on
the language that we are trying to normalize. Here, we borrow some, but not all, techniques used
in [a dependent type theory implementation](https://github.com/jozefg/nbe-for-mltt/blob/master/nbe-explanation.md).

## Syntactic domain

We express a syntactic expression pretty straight forward as follows.
Notice that variables are represented using de-Bruijn levels.

```rust
enum UExpr {
    Zero,
    One,
    Add(Box<UExpr>, Box<UExpr>),
    Mul(Box<UExpr>, Box<UExpr>),
    Squash(Box<UExpr>),
    Not(Box<UExpr>),
    Sum(Vec<DataType>, Box<UExpr>),
    Pred(Predicate),
    App(Relation, Vec<VL>),
}
```

As described above, a syntactic expression will be later transformed into the semantic domain during evaluation.
Such transformation often involves changing the variable binding structures: some scopes might be removed, and some might got extended.
This means that the de-Bruijn levels of each variable have to change appropriately.
However, shifting the level everywhere is very expensive, and to deal with this, we use an auxiliary environment for changing variable levels.
An environment $E$ can be seen as a vector of variables.
When evaluating a syntactic term and stepping on a variable $l$, we use $E[l]$ as the variable in the semantic domain.
This can be very powerful as it allows arbitrary variable substitution.
Moreover, we want to sensibly push new variable substitution pairs into the environment such that the evaluation process can be done in one pass.
Similarly, when reading back a syntactic expression from the semantic domain, we construct an environment again to aid any variable scope changes.

## Semantic domain

To obtain a good design of the semantic domain, we need to inspect closely on our rewrite rules.
We can classify all rules into two types.

1. Rewrite rules from the property of U-semiring.  
   Repeatedly applying those rules on a term will give us sum-product normal form (SPNF).
2. Rewrite rules describing key constraints.
   These rules help cancels some subterms.

The second class of rewrite rules should be applied only after getting SPNF.
We first consider the design of semantic domain when only normalizing up to SPNF.
A U-semiring expression in SPNF is written as additions of normalized terms
$$
E = T_1 + T_2 + \cdots + T_n.
$$
Where every term $T_i$ is of the form
$$ T_i = \sum_{v_1, v_2, \ldots, v_n} [P_1] \times \cdots \times [P_k] \times \| E' \| \times \neg E'' \times R(v_i, \ldots) \times S(v_j \ldots) \times \cdots.
$$
Naturally, in the semantic domain, we can have the following definition for a U-semiring expression.

```rust
struct UExpr(Vec<Term>);
```

And the definition for a term is

```rust
struct Term {
    preds: Vec<Predicate>,
    squash: Option<Box<UExpr>>,
    not: Option<Box<UExpr>>,
    apps: Vec<Application>,
    sums: Vec<Summation>,
}
```

where the `preds`, `squash`, `not`, and `apps` are meant to be multiplied together to form a product. One special thing
of such representation is the way we encode summations in a term.

```rust
struct Summation {
    types: Vec<DataType>,
    summand: Closure,
}

struct Closure {
    body: syn::UExpr,
    env: Env,
}
```

Here a summation is left as an unevaluated closure, which still contains a syntactic U-expression as its body. The `sum`
field in `Term` is a product of summation. However, this does not seems to correspond to a fully normalized term. Since
$(\sum_a S_1[a]) \times (\sum_b S_2[b])$ really should be further normalized as $\sum_{a, b} S_1[a] \times S_2[b]$. We
are still normalizing this, but delayed the process till reading back. If we eagerly evaluate $(\sum_a S_1[a]) \times (
\sum_b S_2[b])$ by separately evaluate the body of each summation, and suppose the summand $S_1[a]$ evaluated with
variable $a$ having de-Bruijn level $l$. The summand $S_2[b]$ will also evaluate with variable $b$ having level $l$.
However, in the normalized result $(\sum_a S_1[a]) \times (\sum_b S_2[b])$, we are expecting $b$ to have a higher level
than $a$. If we don't want to pay the price of constantly shifting variable levels when multiplying summations, we can
delay evaluation of summations after all multiplications of summations are collected. Once we know all summations being
multiplied in a term, we can evaluate each summation with the appropriate de-Bruijn level in one pass.
