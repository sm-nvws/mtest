# spartan-rs

a small dependent type checker in rust, based on andrej bauer's spartan type theory. the main artifact is a machine-checked proof of the weierstrass m-test, built on top of a real analysis axiom set.

## what it does

the checker implements a bidirectional type checker for a dependent type theory with:

- pi types (dependent functions) and sigma types (dependent pairs)
- natural numbers with an eliminator
- universe levels with constraint-based inference and a solver
- a global signature of axioms and definitions
- normalization by evaluation (nbe) for definitional equality

on startup it builds a real analysis context: reals, nat, arithmetic ops, cauchy sequences, uniform convergence, completeness. it then checks three things in order:

1. the cauchy criterion (from completeness)
2. uniform convergence from cauchy + majorization
3. the weierstrass m-test statement

if all three check and the level constraints are consistent, it prints `proof accepted.`

## project layout

```
src/
  arena.rs      ; bump-style arena; terms live as TermId<'scope> tied to a stack lifetime
  term.rs       ; syntactic term enum (TermData); pi, sigma, lam, app, nat, etc.
  value.rs      ; semantic values and neutrals for nbe
  norm.rs       ; eval, apply, quote, def_eq
  check.rs      ; bidirectional type checker; check/infer + elim rules
  level.rs      ; universe level variables, constraints, and the solver
  context.rs    ; typing context (de bruijn, values)
  env.rs        ; evaluation environment (de bruijn, values)
  signature.rs  ; global map of axioms and definitions
  axioms.rs     ; the real-analysis axiom set + m-test statement and proofs
  error.rs      ; TyError via thiserror + miette diagnostics
  main.rs       ; entry point; runs the three proof checks
tests/
  integration.rs  ; end-to-end proof check, nat eval, level solver tests
```

## running

```sh
cargo run    # checks the m-test and prints "proof accepted."
cargo test   # runs integration tests
```

requires rust 2024 edition (rustup stable should be fine).

## design notes

**arena and lifetimes.** all terms are allocated into an `Arena<'scope>` whose lifetime is scoped via `with_scope`. `TermId<'scope>` is a branded index; the phantom lifetime prevents ids from escaping their arena. no gc needed.

**nbe.** evaluation produces `Value<'scope>`; `quote` reifies values back to terms for equality checking. definitional equality is checked by quoting both sides and comparing normal forms.

**universe levels.** `Type` carries a `LevelVar`; subtyping constraints are collected during checking and solved at the end with a simple unification-based worklist solver. inconsistency (e.g. `Succ(l) <= Zero`) is reported as an error.

**axioms vs defs.** the signature distinguishes axioms (opaque; evaluate to `VConst`) from definitions (transparent; unfold on eval). the analysis context is all axioms; proofs are terms that reference them.

## license

MIT