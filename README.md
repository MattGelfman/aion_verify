# aion_verify

[![crates.io](https://img.shields.io/crates/v/aion_verify.svg)](https://crates.io/crates/aion_verify)
[![docs.rs](https://docs.rs/aion_verify/badge.svg)](https://docs.rs/aion_verify)
[![license](https://img.shields.io/crates/l/aion_verify.svg)](#license)

**An exhaustive bounded proof engine for Rust.** Check a predicate against **every** input in a
finite or bounded domain and get back either a proof (`Proven { cases }` — complete coverage) or the
**exact counterexample** that broke it (`Refuted`). Not a random sample — the whole space.

- **`no_std`**, **zero dependencies**, `#![forbid(unsafe_code)]`.
- A real *proof* over the domain, not property-based fuzzing: if it says `Proven`, every input was checked.
- Returns the counterexample on failure, so a red result is immediately actionable.

## Why

Property-based testing (proptest, quickcheck) *samples* an input space and can miss the one value that
breaks your invariant. Symbolic model checkers (like [Kani](https://github.com/model-checking/kani))
prove properties over astronomically large spaces with a SAT/SMT backend, but need a toolchain and can
be slow. For the very common case of a **finite or small bounded** domain — every `u8`, a range, a
cartesian product of a few slices — you can just check *all of it*, fast, in plain safe Rust. That's
`aion_verify`.

It was built as the tier-4 engine of the AION OS verification stack, alongside Kani as the independent
tier-5 formal check. It complements Kani; it does not replace it.

## Example

```rust
use aion_verify::{for_all_u8, for_all_in, for_all_pairs};

// Prove a property over the entire u8 domain (all 256 values):
let v = for_all_u8(|x| (x as u16) + 1 > x as u16);
assert!(v.is_proven());
assert_eq!(v.cases(), 256); // every input checked — a proof

// A failing property hands you the counterexample:
let v = for_all_u8(|x| x < 200);
assert_eq!(v.counterexample(), Some(&200u8));

// Bounded ranges and cartesian products of finite domains:
let v = for_all_in(0, 1000, |x| x * 2 >= x);
assert!(v.is_proven());

let a = [1u32, 2, 3];
let b = [10u32, 20];
let v = for_all_pairs(&a, &b, |&x, &y| x + y == y + x);
assert!(v.is_proven());
```

## API

| Combinator | Domain |
| --- | --- |
| `for_all(iter, pred)` | every item of any finite iterator |
| `for_all_where(iter, precond, pred)` | items satisfying a precondition (like a `kani::assume` guard) |
| `for_all_u8(pred)` | the full `u8` domain (256 values) |
| `for_all_in(lo, hi, pred)` | the inclusive range `[lo, hi]` |
| `for_all_pairs(&a, &b, pred)` | the cartesian product `a × b` (binary invariants) |

Each returns a `Verdict<T>`: `is_proven()`, `cases()`, and `counterexample() -> Option<&T>`.

## Tier 5 — symbolic proofs over *unbounded* domains (`symbolic` module)

Tier 4 enumerates, so it needs a finite domain. Tier 5 proves properties over the **entire** domain —
including all 2^64 values of `u64` — **without enumerating it**, by interval abstract interpretation.
Because it must *reason about* an expression (not just call it), tier-5 predicates use a small
first-party `Expr`/`Prop` DSL:

```rust
use aion_verify::symbolic::{prove_forall, Expr, Iv, Prop, SymVerdict};

// Prove `(x & 0xFF) <= 255` for EVERY u64 — symbolically, no enumeration:
let p = Prop::Le(Expr::var().and(0xFF), Expr::c(255));
assert_eq!(prove_forall(Iv::full(), &p), SymVerdict::Proven);

// A false property comes back with a concrete witness:
let q = Prop::Le(Expr::var(), Expr::c(100));
matches!(prove_forall(Iv::full(), &q), SymVerdict::Refuted { .. });
```

**Multiple variables and function contracts.** Variables are addressed by index (`Expr::var_at(i)`),
and `prove_contract(&doms, &precond, &postcond)` proves `precond -> postcond` over the variables'
domains — the core of verifying a function or component (validate inputs, guarantee the postcondition):

```rust
use aion_verify::symbolic::{prove_contract, Expr, Iv, Prop, SymVerdict};

// Contract over x ∈ [0,1000]: if x <= 1000 then x + 1 <= 1001.
let pre  = Prop::Le(Expr::var(), Expr::c(1000));
let post = Prop::Le(Expr::var().add(Expr::c(1)), Expr::c(1001));
assert_eq!(prove_contract(&[Iv::new(0, 1000)], &pre, &post), SymVerdict::Proven);
```

`SymVerdict` is `Proven` (holds for all), `Refuted { witness }` (a real counterexample — a value per
variable), or `Unknown`
(the interval abstraction was too weak) — **never a false Proven or Refuted**. Pure Rust, no external
solver.

## When to reach for something else

The interval domain is non-relational and single-variable, so tier 5 returns `Unknown` on correlated
or higher-arity properties it can't yet decide (that's soundness, not a bug). For those, a mature
symbolic tool such as [Kani](https://github.com/model-checking/kani) remains a good complement while
this engine's decision procedures grow.

## License

Licensed under the **[Mozilla Public License 2.0](LICENSE)** (MPL-2.0) — a file-level copyleft.

In plain terms: you can use `aion_verify` in any project, including proprietary ones, **but any
modifications you make to its source files must themselves be released under the MPL-2.0** (i.e. kept
open source). Improvements to the engine stay free for everyone; the wider project you build around it
does not have to be. Contributions submitted for inclusion are licensed under the same terms.

> Note: `0.1.0` was briefly published under MIT/Apache-2.0 and has been yanked; `0.2.0` onward is MPL-2.0.
