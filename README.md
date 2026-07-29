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

### Vacuity — when a passing proof proves nothing

A proof over an empty domain trivially succeeds. If `for_all_where`'s precondition rejects every
input, the verdict is `Proven { cases: 0 }`: nothing was tested, yet `is_proven()` returns `true`.
This is the most common way a proof suite quietly stops proving anything — a precondition drifts out
of sync with the domain, and the tests stay green.

```rust
use aion_verify::for_all_where;

let hi = core::hint::black_box(100u8);
// No u8 is both > 200 and < 100, so the predicate below is never even reached.
let v = for_all_where(0u8..=255, |&x| x > 200 && x < hi, |_| false);

assert!(v.is_proven());            // reads as success
assert!(v.is_vacuous());           // but nothing was checked
assert!(!v.is_proven_nonvacuous()); // the assertion you actually want
```

Prefer **`is_proven_nonvacuous()`** in test assertions. It is `is_proven()` plus the requirement that
at least one input reached the predicate.

One caveat, stated plainly: this catches an *empty domain*, not a *trivial predicate*. A predicate
like `|x: i8| x <= 127` is true by the type's own range and proves nothing about the code under test,
but it is indistinguishable from a hard-won property by enumeration alone. Guard against that by
comparing against an independently computed reference value, or by checking that the proof fails when
you deliberately mutate the implementation.

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

**Correlated properties via refinement.** A plain interval domain is non-relational, so it returns
`Unknown` on properties that couple a variable to itself (e.g. `(x >> 1) <= x`). `prove_forall_refine`
recovers these with **branch-and-bound**: when a box is undecided it bisects the widest variable and
proves each half (the property holds on the whole iff it holds on both), up to a split budget — still
sound, and `Unknown` if the budget runs out.

```rust
use aion_verify::symbolic::{prove_forall_refine, Expr, Iv, Prop, SymVerdict};
let p = Prop::Le(Expr::var().shr(1), Expr::var());          // correlated, true for all u64
assert_eq!(prove_forall_refine(&[Iv::full()], &p, 256), SymVerdict::Proven);
```

**Loops & state via inductive invariants.** Everything above reasons about *values*. `prove_inductive`
reasons about a *loop*: it proves a property holds on **every** iteration by induction — **initiation**
(it holds in the initial states) plus **consecution** (if it holds and the guard is true, it still holds
after one transition) — with no unrolling. Consecution uses **assume-narrowing**: the invariant and guard
are assumed by shrinking the state box first, so the proof lands over **unbounded** state (the whole
`u64` range) with no splitting. A non-inductive invariant is refuted with the concrete state that breaks it.

```rust
use aion_verify::symbolic::{prove_inductive, Expr, Iv, Prop, SymVerdict};
// A counter starting at 5 that only increments: prove `i >= 5` on every iteration, over ALL of u64.
let init = &[Iv::new(5, 5)];
let guard = Prop::Le(Expr::var(), Expr::c(1_000_000_000));   // loop while i <= 1e9
let step = &[Expr::var().add(Expr::c(1))];                   // i' = i + 1
let inv = Prop::Ge(Expr::var(), Expr::c(5));                 // i >= 5
assert_eq!(prove_inductive(init, &guard, step, &inv, &[Iv::full()], 8), SymVerdict::Proven);
```

## Tamper-evident proof ledger (`ledger` module)

A proof is only trustworthy if its result can't be quietly forged or deleted. `ledger` records each
verdict in a **hash chain** (with a self-contained pure-Rust **SHA-512**): every entry carries the hash
of the one before it, so altering *any* past record — or deleting one — changes every hash after it and
is caught by `verify()`.

```rust
use aion_verify::ledger::Ledger;
use aion_verify::pqsig::{keygen, sign, verify};

let mut log = Ledger::new();
log.record("x + 1 > x over u8", true);   // a proven result
log.record("x <= 100 over u64", false);  // a refuted result, recorded just the same
let head = log.head();                   // 64-byte fingerprint of the whole history
assert_eq!(log.verify(), Ok(()));        // an untampered chain verifies

// Sign the head with a POST-QUANTUM (hash-based WOTS) signature so the log is provably yours:
let seed = [7u8; 64];                    // one-time secret; never reuse
let public_key = keygen(&seed);          // publish this as the anchor
let seal = sign(&seed, &head);
assert!(verify(&public_key, &head, &seal));
```

Persist the entries, reload with `Ledger::from_entries(..)`, and `verify()` again to detect any on-disk
tampering. Publish the public key + signed head; a later divergence is proof the log was cut or rewritten.

**Post-quantum.** The whole scheme rests only on SHA-512 — hashes are quantum-resistant (Grover is just a
quadratic speedup, and SHA-512 keeps a full 256-bit collision margin), and the signature is hash-based
(WOTS), so nothing here falls to Shor's algorithm. No RSA/ECC anywhere. It's a blockchain's core guarantee
(an immutable, verifiable, *signed* history) without the distributed-consensus machinery a single
authority doesn't need. (WOTS is one-time per key — lift to many-time with XMSS/SPHINCS+ over the same
primitive.)

## When to reach for something else

Linear relational facts (a variable compared against a linear combination of itself and others, like
`x <= x + y`) are proven directly by an **affine layer** that cancels shared terms — no splitting, sound
under u64 wrapping (it only applies where the operands provably can't overflow). Beyond that, refinement
is bounded by its split budget, and neither it nor the interval domain handles arbitrary
non-linear or unbounded-arity logic. For those, a mature symbolic tool such as
[Kani](https://github.com/model-checking/kani) remains a good complement while this engine's decision
procedures grow.

## License

Licensed under the **[Mozilla Public License 2.0](LICENSE)** (MPL-2.0) — a file-level copyleft.

In plain terms: you can use `aion_verify` in any project, including proprietary ones, **but any
modifications you make to its source files must themselves be released under the MPL-2.0** (i.e. kept
open source). Improvements to the engine stay free for everyone; the wider project you build around it
does not have to be. Contributions submitted for inclusion are licensed under the same terms.

> Note: `0.1.0` was briefly published under MIT/Apache-2.0 and has been yanked; `0.2.0` onward is MPL-2.0.
