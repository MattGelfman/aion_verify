// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! AION OS — first-party proof engine (`aion_verify`).
//!
//! It checks a predicate against **every** input in a bounded domain and returns a [`Verdict`] of either
//! `Proven { cases }` (complete coverage — a proof) or `Refuted` **with the counterexample** that broke
//! it. Over that domain the guarantee is the real thing: not a sample, the whole space.
//!
//! # Automatic properties — not just the predicate you write
//!
//! A bounded model checker like Kani verifies properties you never stated: index-out-of-bounds,
//! arithmetic overflow, `unwrap` on `None`, division by zero. Those follow from the language, not from
//! anything the author asserted. Two modules cover that ground here, by different routes:
//!
//! - [`safety::verify_no_panic`] runs the code over every input in a bounded domain and catches any
//!   unwind. Rust already emits those checks as panics, so exhaustive execution proves no input in the
//!   domain can panic. Requires the `std` feature and an unwinding profile.
//! - [`symbolic::prove_no_overflow`] answers the same question *symbolically*, over unbounded domains
//!   and independent of the build profile — which matters because Rust only panics on integer overflow
//!   under `debug-assertions`, and wraps silently in release.
//!
//! # What this still is not
//!
//! Two real gaps remain against a compiler-driven checker, and they are worth stating plainly:
//!
//! - **It does not read your code.** Kani compiles actual Rust MIR and reasons about the program as
//!   written. Tier 4 here executes a closure you hand it; tier 5 analyses an [`symbolic::Expr`] you
//!   build by hand. Modelling a function as an `Expr` is manual work, and a model that drifts from the
//!   implementation proves things about the model, not the code.
//! - **It only covers code that is reached.** Tier 4 covers exactly the paths the enumerated inputs
//!   take, and cannot see a function nobody called. Kani, being compiler-driven, has no such limit.
//!
//! Also inherent to the approach: concrete enumeration cannot span astronomically large domains (tier 5
//! exists for that, at the cost of `Unknown` answers where the interval abstraction loses precision),
//! and a passing verdict can still be hollow — see [`Verdict::is_vacuous`].
//!
//! So `aion_verify` is the everyday, zero-dependency engine for bounded invariants and automatic
//! arithmetic safety, and **Kani remains the independent, third-party formal check**. It complements
//! Kani; it does not replace it.
//!
//! `no_std`, `#![forbid(unsafe_code)]`.
#![forbid(unsafe_code)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

/// Automatic safety checking — panics (index-out-of-bounds, overflow, `unwrap`, division by zero)
/// found without writing a predicate, the way a bounded model checker does. Requires the `std`
/// feature. See [`safety`].
#[cfg(feature = "std")]
pub mod safety;

/// TIER 5 — symbolic verification over unbounded domains (interval abstract interpretation). Proves
/// properties over *all* of `u64` without enumerating it, entirely in first-party Rust. See [`symbolic`].
pub mod symbolic;

/// A tamper-evident, append-only hash-chain [`ledger`] (with a pure-Rust SHA-512) for recording proof
/// results so they cannot be forged or silently deleted.
pub mod ledger;

/// Post-quantum authenticity: a hash-based (WOTS) [`pqsig`] signature over the ledger head, so the log
/// is provably yours and immune to Shor's algorithm — using only SHA-512, still zero-dependency.
pub mod pqsig;

/// Many-time post-quantum signatures: a Merkle tree ([`mss`], XMSS-style) over the one-time WOTS, so
/// one published root signs `2^height` proofs from a single key.
pub mod mss;

/// The outcome of a proof attempt over a domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict<T> {
    /// The predicate held for every one of `cases` inputs — a proof over the domain.
    Proven { cases: u64 },
    /// The predicate failed; `counterexample` is the input that broke it, after `checked` passing inputs.
    Refuted { counterexample: T, checked: u64 },
}

impl<T> Verdict<T> {
    /// True when the predicate was never refuted.
    ///
    /// **Caution — this is true for a vacuous proof.** A `Proven { cases: 0 }` verdict means the
    /// predicate was never actually evaluated, because the domain was empty or a precondition filtered
    /// every input out. Prefer [`is_proven_nonvacuous`](Self::is_proven_nonvacuous) in assertions.
    pub fn is_proven(&self) -> bool {
        matches!(self, Verdict::Proven { .. })
    }

    /// True when the verdict is `Proven` but **zero inputs were checked** — a vacuous proof.
    ///
    /// This is the classic vacuity problem from model checking. `for_all_where(inputs, precond, pred)`
    /// reports `Proven` when `precond` rejected every input: nothing was tested, so nothing was proven,
    /// yet the verdict reads as success. The usual cause is a precondition that over-constrains — an
    /// `assume` that is stricter than the author believed, or that contradicts the domain outright.
    ///
    /// ```
    /// use aion_verify::for_all_where;
    /// // No u8 satisfies both `x > 200` and `x < 100`, so nothing is ever checked.
    /// // `black_box` hides the contradiction from the optimizer and the linter.
    /// let hi = core::hint::black_box(100u8);
    /// let v = for_all_where(0u8..=255, |&x| x > 200 && x < hi, |_| false);
    /// assert!(v.is_proven(), "reads as success...");
    /// assert!(v.is_vacuous(), "...but proves nothing -- note the predicate is literally `false`");
    /// assert!(!v.is_proven_nonvacuous());
    /// ```
    pub fn is_vacuous(&self) -> bool {
        matches!(self, Verdict::Proven { cases: 0 })
    }

    /// [`is_proven`](Self::is_proven) with the vacuity hole closed: the predicate held **and** at least
    /// one input actually reached it. This is what a test assertion should use.
    ///
    /// ```
    /// use aion_verify::for_all_in;
    /// let v = for_all_in(0, 100, |x| x <= 100);
    /// assert!(v.is_proven_nonvacuous());
    /// ```
    ///
    /// # What this does not catch
    ///
    /// Vacuity comes in two forms, and only one is detectable from outside the predicate:
    ///
    /// - **Empty domain** — nothing was checked. Decidable; this method catches it.
    /// - **Trivial predicate** — plenty was checked, but the predicate cannot fail. `|x: i8| x <= 127`
    ///   is true by the type's own range, so it proves nothing about the code under test. No amount of
    ///   enumeration distinguishes a trivially-true property from a hard-won one, so this is *not*
    ///   detectable here. Guard against it by writing predicates that compare against an independently
    ///   computed reference value, or by confirming the proof fails when the implementation is mutated.
    pub fn is_proven_nonvacuous(&self) -> bool {
        matches!(self, Verdict::Proven { cases } if *cases > 0)
    }
    /// Inputs examined (all of them on Proven; the ones that passed before the failure on Refuted).
    pub fn cases(&self) -> u64 {
        match self {
            Verdict::Proven { cases } => *cases,
            Verdict::Refuted { checked, .. } => *checked,
        }
    }
    pub fn counterexample(&self) -> Option<&T> {
        match self {
            Verdict::Refuted { counterexample, .. } => Some(counterexample),
            Verdict::Proven { .. } => None,
        }
    }
}

/// Prove `pred` holds for EVERY item produced by `inputs`. Complete coverage of the domain = a proof.
pub fn for_all<I, T, F>(inputs: I, pred: F) -> Verdict<T>
where
    I: IntoIterator<Item = T>,
    F: Fn(&T) -> bool,
{
    let mut n = 0u64;
    for x in inputs {
        if !pred(&x) {
            return Verdict::Refuted {
                counterexample: x,
                checked: n,
            };
        }
        n += 1;
    }
    Verdict::Proven { cases: n }
}

/// Like [`for_all`] but only over inputs satisfying `precond` — the equivalent of a `kani::assume` guard.
/// Proves `pred` on every input where the precondition holds.
///
/// # Vacuity warning
///
/// If `precond` rejects every input, this returns `Proven { cases: 0 }` — a **vacuous** proof that
/// reads as success while having tested nothing. This is the most common way a proof suite silently
/// stops proving anything: a precondition drifts out of sync with the domain, and every test still
/// passes. Assert with [`Verdict::is_proven_nonvacuous`] rather than [`Verdict::is_proven`], or check
/// [`Verdict::cases`] against the count you expect.
pub fn for_all_where<I, T, P, F>(inputs: I, precond: P, pred: F) -> Verdict<T>
where
    I: IntoIterator<Item = T>,
    P: Fn(&T) -> bool,
    F: Fn(&T) -> bool,
{
    let mut n = 0u64;
    for x in inputs {
        if !precond(&x) {
            continue;
        }
        if !pred(&x) {
            return Verdict::Refuted {
                counterexample: x,
                checked: n,
            };
        }
        n += 1;
    }
    Verdict::Proven { cases: n }
}

/// Exhaustive proof over the entire `u8` domain (all 256 values).
pub fn for_all_u8<F: Fn(u8) -> bool>(pred: F) -> Verdict<u8> {
    for_all(0u8..=255, |&x| pred(x))
}

/// Exhaustive proof over the inclusive range `[lo, hi]`.
pub fn for_all_in<F: Fn(u64) -> bool>(lo: u64, hi: u64, pred: F) -> Verdict<u64> {
    for_all(lo..=hi, |&x| pred(x))
}

/// Exhaustive proof over the cartesian product of two finite domains (binary invariants). Returns the
/// `(a, b)` pair that breaks `pred`, if any.
pub fn for_all_pairs<A: Clone, B: Clone, F: Fn(&A, &B) -> bool>(
    a: &[A],
    b: &[B],
    pred: F,
) -> Verdict<(A, B)> {
    let mut n = 0u64;
    for x in a {
        for y in b {
            if !pred(x, y) {
                return Verdict::Refuted {
                    counterexample: (x.clone(), y.clone()),
                    checked: n,
                };
            }
            n += 1;
        }
    }
    Verdict::Proven { cases: n }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn for_all_proves_a_true_predicate_over_the_whole_domain() {
        let v = for_all_u8(|x| (x as u16) + 1 > x as u16);
        assert!(v.is_proven());
        assert_eq!(v.cases(), 256, "every u8 checked — a proof, not a sample");
    }

    #[test]
    fn vacuous_proofs_are_flagged_when_a_precondition_filters_everything_out() {
        // The predicate is `false` -- it could never hold for any input. But the precondition is
        // unsatisfiable, so the predicate is never reached and the verdict reads as Proven.
        // `black_box` keeps the contradiction opaque to the optimizer and to clippy, which would
        // otherwise reject `x > 200 && x < 100` as a comparison that can never be true -- correct in
        // general, and exactly the situation being tested here.
        let hi = core::hint::black_box(100u8);
        let v = for_all_where(0u8..=255, |&x| x > 200 && x < hi, |_| false);

        assert!(v.is_proven(), "the legacy check reports success");
        assert_eq!(v.cases(), 0, "because nothing was ever checked");
        assert!(
            v.is_vacuous(),
            "which is exactly what is_vacuous exists to surface"
        );
        assert!(
            !v.is_proven_nonvacuous(),
            "and the safe assertion refuses it"
        );
    }

    #[test]
    fn an_empty_domain_is_vacuous_too() {
        // Not just preconditions: any empty input iterator yields the same hollow Proven.
        let v: Verdict<u64> = for_all_in(10, 0, |_| false);
        assert!(v.is_vacuous(), "lo > hi means an empty range");
        assert!(!v.is_proven_nonvacuous());
    }

    #[test]
    fn a_real_proof_is_nonvacuous() {
        let v = for_all_u8(|x| (x as u16) + 1 > x as u16);
        assert!(
            v.is_proven_nonvacuous(),
            "256 inputs actually reached the predicate"
        );
        assert!(!v.is_vacuous());

        // A satisfiable precondition still leaves witnesses behind.
        let w = for_all_where(0u8..=255, |&x| x % 2 == 0, |&x| x % 2 == 0);
        assert!(w.is_proven_nonvacuous());
        assert_eq!(w.cases(), 128);
    }

    #[test]
    fn refuted_verdicts_are_never_vacuous() {
        // A counterexample is proof the predicate was reached, so vacuity cannot apply.
        let v = for_all_u8(|x| x < 200);
        assert!(!v.is_vacuous());
        assert!(
            !v.is_proven_nonvacuous(),
            "refuted is not proven, vacuous or otherwise"
        );
    }

    #[test]
    fn for_all_refutes_and_returns_the_counterexample() {
        let v = for_all_u8(|x| x < 200);
        assert!(!v.is_proven());
        assert_eq!(v.counterexample(), Some(&200u8));
        assert_eq!(
            v.cases(),
            200,
            "200 values passed before the counterexample"
        );
    }

    #[test]
    fn for_all_where_applies_a_precondition() {
        let v = for_all_where(0u16..=255, |x| x % 2 == 0, |x| (x * 2) % 2 == 0);
        assert!(v.is_proven());
        assert_eq!(v.cases(), 128, "only the 128 even values were in scope");
    }

    #[test]
    fn for_all_in_covers_a_bounded_range() {
        let v = for_all_in(10, 20, |x| (10..=20).contains(&x));
        assert!(v.is_proven());
        assert_eq!(v.cases(), 11);
    }

    #[test]
    fn for_all_pairs_covers_the_product_and_finds_a_bad_pair() {
        let a = [1u32, 2, 3];
        let b = [10u32, 20];
        let good = for_all_pairs(&a, &b, |&x, &y| x + y == y + x);
        assert!(good.is_proven());
        assert_eq!(good.cases(), 6, "3 x 2 pairs all checked");
        let bad = for_all_pairs(&a, &b, |&x, &y| x + y != 12);
        assert_eq!(
            bad.counterexample(),
            Some(&(2u32, 10u32)),
            "2+10==12 breaks it"
        );
    }
}

// ── TIER 5 — third-party formal confirmation (Kani) ──────────────────────────────────────────────────
#[cfg(kani)]
mod kani_proofs {
    use super::*;

    /// Independent confirmation: for any bound b <= 16, for_all_in(0, b, |x| x <= b) is Proven and checks
    /// exactly b+1 cases. Kani proves it SYMBOLICALLY — every b in 0..=16 over all execution paths at once,
    /// confirming our enumerating engine's own claim about itself. Bounded to 16 (with a matching unwind so
    /// CBMC fully unwinds the enumeration loop and terminates); the tier-4 test already exercises the full
    /// 0..=255 range concretely, so this adds symbolic assurance on top rather than replacing it.
    #[kani::proof]
    #[kani::unwind(18)]
    fn for_all_in_is_sound() {
        let b: u64 = kani::any();
        kani::assume(b <= 16);
        let v = for_all_in(0, b, |x| x <= b);
        assert!(v.is_proven());
        assert!(v.cases() == b + 1);
    }
}
