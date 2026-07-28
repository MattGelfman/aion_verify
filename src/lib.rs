// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! AION OS — first-party proof engine (`aion_verify`).
//!
//! "Our validation and proof functions should do everything Kani does" — for **enumerable and bounded**
//! domains, this delivers exactly that: it checks a predicate against **every** input in the domain and
//! returns a [`Verdict`] of either `Proven { cases }` (complete coverage — a proof) or `Refuted` **with the
//! counterexample** that broke it. That is the same guarantee a bounded model checker gives over a bounded
//! space: not a sample, the whole space.
//!
//! What it does NOT do (and why Kani stays): it brute-force **enumerates**, so it cannot cover astronomically
//! large domains the way Kani's symbolic/SAT reasoning (CBMC) can. So `aion_verify` is the everyday,
//! first-party tier-4 engine for finite/bounded invariants, and **Kani (tier 5) remains the independent,
//! third-party proof** — symbolic coverage of the large cases plus an outside confirmation of ours. Two
//! tiers, two independent methods, per AION's validation doctrine.
//!
//! `no_std`, `#![forbid(unsafe_code)]`.
#![forbid(unsafe_code)]
#![no_std]

extern crate alloc;

/// TIER 5 — symbolic verification over unbounded domains (interval abstract interpretation). Proves
/// properties over *all* of `u64` without enumerating it, entirely in first-party Rust. See [`symbolic`].
pub mod symbolic;

/// The outcome of a proof attempt over a domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict<T> {
    /// The predicate held for every one of `cases` inputs — a proof over the domain.
    Proven { cases: u64 },
    /// The predicate failed; `counterexample` is the input that broke it, after `checked` passing inputs.
    Refuted { counterexample: T, checked: u64 },
}

impl<T> Verdict<T> {
    pub fn is_proven(&self) -> bool {
        matches!(self, Verdict::Proven { .. })
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
