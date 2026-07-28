// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! SELF-AUDIT — `aion_verify` turned on itself.
//!
//! The strongest possible check of a proof engine is to prove its own invariants *with* it. Every test
//! here uses `aion_verify`'s own combinators to establish, over a complete bounded domain, that the
//! engine behaves exactly as specified — plus a hard scan of the edges where a lesser implementation
//! would panic or miscount (empty domains, the `u64::MAX` boundary, first-counterexample precision).

use aion_verify::{for_all, for_all_in, for_all_pairs, for_all_u8, for_all_where};

#[test]
fn audit_case_count_is_exactly_the_domain_size() {
    // For every (lo, hi) with lo <= hi in [0, 48], for_all_in must report exactly hi-lo+1 cases.
    // Proven with the engine itself over the full product of bounds — a proof about proofs.
    let bounds: Vec<u64> = (0..=48).collect();
    let v = for_all_pairs(&bounds, &bounds, |&lo, &hi| {
        if lo > hi {
            return true; // invalid ordering handled separately below
        }
        for_all_in(lo, hi, |_| true).cases() == hi - lo + 1
    });
    assert!(
        v.is_proven(),
        "case count wrong at {:?}",
        v.counterexample()
    );
}

#[test]
fn audit_reports_the_first_counterexample_with_exact_prior_count() {
    // For EVERY threshold t in 0..=255: proving `x != t` over all u8 must refute at exactly t, having
    // checked exactly t inputs first. Proven exhaustively over all 256 thresholds by the engine itself.
    let v = for_all_u8(|t| {
        let r = for_all_u8(|x| x != t);
        r.counterexample() == Some(&t) && r.cases() == t as u64 && !r.is_proven()
    });
    assert!(
        v.is_proven(),
        "first-counterexample property fails at {:?}",
        v.counterexample()
    );
}

#[test]
fn audit_empty_domain_is_vacuously_proven() {
    // lo > hi is an empty range: vacuously true, zero cases — never a false Refuted.
    let empty = for_all_in(5, 3, |_| false);
    assert!(empty.is_proven());
    assert_eq!(empty.cases(), 0);
    assert_eq!(empty.counterexample(), None);

    let none: [u8; 0] = [];
    assert!(for_all(none, |_| false).is_proven());

    // A precondition satisfied by nothing is likewise vacuous.
    assert!(for_all_where(0u8..=255, |_| false, |_| false).is_proven());
    assert_eq!(for_all_where(0u8..=255, |_| false, |_| false).cases(), 0);
}

#[test]
fn audit_u64_max_boundary_does_not_overflow_or_panic() {
    // The top of the u64 domain is where naive range code overflows. RangeInclusive handles it; confirm.
    assert_eq!(for_all_in(u64::MAX, u64::MAX, |_| true).cases(), 1);
    let near_top = for_all_in(u64::MAX - 3, u64::MAX, |x| x >= u64::MAX - 3);
    assert!(near_top.is_proven());
    assert_eq!(near_top.cases(), 4);
    // And it still refutes correctly at the very top.
    let r = for_all_in(u64::MAX - 3, u64::MAX, |x| x != u64::MAX);
    assert_eq!(r.counterexample(), Some(&u64::MAX));
}

#[test]
fn audit_precondition_counts_only_admitted_inputs() {
    // Exactly the 128 even values of 0..=255 are in scope; the rest are skipped, not failed.
    assert_eq!(
        for_all_where(0u16..=255, |x| x % 2 == 0, |_| true).cases(),
        128
    );
    // A precondition that admits everything degenerates to for_all.
    assert_eq!(for_all_where(0u16..=99, |_| true, |_| true).cases(), 100);
}

#[test]
fn audit_pairs_cover_the_full_cartesian_product() {
    // |a| * |b| pairs, every one checked, in row-major order (so the first bad pair is deterministic).
    let a = [1u32, 2, 3, 4];
    let b = [9u32, 8];
    assert_eq!(for_all_pairs(&a, &b, |_, _| true).cases(), 8);
    // First failure is the earliest in row-major order.
    let bad = for_all_pairs(&a, &b, |&x, &y| !(x == 2 && y == 9));
    assert_eq!(bad.counterexample(), Some(&(2u32, 9u32)));
}

#[test]
fn audit_a_true_property_over_u8_is_a_full_proof() {
    // Sanity anchor: a genuinely-true property covers all 256 values and reports it as a proof.
    let v = for_all_u8(|x| x.wrapping_add(1) != x);
    assert!(v.is_proven());
    assert_eq!(v.cases(), 256);
}
