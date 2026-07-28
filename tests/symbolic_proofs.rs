// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! TIER 5 tests — symbolic proofs over the *entire* `u64` domain (2^64 values) with no enumeration,
//! plus concrete-witness refutation and honest `Unknown` where the interval domain is too weak. The
//! last one is the important one: it demonstrates the engine never returns a false Proven/Refuted.

use aion_verify::symbolic::{
    prove_contract, prove_forall, prove_forall_n, prove_forall_refine, Expr, Iv, Prop, SymVerdict,
};

#[test]
fn proves_mask_bound_over_all_of_u64() {
    // ∀ x: (x & 0xFF) <= 255 — proven over all 2^64 values, symbolically.
    let p = Prop::Le(Expr::var().and(0xFF), Expr::c(255));
    assert_eq!(prove_forall(Iv::full(), &p), SymVerdict::Proven);
}

#[test]
fn proves_shift_range_over_all_of_u64() {
    // ∀ x: (x >> 8) < 2^56
    let p = Prop::Lt(Expr::var().shr(8), Expr::c(1 << 56));
    assert_eq!(prove_forall(Iv::full(), &p), SymVerdict::Proven);
}

#[test]
fn proves_modulo_bound_over_all_of_u64() {
    // ∀ x: x % 10 <= 9
    let p = Prop::Le(Expr::var().rem(10), Expr::c(9));
    assert_eq!(prove_forall(Iv::full(), &p), SymVerdict::Proven);
}

#[test]
fn proves_bounded_arithmetic_has_no_overflow() {
    // ∀ x ∈ [0, 1000]: x + 5 <= 1005 (the analysis knows the add can't overflow in range).
    let p = Prop::Le(Expr::var().add(Expr::c(5)), Expr::c(1005));
    assert_eq!(prove_forall(Iv::new(0, 1000), &p), SymVerdict::Proven);
    // ...and x * 2 <= 2000 on the same domain.
    let q = Prop::Le(Expr::var().mul(Expr::c(2)), Expr::c(2000));
    assert_eq!(prove_forall(Iv::new(0, 1000), &q), SymVerdict::Proven);
}

#[test]
fn proves_a_conjunction() {
    // ∀ x: (x & 0xF) <= 15  AND  (x >> 60) <= 15
    let p =
        Prop::Le(Expr::var().and(0xF), Expr::c(15)).and(Prop::Le(Expr::var().shr(60), Expr::c(15)));
    assert_eq!(prove_forall(Iv::full(), &p), SymVerdict::Proven);
}

#[test]
fn refutes_with_a_confirmed_witness() {
    // ∀ x: x <= 100 — false. Must return a concrete value that really violates it.
    let p = Prop::Le(Expr::var(), Expr::c(100));
    match prove_forall(Iv::full(), &p) {
        SymVerdict::Refuted { witness } => {
            assert!(witness[0] > 100, "witness {:?} must break x<=100", witness)
        }
        v => panic!("expected Refuted, got {v:?}"),
    }
}

#[test]
fn refutes_a_too_tight_mask_bound() {
    // ∀ x: (x & 0xFF) <= 100 — false, since low byte can reach 255.
    let p = Prop::Le(Expr::var().and(0xFF), Expr::c(100));
    match prove_forall(Iv::full(), &p) {
        SymVerdict::Refuted { witness } => assert!((witness[0] & 0xFF) > 100),
        v => panic!("expected Refuted, got {v:?}"),
    }
}

// ── Phase B — multiple variables + function contracts ──────────────────────────────────────────────

#[test]
fn proves_a_multi_variable_property() {
    // ∀ x0 ∈ [0,100], x1 ∈ [0,100]: x0 + x1 <= 200 (the add can't overflow in range).
    let sum = Expr::var_at(0).add(Expr::var_at(1));
    let p = Prop::Le(sum, Expr::c(200));
    assert_eq!(
        prove_forall_n(&[Iv::new(0, 100), Iv::new(0, 100)], &p),
        SymVerdict::Proven
    );
}

#[test]
fn refutes_a_multi_variable_property_with_a_full_assignment() {
    // ∀ x0,x1 ∈ [0,100]: x0 + x1 <= 150 — false (100+100=200). Witness names BOTH variables.
    let sum = Expr::var_at(0).add(Expr::var_at(1));
    let p = Prop::Le(sum, Expr::c(150));
    match prove_forall_n(&[Iv::new(0, 100), Iv::new(0, 100)], &p) {
        SymVerdict::Refuted { witness } => {
            assert_eq!(witness.len(), 2, "witness assigns both variables");
            assert!(
                witness[0] + witness[1] > 150,
                "witness {:?} really breaks it",
                witness
            );
        }
        v => panic!("expected Refuted, got {v:?}"),
    }
}

#[test]
fn proves_a_function_contract() {
    // Contract: for x in [0,1000], if x <= 1000 then x + 1 <= 1001. (precond -> postcond)
    let pre = Prop::Le(Expr::var(), Expr::c(1000));
    let post = Prop::Le(Expr::var().add(Expr::c(1)), Expr::c(1001));
    assert_eq!(
        prove_contract(&[Iv::new(0, 1000)], &pre, &post),
        SymVerdict::Proven
    );
}

#[test]
fn refutes_a_false_contract_with_a_witness() {
    // Contract that's FALSE: for x in [0,1000], if x <= 1000 then x <= 999. Broken at x=1000.
    let pre = Prop::Le(Expr::var(), Expr::c(1000));
    let post = Prop::Le(Expr::var(), Expr::c(999));
    match prove_contract(&[Iv::new(0, 1000)], &pre, &post) {
        SymVerdict::Refuted { witness } => assert_eq!(witness, vec![1000]),
        v => panic!("expected Refuted, got {v:?}"),
    }
}

#[test]
fn honest_unknown_never_a_false_result() {
    // (x >> 1) <= x is TRUE for every u64 — but a NON-relational interval domain loses the correlation
    // between `x >> 1` and `x`, and no probed value breaks it. So the engine says Unknown, NOT a false
    // Proven and NOT a false Refuted. Soundness over bravado.
    let p = Prop::Le(Expr::var().shr(1), Expr::var());
    assert_eq!(prove_forall(Iv::full(), &p), SymVerdict::Unknown);
}

// ── Phase C — interval refinement (branch-and-bound) proves correlated properties ──────────────────

#[test]
fn refinement_proves_a_correlated_property() {
    // (x >> 1) <= x is TRUE for all u64 but CORRELATED — prove_forall_n gives Unknown (see the test
    // above). With refinement (bisecting the domain) it becomes a real proof over all 2^64 values.
    let p = Prop::Le(Expr::var().shr(1), Expr::var());
    assert_eq!(prove_forall_n(&[Iv::full()], &p), SymVerdict::Unknown); // plain interval: undecided
    assert_eq!(
        prove_forall_refine(&[Iv::full()], &p, 256),
        SymVerdict::Proven
    ); // refinement: proven
}

#[test]
fn refinement_refutes_a_false_correlation() {
    // (x >> 1) >= x is FALSE (x=1 gives 0 >= 1). Refinement must find a concrete witness.
    let p = Prop::Ge(Expr::var().shr(1), Expr::var());
    match prove_forall_refine(&[Iv::full()], &p, 256) {
        SymVerdict::Refuted { witness } => {
            assert!((witness[0] >> 1) < witness[0], "witness {:?}", witness)
        }
        v => panic!("expected Refuted, got {v:?}"),
    }
}

#[test]
fn refinement_is_honest_when_the_budget_runs_out() {
    // With too small a split budget it cannot finish the proof — and must say Unknown, never a false
    // Proven. Soundness holds regardless of budget.
    let p = Prop::Le(Expr::var().shr(1), Expr::var());
    assert_eq!(
        prove_forall_refine(&[Iv::full()], &p, 2),
        SymVerdict::Unknown
    );
}

// ── Phase D — affine relational reasoning (shared variables, no splitting) ─────────────────────────

#[test]
fn relational_proves_a_shared_variable_fact_without_splitting() {
    // ∀ x0,x1 ∈ [0, 1e9]: x0 <= x0 + x1. The two x0's are the SAME value — the interval domain can't
    // see that, but the affine layer cancels them (x0 - (x0+x1) = -x1 <= 0) and proves it directly.
    let d = &[Iv::new(0, 1_000_000_000), Iv::new(0, 1_000_000_000)];
    let p = Prop::Le(Expr::var_at(0), Expr::var_at(0).add(Expr::var_at(1)));
    assert_eq!(prove_forall_n(d, &p), SymVerdict::Proven);
}

#[test]
fn relational_proves_commutativity() {
    // ∀ x0,x1: x0 + x1 == x1 + x0 (over a non-overflowing domain) — the affine difference is identically 0.
    let d = &[Iv::new(0, 1_000_000), Iv::new(0, 1_000_000)];
    let lhs = Expr::var_at(0).add(Expr::var_at(1));
    let rhs = Expr::var_at(1).add(Expr::var_at(0));
    assert_eq!(prove_forall_n(d, &Prop::Eq(lhs, rhs)), SymVerdict::Proven);
}

#[test]
fn relational_is_sound_under_wrapping() {
    // x0 <= x0 + x1 is NOT true over the FULL u64 domain: when x0 + x1 wraps, the sum is < x0. The
    // affine layer must NOT apply here (overflow), and the engine must not falsely prove it — it finds
    // the wrapping counterexample instead. Soundness over the shortcut.
    let d = &[Iv::full(), Iv::full()];
    let p = Prop::Le(Expr::var_at(0), Expr::var_at(0).add(Expr::var_at(1)));
    assert_ne!(
        prove_forall_n(d, &p),
        SymVerdict::Proven,
        "must never falsely prove a wrapping case"
    );
}

#[test]
fn u64_max_boundary_is_safe() {
    // Reasoning at the very top of the domain must never overflow or panic.
    let p = Prop::Ge(Expr::var(), Expr::c(0)); // trivially true for unsigned
    assert_eq!(prove_forall(Iv::full(), &p), SymVerdict::Proven);
    let q = Prop::Le(Expr::var(), Expr::c(u64::MAX)); // every u64 <= u64::MAX
    assert_eq!(prove_forall(Iv::full(), &q), SymVerdict::Proven);
}
