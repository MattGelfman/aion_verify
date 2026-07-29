// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! TIER 5 — symbolic verification over *unbounded* integer domains, in pure Rust.
//!
//! Tier 4 ([`crate::for_all`]) enumerates: it proves a property by checking every value, so it can only
//! cover finite/bounded domains. Tier 5 proves properties over the **entire** domain — including all
//! 2^64 values of `u64`, over any number of variables — **without enumerating it**, by *interval
//! abstract interpretation*: it computes, for each sub-expression, an interval guaranteed to contain
//! every value that expression can take, then decides the property over those intervals.
//!
//! Because tier 5 must *reason about* an expression rather than merely call it, its predicates are a
//! small first-party [`Expr`]/[`Prop`] DSL (an opaque `Fn` can't be analysed — only executed). Variables
//! are addressed by index ([`Expr::var_at`]); [`Expr::var`] is variable 0.
//!
//! **Function contracts** — the workhorse of component/kernel verification — are [`prove_contract`]:
//! prove that a postcondition holds whenever a precondition does, over the variables' domains.
//!
//! **Soundness is the whole point** — the interval transfer functions always *over-approximate* (the
//! true set of values is a subset of the computed interval), and every uncertain case degrades to
//! [`SymVerdict::Unknown`] rather than guessing:
//!  - [`SymVerdict::Proven`] — the property holds for **every** assignment in the domain (a real proof).
//!  - [`SymVerdict::Refuted`] — carries a **concrete** assignment that falsifies it (confirmed).
//!  - [`SymVerdict::Unknown`] — the interval abstraction wasn't precise enough to decide (e.g. a
//!    relational/correlated property). Never a false Proven or Refuted.
//!
//! This is the role Kani/CBMC plays, done entirely first-party: no C, no external solver, no WSL —
//! `no_std`, only `alloc` for the expression tree and witnesses.

// The DSL's builder methods (add/sub/mul/shl/shr/rem/not) intentionally mirror operator names.
#![allow(clippy::should_implement_trait)]

use alloc::boxed::Box;
use alloc::vec::Vec;

/// An inclusive interval `[lo, hi]` over `u64`. Every operation **over-approximates**: the set of real
/// results is always a subset of the returned interval — which is exactly what makes a proof over the
/// interval sound. When an operation could wrap/overflow into an un-representable set, it widens to
/// [`Iv::full`] (always sound, just less precise).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Iv {
    pub lo: u64,
    pub hi: u64,
}

impl Iv {
    /// The interval containing exactly one value.
    pub const fn point(v: u64) -> Iv {
        Iv { lo: v, hi: v }
    }
    /// The interval `[lo, hi]` (swapped if given out of order).
    pub const fn new(lo: u64, hi: u64) -> Iv {
        if lo <= hi {
            Iv { lo, hi }
        } else {
            Iv { lo: hi, hi: lo }
        }
    }
    /// The whole `u64` domain, `[0, u64::MAX]`.
    pub const fn full() -> Iv {
        Iv {
            lo: 0,
            hi: u64::MAX,
        }
    }
    /// Whether `v` is inside the interval.
    pub const fn contains(&self, v: u64) -> bool {
        self.lo <= v && v <= self.hi
    }

    fn add(self, o: Iv) -> Iv {
        match (self.lo.checked_add(o.lo), self.hi.checked_add(o.hi)) {
            (Some(lo), Some(hi)) => Iv { lo, hi },
            _ => Iv::full(), // a wrap makes the result set non-contiguous -> widen (sound)
        }
    }
    fn sub(self, o: Iv) -> Iv {
        match (self.lo.checked_sub(o.hi), self.hi.checked_sub(o.lo)) {
            (Some(lo), Some(hi)) => Iv { lo, hi },
            _ => Iv::full(),
        }
    }
    fn mul(self, o: Iv) -> Iv {
        match (self.lo.checked_mul(o.lo), self.hi.checked_mul(o.hi)) {
            (Some(lo), Some(hi)) => Iv { lo, hi },
            _ => Iv::full(),
        }
    }
    fn shl(self, k: u32) -> Iv {
        if k >= 64 {
            return if self.lo == 0 && self.hi == 0 {
                Iv::point(0)
            } else {
                Iv::full()
            };
        }
        if self.hi <= (u64::MAX >> k) {
            Iv {
                lo: self.lo << k,
                hi: self.hi << k,
            }
        } else {
            Iv::full()
        }
    }
    fn shr(self, k: u32) -> Iv {
        if k >= 64 {
            return Iv::point(0);
        }
        Iv {
            lo: self.lo >> k,
            hi: self.hi >> k,
        } // monotone, never overflows
    }
    fn bitand(self, mask: u64) -> Iv {
        let hi = if mask < self.hi { mask } else { self.hi };
        Iv { lo: 0, hi }
    }
    fn bitor(self, mask: u64) -> Iv {
        let lo = if mask > self.lo { mask } else { self.lo };
        Iv { lo, hi: u64::MAX }
    }
    fn rem(self, m: u64) -> Iv {
        if m == 0 {
            return Iv::full();
        }
        if self.hi < m {
            self
        } else {
            Iv { lo: 0, hi: m - 1 }
        }
    }
}

/// An integer expression over one or more symbolic variables (addressed by index), evaluated in the
/// `u64` bitvector domain (wrapping arithmetic, like real Rust `u64`).
#[derive(Clone, Debug)]
pub enum Expr {
    /// A symbolic input variable, by index (0, 1, ...).
    Var(u32),
    /// A constant.
    Const(u64),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    /// Left shift by a constant.
    Shl(Box<Expr>, u32),
    /// Right shift by a constant.
    Shr(Box<Expr>, u32),
    /// Bitwise AND with a constant mask.
    And(Box<Expr>, u64),
    /// Bitwise OR with a constant mask.
    Or(Box<Expr>, u64),
    /// Remainder by a constant modulus.
    Rem(Box<Expr>, u64),
}

impl Expr {
    /// Variable 0 (the common single-variable case).
    pub fn var() -> Expr {
        Expr::Var(0)
    }
    /// Variable `i`.
    pub fn var_at(i: u32) -> Expr {
        Expr::Var(i)
    }
    pub fn c(v: u64) -> Expr {
        Expr::Const(v)
    }
    pub fn add(self, o: Expr) -> Expr {
        Expr::Add(Box::new(self), Box::new(o))
    }
    pub fn sub(self, o: Expr) -> Expr {
        Expr::Sub(Box::new(self), Box::new(o))
    }
    pub fn mul(self, o: Expr) -> Expr {
        Expr::Mul(Box::new(self), Box::new(o))
    }
    pub fn shl(self, k: u32) -> Expr {
        Expr::Shl(Box::new(self), k)
    }
    pub fn shr(self, k: u32) -> Expr {
        Expr::Shr(Box::new(self), k)
    }
    pub fn and(self, m: u64) -> Expr {
        Expr::And(Box::new(self), m)
    }
    pub fn or(self, m: u64) -> Expr {
        Expr::Or(Box::new(self), m)
    }
    pub fn rem(self, m: u64) -> Expr {
        Expr::Rem(Box::new(self), m)
    }

    /// Substitute every variable by its next-state expression: `Var(i)` becomes `next[i]`. This is how a
    /// transition system's step is applied to an invariant (turn `inv(state)` into `inv(next_state)`).
    pub fn subst(&self, next: &[Expr]) -> Expr {
        match self {
            Expr::Var(i) => next.get(*i as usize).cloned().unwrap_or(Expr::Var(*i)),
            Expr::Const(v) => Expr::Const(*v),
            Expr::Add(a, b) => Expr::Add(Box::new(a.subst(next)), Box::new(b.subst(next))),
            Expr::Sub(a, b) => Expr::Sub(Box::new(a.subst(next)), Box::new(b.subst(next))),
            Expr::Mul(a, b) => Expr::Mul(Box::new(a.subst(next)), Box::new(b.subst(next))),
            Expr::Shl(a, k) => Expr::Shl(Box::new(a.subst(next)), *k),
            Expr::Shr(a, k) => Expr::Shr(Box::new(a.subst(next)), *k),
            Expr::And(a, m) => Expr::And(Box::new(a.subst(next)), *m),
            Expr::Or(a, m) => Expr::Or(Box::new(a.subst(next)), *m),
            Expr::Rem(a, m) => Expr::Rem(Box::new(a.subst(next)), *m),
        }
    }

    /// Abstract evaluation: the interval of every value this expression can take when each variable `i`
    /// ranges over `doms[i]`. Guaranteed to be a superset of the true value set (soundness). An
    /// out-of-range variable index defaults to the full domain (still sound).
    fn eval_iv(&self, doms: &[Iv]) -> Iv {
        match self {
            Expr::Var(i) => doms.get(*i as usize).copied().unwrap_or_else(Iv::full),
            Expr::Const(v) => Iv::point(*v),
            Expr::Add(a, b) => a.eval_iv(doms).add(b.eval_iv(doms)),
            Expr::Sub(a, b) => a.eval_iv(doms).sub(b.eval_iv(doms)),
            Expr::Mul(a, b) => a.eval_iv(doms).mul(b.eval_iv(doms)),
            Expr::Shl(a, k) => a.eval_iv(doms).shl(*k),
            Expr::Shr(a, k) => a.eval_iv(doms).shr(*k),
            Expr::And(a, m) => a.eval_iv(doms).bitand(*m),
            Expr::Or(a, m) => a.eval_iv(doms).bitor(*m),
            Expr::Rem(a, m) => a.eval_iv(doms).rem(*m),
        }
    }

    /// Concrete evaluation at an assignment `xs` (wrapping `u64` arithmetic) — used to confirm witnesses.
    fn eval_at(&self, xs: &[u64]) -> u64 {
        match self {
            Expr::Var(i) => xs.get(*i as usize).copied().unwrap_or(0),
            Expr::Const(v) => *v,
            Expr::Add(a, b) => a.eval_at(xs).wrapping_add(b.eval_at(xs)),
            Expr::Sub(a, b) => a.eval_at(xs).wrapping_sub(b.eval_at(xs)),
            Expr::Mul(a, b) => a.eval_at(xs).wrapping_mul(b.eval_at(xs)),
            Expr::Shl(a, k) => a.eval_at(xs).wrapping_shl(*k),
            Expr::Shr(a, k) => a.eval_at(xs).wrapping_shr(*k),
            Expr::And(a, m) => a.eval_at(xs) & *m,
            Expr::Or(a, m) => a.eval_at(xs) | *m,
            Expr::Rem(a, m) => {
                if *m == 0 {
                    0
                } else {
                    a.eval_at(xs) % *m
                }
            }
        }
    }
}

/// Three-valued logic: the outcome of deciding a proposition over an *interval* abstraction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tri {
    True,
    False,
    Unknown,
}

impl Tri {
    fn negate(self) -> Tri {
        match self {
            Tri::True => Tri::False,
            Tri::False => Tri::True,
            Tri::Unknown => Tri::Unknown,
        }
    }
    fn and(self, o: Tri) -> Tri {
        match (self, o) {
            (Tri::False, _) | (_, Tri::False) => Tri::False,
            (Tri::True, Tri::True) => Tri::True,
            _ => Tri::Unknown,
        }
    }
    fn or(self, o: Tri) -> Tri {
        match (self, o) {
            (Tri::True, _) | (_, Tri::True) => Tri::True,
            (Tri::False, Tri::False) => Tri::False,
            _ => Tri::Unknown,
        }
    }
}

/// A boolean property of the symbolic variables, built from comparisons of [`Expr`]s and connectives.
#[derive(Clone, Debug)]
pub enum Prop {
    Le(Expr, Expr),
    Lt(Expr, Expr),
    Ge(Expr, Expr),
    Gt(Expr, Expr),
    Eq(Expr, Expr),
    Ne(Expr, Expr),
    And(Box<Prop>, Box<Prop>),
    Or(Box<Prop>, Box<Prop>),
    Not(Box<Prop>),
    /// `a -> b`, i.e. `!a || b`.
    Implies(Box<Prop>, Box<Prop>),
}

impl Prop {
    pub fn and(self, o: Prop) -> Prop {
        Prop::And(Box::new(self), Box::new(o))
    }
    pub fn or(self, o: Prop) -> Prop {
        Prop::Or(Box::new(self), Box::new(o))
    }
    pub fn not(self) -> Prop {
        Prop::Not(Box::new(self))
    }
    pub fn implies(self, o: Prop) -> Prop {
        Prop::Implies(Box::new(self), Box::new(o))
    }

    /// Substitute every variable in this proposition by its next-state expression (`Var(i)` -> `next[i]`).
    /// Turns `inv(state)` into `inv(next_state)` — the heart of an inductive consecution check.
    pub fn subst(&self, next: &[Expr]) -> Prop {
        match self {
            Prop::Le(a, b) => Prop::Le(a.subst(next), b.subst(next)),
            Prop::Lt(a, b) => Prop::Lt(a.subst(next), b.subst(next)),
            Prop::Ge(a, b) => Prop::Ge(a.subst(next), b.subst(next)),
            Prop::Gt(a, b) => Prop::Gt(a.subst(next), b.subst(next)),
            Prop::Eq(a, b) => Prop::Eq(a.subst(next), b.subst(next)),
            Prop::Ne(a, b) => Prop::Ne(a.subst(next), b.subst(next)),
            Prop::And(p, q) => Prop::And(Box::new(p.subst(next)), Box::new(q.subst(next))),
            Prop::Or(p, q) => Prop::Or(Box::new(p.subst(next)), Box::new(q.subst(next))),
            Prop::Not(p) => Prop::Not(Box::new(p.subst(next))),
            Prop::Implies(p, q) => Prop::Implies(Box::new(p.subst(next)), Box::new(q.subst(next))),
        }
    }

    fn eval_iv(&self, doms: &[Iv]) -> Tri {
        match self {
            Prop::Le(a, b) => cmp_le_full(a, b, doms),
            Prop::Lt(a, b) => cmp_lt_full(a, b, doms),
            Prop::Ge(a, b) => cmp_le_full(b, a, doms),
            Prop::Gt(a, b) => cmp_lt_full(b, a, doms),
            Prop::Eq(a, b) => cmp_eq_full(a, b, doms),
            Prop::Ne(a, b) => cmp_eq_full(a, b, doms).negate(),
            Prop::And(p, q) => p.eval_iv(doms).and(q.eval_iv(doms)),
            Prop::Or(p, q) => p.eval_iv(doms).or(q.eval_iv(doms)),
            Prop::Not(p) => p.eval_iv(doms).negate(),
            Prop::Implies(p, q) => p.eval_iv(doms).negate().or(q.eval_iv(doms)),
        }
    }

    fn eval_at(&self, xs: &[u64]) -> bool {
        match self {
            Prop::Le(a, b) => a.eval_at(xs) <= b.eval_at(xs),
            Prop::Lt(a, b) => a.eval_at(xs) < b.eval_at(xs),
            Prop::Ge(a, b) => a.eval_at(xs) >= b.eval_at(xs),
            Prop::Gt(a, b) => a.eval_at(xs) > b.eval_at(xs),
            Prop::Eq(a, b) => a.eval_at(xs) == b.eval_at(xs),
            Prop::Ne(a, b) => a.eval_at(xs) != b.eval_at(xs),
            Prop::And(p, q) => p.eval_at(xs) && q.eval_at(xs),
            Prop::Or(p, q) => p.eval_at(xs) || q.eval_at(xs),
            Prop::Not(p) => !p.eval_at(xs),
            Prop::Implies(p, q) => !p.eval_at(xs) || q.eval_at(xs),
        }
    }
}

// ── Phase D: affine (linear) relational reasoning ─────────────────────────────────────────────────
//
// A plain interval domain evaluates each occurrence of a variable independently, so it can't see that
// the two `x`s in `x <= x + y` are the *same* value. Representing the LINEAR fragment as an affine form
// `c + Σ cᵢ·vᵢ` lets a comparison `a ≤ b` be decided from the bounds of `a − b`, where shared terms
// cancel (`x − (x + y) = −y`) — proving relational facts with no splitting.
//
// SOUNDNESS vs u64 wrapping: the affine form is exact integer math, but the engine's semantics are
// *wrapping* u64. We only use affine reasoning when it provably matches: the fragment is built solely
// from non-negative, non-decreasing ops (Var / Const / Add / Mul-by-const / Shl), so every value is
// ≥ 0, and we require each operand's maximum over the domain to be ≤ u64::MAX (no overflow). Under
// those two conditions the u64 value equals the integer value, so the u64 comparison equals the
// integer one. Anything else (Sub, Shr, And, Or, Rem, var·var) is not affine here and falls back to
// the interval comparison — never an unsound shortcut.

/// A linear form `c + Σ coeffs[(var, coeff)]` over `i128` (wide enough that sums/differences of u64
/// magnitudes never overflow).
struct Affine {
    c: i128,
    coeffs: Vec<(u32, i128)>,
}

impl Affine {
    fn add(mut self, o: Affine) -> Affine {
        self.c += o.c;
        for (v, k) in o.coeffs {
            match self.coeffs.iter_mut().find(|(vv, _)| *vv == v) {
                Some(e) => e.1 += k,
                None => self.coeffs.push((v, k)),
            }
        }
        self
    }
    fn scale(mut self, s: i128) -> Affine {
        self.c *= s;
        for e in self.coeffs.iter_mut() {
            e.1 *= s;
        }
        self
    }
    fn neg(self) -> Affine {
        self.scale(-1)
    }
    /// The (min, max) of this form over the variable domains, exact in `i128`.
    fn bounds(&self, doms: &[Iv]) -> (i128, i128) {
        let mut lo = self.c;
        let mut hi = self.c;
        for &(v, k) in &self.coeffs {
            let d = doms.get(v as usize).copied().unwrap_or_else(Iv::full);
            let (dl, dh) = (d.lo as i128, d.hi as i128);
            if k >= 0 {
                lo += k * dl;
                hi += k * dh;
            } else {
                lo += k * dh;
                hi += k * dl;
            }
        }
        (lo, hi)
    }
}

/// The affine form of the linear fragment (`None` for anything non-linear or possibly-negative).
fn to_affine(e: &Expr) -> Option<Affine> {
    match e {
        Expr::Var(i) => Some(Affine {
            c: 0,
            coeffs: alloc::vec![(*i, 1)],
        }),
        Expr::Const(v) => Some(Affine {
            c: *v as i128,
            coeffs: Vec::new(),
        }),
        Expr::Add(a, b) => Some(to_affine(a)?.add(to_affine(b)?)),
        Expr::Mul(a, b) => {
            let (af, bf) = (to_affine(a)?, to_affine(b)?);
            if af.coeffs.is_empty() {
                Some(bf.scale(af.c))
            } else if bf.coeffs.is_empty() {
                Some(af.scale(bf.c))
            } else {
                None // var·var is non-linear
            }
        }
        Expr::Shl(a, k) if *k < 63 => Some(to_affine(a)?.scale(1i128 << k)),
        // Sub can go negative (u64 wrap); Shr/And/Or/Rem are non-linear — fall back to intervals.
        _ => None,
    }
}

/// If both sides are affine and provably non-wrapping over the domain, decide `a - b` vs 0 relationally.
/// Returns `None` when affine reasoning doesn't apply (caller falls back to the interval comparison).
fn affine_diff(a: &Expr, b: &Expr, doms: &[Iv]) -> Option<(i128, i128)> {
    let (af, bf) = (to_affine(a)?, to_affine(b)?);
    const MAX: i128 = u64::MAX as i128;
    // No overflow in computing either operand (both are ≥ 0 by construction of the fragment).
    if af.bounds(doms).1 > MAX || bf.bounds(doms).1 > MAX {
        return None;
    }
    Some(af.add(bf.neg()).bounds(doms)) // bounds of (a - b)
}

fn cmp_le_full(a: &Expr, b: &Expr, doms: &[Iv]) -> Tri {
    if let Some((dlo, dhi)) = affine_diff(a, b, doms) {
        if dhi <= 0 {
            return Tri::True; // a - b <= 0 everywhere
        }
        if dlo > 0 {
            return Tri::False;
        }
    }
    cmp_le(a.eval_iv(doms), b.eval_iv(doms))
}

fn cmp_lt_full(a: &Expr, b: &Expr, doms: &[Iv]) -> Tri {
    if let Some((dlo, dhi)) = affine_diff(a, b, doms) {
        if dhi < 0 {
            return Tri::True;
        }
        if dlo >= 0 {
            return Tri::False;
        }
    }
    cmp_lt(a.eval_iv(doms), b.eval_iv(doms))
}

fn cmp_eq_full(a: &Expr, b: &Expr, doms: &[Iv]) -> Tri {
    if let Some((dlo, dhi)) = affine_diff(a, b, doms) {
        if dlo == 0 && dhi == 0 {
            return Tri::True; // a - b is identically 0
        }
        if dlo > 0 || dhi < 0 {
            return Tri::False; // 0 not attainable
        }
    }
    cmp_eq(a.eval_iv(doms), b.eval_iv(doms))
}

fn cmp_le(a: Iv, b: Iv) -> Tri {
    if a.hi <= b.lo {
        Tri::True
    } else if a.lo > b.hi {
        Tri::False
    } else {
        Tri::Unknown
    }
}
fn cmp_lt(a: Iv, b: Iv) -> Tri {
    if a.hi < b.lo {
        Tri::True
    } else if a.lo >= b.hi {
        Tri::False
    } else {
        Tri::Unknown
    }
}
fn cmp_eq(a: Iv, b: Iv) -> Tri {
    if a.lo == a.hi && b.lo == b.hi && a.lo == b.lo {
        Tri::True
    } else if a.hi < b.lo || b.hi < a.lo {
        Tri::False
    } else {
        Tri::Unknown
    }
}

/// The outcome of a tier-5 symbolic proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SymVerdict {
    /// The property holds for every assignment in the domain — a proof, no enumeration.
    Proven,
    /// The property fails; `witness[i]` is a concrete value for variable `i` that falsifies it
    /// (confirmed by concrete evaluation).
    Refuted { witness: Vec<u64> },
    /// The interval abstraction was too imprecise to decide. Never a false Proven/Refuted.
    Unknown,
}

/// Prove `prop` holds for every value of a **single** variable `x` in `domain` (convenience for the
/// common one-variable case). See [`prove_forall_n`] for multiple variables.
pub fn prove_forall(domain: Iv, prop: &Prop) -> SymVerdict {
    prove_forall_n(&[domain], prop)
}

/// Prove `prop` holds for **every** assignment where variable `i` ranges over `doms[i]` — symbolically,
/// without enumerating the domain.
///
/// Sound: a `Proven` result means the interval analysis established the property over a *superset* of
/// the domain, so it holds for the domain itself. A `Refuted` result is always backed by a concrete
/// assignment confirmed with wrapping arithmetic. Otherwise `Unknown`.
pub fn prove_forall_n(doms: &[Iv], prop: &Prop) -> SymVerdict {
    match prop.eval_iv(doms) {
        Tri::True => SymVerdict::Proven,
        Tri::False => {
            // False across the whole (over-approximated) domain; the all-low corner is a real assignment
            // — confirm it concretely so the witness is never spurious.
            let xs: Vec<u64> = doms.iter().map(|d| d.lo).collect();
            if !prop.eval_at(&xs) {
                SymVerdict::Refuted { witness: xs }
            } else {
                probe(doms, prop)
            }
        }
        Tri::Unknown => probe(doms, prop),
    }
}

/// Prove a **function contract**: that `postcond` holds for every assignment in `doms` for which
/// `precond` holds. This is `forall x. precond(x) -> postcond(x)` — the core of verifying a function or
/// component's behaviour (validate inputs in the precondition, guarantee the postcondition).
pub fn prove_contract(doms: &[Iv], precond: &Prop, postcond: &Prop) -> SymVerdict {
    let implication = precond.clone().implies(postcond.clone());
    prove_forall_n(doms, &implication)
}

/// Prove an **inductive invariant** of a transition system — the first-party way to reason about a
/// *loop or state machine* without unrolling it. Given:
///  - `init_doms`: the set of initial states,
///  - `guard`: the condition under which a step is taken (the loop condition),
///  - `transition[i]`: the next value of variable `i` after one step,
///  - `invariant`: the property to establish for **every reachable state**,
///  - `state_doms`: a domain covering the reachable states (over which preservation is checked),
///
/// it checks the two classic conditions and, if both hold, the invariant holds for *all* iterations:
///  1. **Initiation** — the invariant holds in every initial state.
///  2. **Consecution** — if the invariant and the guard hold, they still hold after one step
///     (`(invariant ∧ guard) → invariant[next]`).
///
/// Returns [`SymVerdict::Proven`] only when both hold; otherwise the failing check's verdict (a
/// `Refuted` names a concrete state that breaks it). `max_splits` bounds the refinement used on each
/// verification condition. This handles **state**, which the value-only tiers do not.
const fn as_var(e: &Expr) -> Option<u32> {
    if let Expr::Var(i) = e {
        Some(*i)
    } else {
        None
    }
}
const fn as_const(e: &Expr) -> Option<u64> {
    if let Expr::Const(v) = e {
        Some(*v)
    } else {
        None
    }
}

/// Narrow a domain box by the box-expressible constraints in `p` (conjunctions of `variable vs constant`
/// comparisons) — "assume `p` holds". Returns `None` if the constraints make the box empty (so `p` is
/// unsatisfiable on it). Relational/disjunctive parts are ignored (a sound over-approximation: we assume
/// *less*, so a proof over the wider box still holds). This is Phase G's key move: assume the invariant
/// and guard, then prove preservation on the *narrowed* region — which works over UNBOUNDED state.
fn assume_narrow(p: &Prop, doms: &[Iv]) -> Option<Vec<Iv>> {
    let mut d = doms.to_vec();
    fn le(a: &Expr, b: &Expr, d: &mut [Iv]) -> Option<()> {
        if let (Some(vi), Some(c)) = (as_var(a), as_const(b)) {
            let iv = d.get_mut(vi as usize)?;
            iv.hi = iv.hi.min(c);
            if iv.lo > iv.hi {
                return None;
            }
        } else if let (Some(c), Some(vi)) = (as_const(a), as_var(b)) {
            let iv = d.get_mut(vi as usize)?;
            iv.lo = iv.lo.max(c);
            if iv.lo > iv.hi {
                return None;
            }
        }
        Some(())
    }
    fn lt(a: &Expr, b: &Expr, d: &mut [Iv]) -> Option<()> {
        if let (Some(vi), Some(c)) = (as_var(a), as_const(b)) {
            if c == 0 {
                return None; // var < 0 is impossible for unsigned
            }
            let iv = d.get_mut(vi as usize)?;
            iv.hi = iv.hi.min(c - 1);
            if iv.lo > iv.hi {
                return None;
            }
        } else if let (Some(c), Some(vi)) = (as_const(a), as_var(b)) {
            let iv = d.get_mut(vi as usize)?;
            iv.lo = iv.lo.max(c.saturating_add(1));
            if iv.lo > iv.hi {
                return None;
            }
        }
        Some(())
    }
    fn go(p: &Prop, d: &mut [Iv]) -> Option<()> {
        match p {
            Prop::And(a, b) => {
                go(a, d)?;
                go(b, d)
            }
            Prop::Le(a, b) => le(a, b, d),
            Prop::Lt(a, b) => lt(a, b, d),
            Prop::Ge(a, b) => le(b, a, d),
            Prop::Gt(a, b) => lt(b, a, d),
            Prop::Eq(a, b) => {
                le(a, b, d)?;
                le(b, a, d)
            }
            _ => Some(()), // Or / Not / Ne / relational: no box narrowing (assume less — sound)
        }
    }
    go(p, &mut d)?;
    Some(d)
}

pub fn prove_inductive(
    init_doms: &[Iv],
    guard: &Prop,
    transition: &[Expr],
    invariant: &Prop,
    state_doms: &[Iv],
    max_splits: u32,
) -> SymVerdict {
    // 1. Initiation: the invariant holds in every initial state.
    let initiation = prove_forall_refine(init_doms, invariant, max_splits);
    if initiation != SymVerdict::Proven {
        return initiation;
    }
    // 2. Consecution: (invariant ∧ guard) ⇒ invariant after one step.
    let inv_next = invariant.subst(transition);
    let assumption = invariant.clone().and(guard.clone());
    // Phase G: assume the invariant+guard by narrowing the state box, then prove preservation there.
    // This discharges the common (box-expressible) case over UNBOUNDED state with no refinement.
    match assume_narrow(&assumption, state_doms) {
        None => SymVerdict::Proven, // no state satisfies (invariant ∧ guard) here — vacuously preserved
        Some(narrowed) => {
            if prove_forall_refine(&narrowed, &inv_next, max_splits) == SymVerdict::Proven {
                return SymVerdict::Proven;
            }
            // Narrowing dropped a relational part (or it genuinely fails) — fall back to the full,
            // always-sound verification condition over the whole state domain.
            let vc = assumption.implies(inv_next);
            prove_forall_refine(state_doms, &vc, max_splits)
        }
    }
}

/// When the abstraction can't decide, try the assignments most likely to break a property — the corners
/// of the domain box and per-variable special values — concretely. A hit is a genuine counterexample.
fn probe(doms: &[Iv], prop: &Prop) -> SymVerdict {
    let n = doms.len();
    // Corners of the domain box: each variable at its lo or hi. Bounded to 2^12 to stay fast.
    if n <= 12 {
        for mask in 0u32..(1u32 << n) {
            let xs: Vec<u64> = (0..n)
                .map(|i| {
                    if mask & (1 << i) != 0 {
                        doms[i].hi
                    } else {
                        doms[i].lo
                    }
                })
                .collect();
            if !prop.eval_at(&xs) {
                return SymVerdict::Refuted { witness: xs };
            }
        }
    }
    // Per-variable special values (the rest held at their low bound) — catches interior breakers.
    for i in 0..n {
        let d = doms[i];
        let mid = d.lo.wrapping_add(d.hi.wrapping_sub(d.lo) / 2);
        for &sv in &[d.lo, d.hi, mid, 0, u64::MAX, 1u64 << 63, 1] {
            if !d.contains(sv) {
                continue;
            }
            let mut xs: Vec<u64> = doms.iter().map(|dd| dd.lo).collect();
            xs[i] = sv;
            if !prop.eval_at(&xs) {
                return SymVerdict::Refuted { witness: xs };
            }
        }
    }
    SymVerdict::Unknown
}

/// Prove `prop` over `doms` with **interval refinement** (branch-and-bound). When the plain interval
/// analysis can't decide a domain, this bisects the widest variable and proves each half — the property
/// holds on the whole box iff it holds on both halves, so splitting is sound and recovers the
/// correlation a non-relational interval domain loses. This proves many properties [`prove_forall_n`]
/// returns `Unknown` for (e.g. `(x >> 1) <= x`).
///
/// `max_splits` bounds the total number of bisections (protecting against blow-up); on exhaustion the
/// undecided part is reported honestly as `Unknown`. A `Refuted` anywhere is a real counterexample for
/// the whole domain; `Proven` requires every sub-box to be proven.
pub fn prove_forall_refine(doms: &[Iv], prop: &Prop, max_splits: u32) -> SymVerdict {
    let mut budget = max_splits;
    refine(doms, prop, &mut budget)
}

fn refine(doms: &[Iv], prop: &Prop, budget: &mut u32) -> SymVerdict {
    match prop.eval_iv(doms) {
        Tri::True => SymVerdict::Proven,
        Tri::False => {
            let xs: Vec<u64> = doms.iter().map(|d| d.lo).collect();
            if !prop.eval_at(&xs) {
                SymVerdict::Refuted { witness: xs }
            } else {
                probe(doms, prop)
            }
        }
        Tri::Unknown => {
            // Pick the widest splittable variable; if none (all points) the intervals are exact and
            // eval_iv would not have returned Unknown, so fall back to a probe.
            let mut wi: Option<usize> = None;
            let mut wwidth = 0u64;
            for (i, d) in doms.iter().enumerate() {
                let w = d.hi - d.lo;
                if w > 0 && w >= wwidth {
                    wwidth = w;
                    wi = Some(i);
                }
            }
            let i = match wi {
                Some(i) => i,
                None => return probe(doms, prop),
            };
            if *budget == 0 {
                return probe(doms, prop); // out of budget: try to refute, else honest Unknown
            }
            *budget -= 1;
            let d = doms[i];
            let mid = d.lo + (d.hi - d.lo) / 2;
            let mut left = doms.to_vec();
            left[i] = Iv::new(d.lo, mid);
            let mut right = doms.to_vec();
            right[i] = Iv::new(mid + 1, d.hi);
            match refine(&left, prop, budget) {
                SymVerdict::Refuted { witness } => SymVerdict::Refuted { witness },
                SymVerdict::Unknown => match refine(&right, prop, budget) {
                    // left undecided: a refutation on the right is still real; otherwise Unknown.
                    SymVerdict::Refuted { witness } => SymVerdict::Refuted { witness },
                    _ => SymVerdict::Unknown,
                },
                SymVerdict::Proven => refine(&right, prop, budget), // whole = left ∧ right
            }
        }
    }
}

// ── Automatic arithmetic-safety properties ────────────────────────────────────────────────────────
// Kani checks overflow, underflow, and division by zero without being asked, because they follow from
// the language semantics rather than from a property the author stated. `safety::verify_no_panic`
// reaches the same result by execution, but only over a bounded domain and only when the build profile
// has `debug-assertions` on (release builds wrap silently). The functions below answer the same
// question symbolically: over UNBOUNDED domains, and independent of the build profile.

/// An arithmetic fault an expression can exhibit at run time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    /// `a + b` exceeded `u64::MAX`.
    AddOverflow,
    /// `a - b` went below zero.
    SubUnderflow,
    /// `a * b` exceeded `u64::MAX`.
    MulOverflow,
    /// `a << k` shifted bits out, or `k >= 64`.
    ShlOverflow,
    /// `a % 0`.
    DivByZero,
}

impl Expr {
    /// Concrete evaluation with **checked** arithmetic: returns the first fault instead of wrapping.
    ///
    /// [`Expr::eval_at`] deliberately wraps, modelling release-mode Rust. This is its counterpart,
    /// modelling debug-mode Rust, and is what confirms a witness is genuine rather than an artefact of
    /// interval imprecision.
    fn eval_checked(&self, xs: &[u64]) -> Result<u64, Fault> {
        match self {
            Expr::Var(i) => Ok(xs.get(*i as usize).copied().unwrap_or(0)),
            Expr::Const(v) => Ok(*v),
            Expr::Add(a, b) => a
                .eval_checked(xs)?
                .checked_add(b.eval_checked(xs)?)
                .ok_or(Fault::AddOverflow),
            Expr::Sub(a, b) => a
                .eval_checked(xs)?
                .checked_sub(b.eval_checked(xs)?)
                .ok_or(Fault::SubUnderflow),
            Expr::Mul(a, b) => a
                .eval_checked(xs)?
                .checked_mul(b.eval_checked(xs)?)
                .ok_or(Fault::MulOverflow),
            Expr::Shl(a, k) => {
                let v = a.eval_checked(xs)?;
                if *k >= 64 || v > (u64::MAX >> *k) {
                    Err(Fault::ShlOverflow)
                } else {
                    Ok(v << *k)
                }
            }
            Expr::Shr(a, k) => Ok(if *k >= 64 {
                0
            } else {
                a.eval_checked(xs)? >> *k
            }),
            Expr::And(a, m) => Ok(a.eval_checked(xs)? & *m),
            Expr::Or(a, m) => Ok(a.eval_checked(xs)? | *m),
            Expr::Rem(a, m) => {
                let v = a.eval_checked(xs)?;
                if *m == 0 {
                    Err(Fault::DivByZero)
                } else {
                    Ok(v % *m)
                }
            }
        }
    }

    /// True when interval reasoning establishes that NO node in this expression can fault over `doms`.
    ///
    /// Sound in the direction that matters: `true` means fault-free for certain (every reachable value
    /// lies within the interval, and the interval endpoints are safe). `false` means "cannot rule it
    /// out", not "faults" — interval analysis loses correlation between variables, so `x - x` is
    /// reported as possibly-underflowing even though it never is.
    fn cannot_fault(&self, doms: &[Iv]) -> bool {
        match self {
            Expr::Var(_) | Expr::Const(_) => true,
            Expr::Add(a, b) => {
                a.cannot_fault(doms)
                    && b.cannot_fault(doms)
                    && a.eval_iv(doms).hi.checked_add(b.eval_iv(doms).hi).is_some()
            }
            Expr::Sub(a, b) => {
                a.cannot_fault(doms)
                    && b.cannot_fault(doms)
                    && a.eval_iv(doms).lo >= b.eval_iv(doms).hi
            }
            Expr::Mul(a, b) => {
                a.cannot_fault(doms)
                    && b.cannot_fault(doms)
                    && a.eval_iv(doms).hi.checked_mul(b.eval_iv(doms).hi).is_some()
            }
            Expr::Shl(a, k) => {
                a.cannot_fault(doms) && *k < 64 && a.eval_iv(doms).hi <= (u64::MAX >> *k)
            }
            Expr::Shr(a, _) | Expr::And(a, _) | Expr::Or(a, _) => a.cannot_fault(doms),
            Expr::Rem(a, m) => a.cannot_fault(doms) && *m != 0,
        }
    }
}

/// Corner assignments of `doms`: each variable at its low or high endpoint.
///
/// Extremes are where arithmetic faults live, so corners are where a witness is most likely to be
/// found. Capped at `MAX_CORNER_VARS` variables to keep this from becoming exponential; beyond that
/// only the all-low and all-high corners are tried, which can turn a `Refuted` into an honest
/// `Unknown` but never produces a wrong answer.
fn corner_assignments(doms: &[Iv]) -> Vec<Vec<u64>> {
    const MAX_CORNER_VARS: usize = 10;
    let n = doms.len();
    if n == 0 {
        return alloc::vec![Vec::new()];
    }
    if n > MAX_CORNER_VARS {
        return alloc::vec![
            doms.iter().map(|d| d.lo).collect(),
            doms.iter().map(|d| d.hi).collect(),
        ];
    }
    let mut out = Vec::with_capacity(1usize << n);
    for mask in 0u32..(1u32 << n) {
        out.push(
            doms.iter()
                .enumerate()
                .map(|(i, d)| if mask >> i & 1 == 1 { d.hi } else { d.lo })
                .collect(),
        );
    }
    out
}

/// Prove that evaluating `e` **cannot overflow, underflow, or divide by zero** for any assignment in
/// `doms` — symbolically, over unbounded domains, without enumeration.
///
/// This is an automatic property in the model-checking sense: you state no invariant, and the faults
/// come from the arithmetic itself. It is the profile-independent counterpart to
/// [`safety::verify_no_panic`](crate::safety::verify_no_panic), which finds the same faults by
/// execution but only over a bounded domain and only under `debug-assertions`.
///
/// - `Proven` — no assignment in the domain can fault. Sound: established over a superset of the domain.
/// - `Refuted { witness }` — a concrete assignment that genuinely faults, confirmed with checked
///   arithmetic. Never spurious.
/// - `Unknown` — interval reasoning could not rule a fault out and no corner assignment exhibited one.
///   Interval analysis discards correlation between variables, so `x - x` lands here.
///
/// ```
/// use aion_verify::symbolic::{prove_no_overflow, Expr, Iv, SymVerdict};
///
/// // x + 1 over the full u64 domain overflows at x = u64::MAX.
/// let e = Expr::var().add(Expr::c(1));
/// assert!(matches!(prove_no_overflow(&[Iv::full()], &e), SymVerdict::Refuted { .. }));
///
/// // Constrain the domain and the same expression is provably safe.
/// assert_eq!(prove_no_overflow(&[Iv::new(0, 1000)], &e), SymVerdict::Proven);
/// ```
pub fn prove_no_overflow(doms: &[Iv], e: &Expr) -> SymVerdict {
    if e.cannot_fault(doms) {
        return SymVerdict::Proven;
    }
    // A fault could not be ruled out. Look for a genuine witness at the domain corners before
    // reporting anything -- an unconfirmed "may fault" must never be presented as a refutation.
    for xs in corner_assignments(doms) {
        if e.eval_checked(&xs).is_err() {
            return SymVerdict::Refuted { witness: xs };
        }
    }
    SymVerdict::Unknown
}

/// The specific [`Fault`] an assignment triggers, or `None` if it evaluates cleanly.
///
/// Useful for reporting *why* a [`prove_no_overflow`] witness fails.
pub fn fault_at(e: &Expr, xs: &[u64]) -> Option<Fault> {
    e.eval_checked(xs).err()
}

#[cfg(test)]
mod overflow_tests {
    use super::*;

    #[test]
    fn unbounded_increment_is_refuted_with_a_real_witness() {
        let e = Expr::var().add(Expr::c(1));
        match prove_no_overflow(&[Iv::full()], &e) {
            SymVerdict::Refuted { witness } => {
                assert_eq!(witness, alloc::vec![u64::MAX]);
                assert_eq!(fault_at(&e, &witness), Some(Fault::AddOverflow));
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    #[test]
    fn a_constrained_domain_makes_the_same_expression_provably_safe() {
        let e = Expr::var().add(Expr::c(1));
        assert_eq!(
            prove_no_overflow(&[Iv::new(0, 1000)], &e),
            SymVerdict::Proven
        );
        // Right at the boundary it is still safe: u64::MAX - 1 plus 1 fits exactly.
        assert_eq!(
            prove_no_overflow(&[Iv::new(0, u64::MAX - 1)], &e),
            SymVerdict::Proven
        );
    }

    #[test]
    fn subtraction_underflow_is_found() {
        // x - 5 underflows whenever x < 5.
        let e = Expr::var().sub(Expr::c(5));
        match prove_no_overflow(&[Iv::new(0, 100)], &e) {
            SymVerdict::Refuted { witness } => {
                assert_eq!(fault_at(&e, &witness), Some(Fault::SubUnderflow));
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
        // Constrain x >= 5 and it is safe.
        assert_eq!(
            prove_no_overflow(&[Iv::new(5, 100)], &e),
            SymVerdict::Proven
        );
    }

    #[test]
    fn multiplication_overflow_is_found() {
        let e = Expr::var().mul(Expr::var_at(1));
        let doms = [Iv::new(0, u64::MAX), Iv::new(0, u64::MAX)];
        match prove_no_overflow(&doms, &e) {
            SymVerdict::Refuted { witness } => {
                assert_eq!(fault_at(&e, &witness), Some(Fault::MulOverflow));
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
        // Bounded factors whose product fits are proven safe.
        assert_eq!(
            prove_no_overflow(&[Iv::new(0, 1_000_000), Iv::new(0, 1_000_000)], &e),
            SymVerdict::Proven
        );
    }

    #[test]
    fn division_by_zero_is_found_without_being_asked() {
        let e = Expr::var().rem(0);
        match prove_no_overflow(&[Iv::new(0, 10)], &e) {
            SymVerdict::Refuted { witness } => {
                assert_eq!(fault_at(&e, &witness), Some(Fault::DivByZero));
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
        assert_eq!(
            prove_no_overflow(&[Iv::new(0, 10)], &Expr::var().rem(7)),
            SymVerdict::Proven
        );
    }

    #[test]
    fn shift_overflow_is_found() {
        let e = Expr::var().shl(60);
        match prove_no_overflow(&[Iv::full()], &e) {
            SymVerdict::Refuted { witness } => {
                assert_eq!(fault_at(&e, &witness), Some(Fault::ShlOverflow));
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
        // Values small enough that 60 bits of headroom remain are safe.
        assert_eq!(prove_no_overflow(&[Iv::new(0, 15)], &e), SymVerdict::Proven);
    }

    #[test]
    fn correlation_loss_yields_an_honest_unknown_not_a_false_refutation() {
        // x - x is always 0 and never underflows, but interval analysis treats the two occurrences as
        // independent and cannot see that. The correct answer is Unknown -- NOT Refuted, since no
        // assignment actually faults, and NOT Proven, since the abstraction cannot establish it.
        let e = Expr::var().sub(Expr::var());
        assert_eq!(
            prove_no_overflow(&[Iv::new(1, 100)], &e),
            SymVerdict::Unknown,
            "imprecision must surface as Unknown, never as a wrong verdict"
        );
        // And the soundness claim is real: no corner assignment actually faults.
        for xs in corner_assignments(&[Iv::new(1, 100)]) {
            assert!(e.eval_checked(&xs).is_ok(), "x - x never faults");
        }
    }

    #[test]
    fn nested_expressions_propagate_faults_from_subterms() {
        // (x * x) + 1: the inner multiplication is the fault, and it must not be masked by the outer add.
        let e = Expr::var().mul(Expr::var()).add(Expr::c(1));
        assert!(matches!(
            prove_no_overflow(&[Iv::full()], &e),
            SymVerdict::Refuted { .. }
        ));
        assert_eq!(
            prove_no_overflow(&[Iv::new(0, 1000)], &e),
            SymVerdict::Proven
        );
    }

    #[test]
    fn masking_operations_never_fault() {
        // And/Or/Shr cannot overflow, so they are provably safe over any domain.
        let e = Expr::var().and(0xFF).or(0x0F).shr(2);
        assert_eq!(prove_no_overflow(&[Iv::full()], &e), SymVerdict::Proven);
    }
}
