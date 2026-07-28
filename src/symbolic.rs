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

    fn eval_iv(&self, doms: &[Iv]) -> Tri {
        match self {
            Prop::Le(a, b) => cmp_le(a.eval_iv(doms), b.eval_iv(doms)),
            Prop::Lt(a, b) => cmp_lt(a.eval_iv(doms), b.eval_iv(doms)),
            Prop::Ge(a, b) => cmp_le(b.eval_iv(doms), a.eval_iv(doms)),
            Prop::Gt(a, b) => cmp_lt(b.eval_iv(doms), a.eval_iv(doms)),
            Prop::Eq(a, b) => cmp_eq(a.eval_iv(doms), b.eval_iv(doms)),
            Prop::Ne(a, b) => cmp_eq(a.eval_iv(doms), b.eval_iv(doms)).negate(),
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
