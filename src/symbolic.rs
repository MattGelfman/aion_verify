// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! TIER 5 — symbolic verification over *unbounded* integer domains, in pure Rust.
//!
//! Tier 4 ([`crate::for_all`]) enumerates: it proves a property by checking every value, so it can only
//! cover finite/bounded domains. Tier 5 proves properties over the **entire** domain — including all
//! 2^64 values of `u64` — **without enumerating it**, by *interval abstract interpretation*: it computes,
//! for each sub-expression, an interval guaranteed to contain every value that expression can take, then
//! decides the property over those intervals.
//!
//! Because tier 5 must *reason about* an expression rather than merely call it, its predicates are a
//! small first-party [`Expr`]/[`Prop`] DSL (an opaque `Fn` can't be analysed — only executed).
//!
//! **Soundness is the whole point** — the interval transfer functions always *over-approximate* (the
//! true set of values is a subset of the computed interval), and every uncertain case degrades to
//! [`SymVerdict::Unknown`] rather than guessing:
//!  - [`SymVerdict::Proven`] — the property holds for **every** value in the domain (a real proof).
//!  - [`SymVerdict::Refuted`] — carries a **concrete** witness that actually falsifies it.
//!  - [`SymVerdict::Unknown`] — the interval abstraction wasn't precise enough to decide. Never a false
//!    Proven or Refuted.
//!
//! This is the role Kani/CBMC plays, done entirely first-party: no C, no external solver, no WSL —
//! `no_std`, only `alloc` for the expression tree.

// This module is a small expression DSL: several builder methods (add/sub/mul/shl/shr/rem/not)
// intentionally mirror operator names for readability, so `should_implement_trait` is a non-issue here.
#![allow(clippy::should_implement_trait)]

use alloc::boxed::Box;

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
        // min = self.lo - o.hi, max = self.hi - o.lo; sound only if neither underflows.
        match (self.lo.checked_sub(o.hi), self.hi.checked_sub(o.lo)) {
            (Some(lo), Some(hi)) => Iv { lo, hi },
            _ => Iv::full(),
        }
    }
    fn mul(self, o: Iv) -> Iv {
        // All values are non-negative, so mul is monotone in both args.
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
        // No value overflow iff hi <= (MAX >> k). shl is monotone.
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
        // x & mask <= mask, and x & mask <= x <= self.hi, and >= 0.
        let hi = if mask < self.hi { mask } else { self.hi };
        Iv { lo: 0, hi }
    }
    fn bitor(self, mask: u64) -> Iv {
        // x | mask >= mask and >= x >= self.lo. Upper bound is conservative.
        let lo = if mask > self.lo { mask } else { self.lo };
        Iv { lo, hi: u64::MAX }
    }
    fn rem(self, m: u64) -> Iv {
        if m == 0 {
            return Iv::full(); // avoid a division trap; caller shouldn't do this
        }
        if self.hi < m {
            self // x < m => x % m == x
        } else {
            Iv { lo: 0, hi: m - 1 }
        }
    }
}

/// An integer expression over a single symbolic variable `x`, evaluated in the `u64` bitvector domain
/// (wrapping arithmetic, like real Rust `u64`).
#[derive(Clone, Debug)]
pub enum Expr {
    /// The symbolic input variable.
    Var,
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
    // Ergonomic builders.
    pub fn var() -> Expr {
        Expr::Var
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

    /// Abstract evaluation: the interval of every value this expression can take when `x` ranges over
    /// `x_iv`. Guaranteed to be a superset of the true value set (soundness).
    fn eval_iv(&self, x_iv: Iv) -> Iv {
        match self {
            Expr::Var => x_iv,
            Expr::Const(v) => Iv::point(*v),
            Expr::Add(a, b) => a.eval_iv(x_iv).add(b.eval_iv(x_iv)),
            Expr::Sub(a, b) => a.eval_iv(x_iv).sub(b.eval_iv(x_iv)),
            Expr::Mul(a, b) => a.eval_iv(x_iv).mul(b.eval_iv(x_iv)),
            Expr::Shl(a, k) => a.eval_iv(x_iv).shl(*k),
            Expr::Shr(a, k) => a.eval_iv(x_iv).shr(*k),
            Expr::And(a, m) => a.eval_iv(x_iv).bitand(*m),
            Expr::Or(a, m) => a.eval_iv(x_iv).bitor(*m),
            Expr::Rem(a, m) => a.eval_iv(x_iv).rem(*m),
        }
    }

    /// Concrete evaluation at a single `x` (wrapping `u64` arithmetic) — used to confirm witnesses.
    fn eval_at(&self, x: u64) -> u64 {
        match self {
            Expr::Var => x,
            Expr::Const(v) => *v,
            Expr::Add(a, b) => a.eval_at(x).wrapping_add(b.eval_at(x)),
            Expr::Sub(a, b) => a.eval_at(x).wrapping_sub(b.eval_at(x)),
            Expr::Mul(a, b) => a.eval_at(x).wrapping_mul(b.eval_at(x)),
            Expr::Shl(a, k) => a.eval_at(x).wrapping_shl(*k),
            Expr::Shr(a, k) => a.eval_at(x).wrapping_shr(*k),
            Expr::And(a, m) => a.eval_at(x) & *m,
            Expr::Or(a, m) => a.eval_at(x) | *m,
            Expr::Rem(a, m) => {
                if *m == 0 {
                    0
                } else {
                    a.eval_at(x) % *m
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
    fn not(self) -> Tri {
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

/// A boolean property of the symbolic variable `x`, built from comparisons of [`Expr`]s and the usual
/// connectives.
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

    fn eval_iv(&self, x_iv: Iv) -> Tri {
        match self {
            Prop::Le(a, b) => cmp_le(a.eval_iv(x_iv), b.eval_iv(x_iv)),
            Prop::Lt(a, b) => cmp_lt(a.eval_iv(x_iv), b.eval_iv(x_iv)),
            Prop::Ge(a, b) => cmp_le(b.eval_iv(x_iv), a.eval_iv(x_iv)),
            Prop::Gt(a, b) => cmp_lt(b.eval_iv(x_iv), a.eval_iv(x_iv)),
            Prop::Eq(a, b) => cmp_eq(a.eval_iv(x_iv), b.eval_iv(x_iv)),
            Prop::Ne(a, b) => cmp_eq(a.eval_iv(x_iv), b.eval_iv(x_iv)).not(),
            Prop::And(p, q) => p.eval_iv(x_iv).and(q.eval_iv(x_iv)),
            Prop::Or(p, q) => p.eval_iv(x_iv).or(q.eval_iv(x_iv)),
            Prop::Not(p) => p.eval_iv(x_iv).not(),
            Prop::Implies(p, q) => p.eval_iv(x_iv).not().or(q.eval_iv(x_iv)),
        }
    }

    fn eval_at(&self, x: u64) -> bool {
        match self {
            Prop::Le(a, b) => a.eval_at(x) <= b.eval_at(x),
            Prop::Lt(a, b) => a.eval_at(x) < b.eval_at(x),
            Prop::Ge(a, b) => a.eval_at(x) >= b.eval_at(x),
            Prop::Gt(a, b) => a.eval_at(x) > b.eval_at(x),
            Prop::Eq(a, b) => a.eval_at(x) == b.eval_at(x),
            Prop::Ne(a, b) => a.eval_at(x) != b.eval_at(x),
            Prop::And(p, q) => p.eval_at(x) && q.eval_at(x),
            Prop::Or(p, q) => p.eval_at(x) || q.eval_at(x),
            Prop::Not(p) => !p.eval_at(x),
            Prop::Implies(p, q) => !p.eval_at(x) || q.eval_at(x),
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
        Tri::False // disjoint intervals can never be equal
    } else {
        Tri::Unknown
    }
}

/// The outcome of a tier-5 symbolic proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymVerdict {
    /// The property holds for every value in the domain — a proof, no enumeration.
    Proven,
    /// The property fails; `witness` is a concrete value that falsifies it (confirmed by evaluation).
    Refuted { witness: u64 },
    /// The interval abstraction was too imprecise to decide. Never a false Proven/Refuted.
    Unknown,
}

/// Prove `prop` holds for **every** `x` in `domain` — symbolically, without enumerating the domain.
///
/// Sound: a `Proven` result means the interval analysis established the property over a *superset* of
/// the domain, so it holds for the domain itself. A `Refuted` result is always backed by a concrete
/// witness confirmed with wrapping arithmetic. Otherwise `Unknown`.
pub fn prove_forall(domain: Iv, prop: &Prop) -> SymVerdict {
    match prop.eval_iv(domain) {
        Tri::True => SymVerdict::Proven,
        Tri::False => {
            // The property is false across the whole (over-approximated) domain; the low endpoint is a
            // real value in the domain — confirm it concretely so the witness is never spurious.
            if !prop.eval_at(domain.lo) {
                SymVerdict::Refuted { witness: domain.lo }
            } else {
                probe_witnesses(domain, prop)
            }
        }
        Tri::Unknown => probe_witnesses(domain, prop),
    }
}

/// When the abstraction can't decide, try the values most likely to break a property — the domain
/// endpoints and bit boundaries — concretely. A hit is a genuine counterexample; otherwise Unknown.
fn probe_witnesses(domain: Iv, prop: &Prop) -> SymVerdict {
    let mut candidates = [
        domain.lo,
        domain.hi,
        domain.lo.wrapping_add(1),
        domain.hi.wrapping_sub(1),
        domain
            .lo
            .wrapping_add((domain.hi.wrapping_sub(domain.lo)) / 2),
        0,
        u64::MAX,
        1,
        u64::MAX >> 1,
        1u64 << 63,
    ];
    // De-dup is unnecessary; a redundant check is harmless.
    for w in candidates.iter_mut() {
        if domain.contains(*w) && !prop.eval_at(*w) {
            return SymVerdict::Refuted { witness: *w };
        }
    }
    SymVerdict::Unknown
}
