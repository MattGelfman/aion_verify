// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! **Post-quantum authenticity** — a WOTS (Winternitz one-time) hash-based signature over SHA-512.
//!
//! Hash-based signatures are the most conservative post-quantum family: their security rests **only on
//! the hash function** ([`crate::ledger::sha512`]), so nothing here falls to Shor's algorithm the way
//! classical ECDSA/Ed25519/RSA do. Signing the [`crate::ledger::Ledger`] head with this makes the log
//! not just tamper-evident but **provably yours**, and post-quantum.
//!
//! **ONE-TIME.** A WOTS keypair must sign **at most one** message. The intended use is: seal a ledger
//! snapshot by signing its head, publish the [`keygen`] public key as the anchor, and re-key for the
//! next snapshot. To sign an unbounded stream from a single published key, lift WOTS to many-time with a
//! Merkle tree (XMSS) or SPHINCS+ — both build on exactly this primitive.
//!
//! No dependencies, `no_std`.

use crate::ledger::sha512;
use alloc::vec::Vec;

const N: usize = 64; // SHA-512 output size
const W: usize = 16; // Winternitz parameter (4 bits per chain)
const MSG_DIGITS: usize = 128; // a 64-byte message = 128 base-16 digits
const CKSUM_DIGITS: usize = 3; // checksum (max 128*15=1920 = 0x780) fits in 3 base-16 digits
/// Number of hash chains in a keypair/signature.
pub const LEN: usize = MSG_DIGITS + CKSUM_DIGITS; // 131

/// Apply SHA-512 `iters` times (a hash chain).
fn chain(mut x: [u8; N], iters: usize) -> [u8; N] {
    for _ in 0..iters {
        x = sha512(&x);
    }
    x
}

/// Deterministically derive the i-th secret chain start from the seed.
fn sk_element(seed: &[u8; N], i: usize) -> [u8; N] {
    let mut buf = Vec::with_capacity(N + 8);
    buf.extend_from_slice(seed);
    buf.extend_from_slice(&(i as u64).to_be_bytes());
    sha512(&buf)
}

/// The base-16 digits of the 64-byte message, followed by the 3 checksum digits.
fn digits(msg: &[u8; N]) -> [usize; LEN] {
    let mut d = [0usize; LEN];
    for (i, &b) in msg.iter().enumerate() {
        d[i * 2] = (b >> 4) as usize;
        d[i * 2 + 1] = (b & 0x0F) as usize;
    }
    // Checksum prevents forging a message by only *increasing* digits (which is easy — hash forward).
    let mut cksum = 0usize;
    for &di in d.iter().take(MSG_DIGITS) {
        cksum += (W - 1) - di;
    }
    d[MSG_DIGITS] = (cksum >> 8) & 0x0F;
    d[MSG_DIGITS + 1] = (cksum >> 4) & 0x0F;
    d[MSG_DIGITS + 2] = cksum & 0x0F;
    d
}

/// Generate the public key (the 64-byte anchor) for a one-time `seed`. Publish this; signatures verify
/// against it. Keep the seed secret and use it to sign **exactly one** message.
pub fn keygen(seed: &[u8; N]) -> [u8; N] {
    let mut concat = Vec::with_capacity(LEN * N);
    for i in 0..LEN {
        concat.extend_from_slice(&chain(sk_element(seed, i), W - 1));
    }
    sha512(&concat)
}

/// A WOTS signature — one chained secret per hash chain.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signature(pub Vec<[u8; N]>);

/// Sign a 64-byte message (e.g. a ledger head) with the one-time `seed`. Never reuse a seed.
pub fn sign(seed: &[u8; N], msg: &[u8; N]) -> Signature {
    let d = digits(msg);
    let mut sig = Vec::with_capacity(LEN);
    for (i, &di) in d.iter().enumerate() {
        sig.push(chain(sk_element(seed, i), di));
    }
    Signature(sig)
}

/// Verify `sig` on `msg` against the published `public_key`. Returns true iff the signature is authentic.
pub fn verify(public_key: &[u8; N], msg: &[u8; N], sig: &Signature) -> bool {
    if sig.0.len() != LEN {
        return false;
    }
    let d = digits(msg);
    let mut concat = Vec::with_capacity(LEN * N);
    for (i, &di) in d.iter().enumerate() {
        // Finish each chain from where the signature stopped; it must land on the public key element.
        concat.extend_from_slice(&chain(sig.0[i], (W - 1) - di));
    }
    sha512(&concat) == *public_key
}
