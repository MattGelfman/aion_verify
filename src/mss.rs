// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! **Many-time post-quantum signatures** — a Merkle Signature Scheme (XMSS-style) over the one-time
//! WOTS of [`crate::pqsig`].
//!
//! WOTS signs one message per key. This builds a binary Merkle tree of `2^height` WOTS keypairs; the
//! **single published public key is the tree root**, and each signature carries a WOTS signature under
//! one leaf plus the `height` sibling hashes (the *authentication path*) that let a verifier recompute
//! the root. So one 64-byte published key authenticates `2^height` proofs — an unbounded-in-practice
//! signed proof stream, still resting only on SHA-512 (post-quantum, no Shor exposure), still zero-dep.
//!
//! **Stateful.** Each leaf must sign at most once, so [`MerkleKey::sign`] advances an internal index and
//! refuses to reuse a leaf. Keep `height` modest (keygen builds all `2^height` WOTS keys): 8–12 gives
//! 256–4096 signatures per published key.

use crate::ledger::sha512;
use crate::pqsig;
use alloc::vec::Vec;

const N: usize = 64;

/// Domain-separated leaf hash of a WOTS public key.
fn leaf_hash(wots_pk: &[u8; N]) -> [u8; N] {
    let mut b = Vec::with_capacity(1 + N);
    b.push(0x00);
    b.extend_from_slice(wots_pk);
    sha512(&b)
}

/// Domain-separated internal-node hash of two children.
fn node_hash(left: &[u8; N], right: &[u8; N]) -> [u8; N] {
    let mut b = Vec::with_capacity(1 + 2 * N);
    b.push(0x01);
    b.extend_from_slice(left);
    b.extend_from_slice(right);
    sha512(&b)
}

/// The one-time WOTS seed for leaf `i`, derived from the master seed (domain-separated from WOTS's own
/// per-chain derivation).
fn leaf_seed(seed: &[u8; N], i: u32) -> [u8; N] {
    let mut b = Vec::with_capacity(N + 5);
    b.extend_from_slice(seed);
    b.push(0x02);
    b.extend_from_slice(&i.to_be_bytes());
    sha512(&b)
}

fn build_levels(leaves: &[[u8; N]]) -> Vec<Vec<[u8; N]>> {
    let mut levels = alloc::vec![leaves.to_vec()];
    while levels.last().map(Vec::len).unwrap_or(0) > 1 {
        let cur = levels.last().unwrap();
        let mut next = Vec::with_capacity(cur.len() / 2);
        for pair in cur.chunks(2) {
            next.push(node_hash(&pair[0], &pair[1])); // leaf count is 2^height, so pairs are complete
        }
        levels.push(next);
    }
    levels
}

/// A stateful many-time Merkle key. The public value is [`MerkleKey::root`]; keep the whole struct
/// secret (it holds the seed) and let it track which leaf to use next.
pub struct MerkleKey {
    seed: [u8; N],
    pub height: u32,
    pub root: [u8; N],
    next: u32,
    leaves: Vec<[u8; N]>,
}

/// A many-time signature: which leaf signed, the WOTS signature, and the authentication path to the root.
pub struct MerkleSig {
    pub index: u32,
    pub wots: pqsig::Signature,
    pub path: Vec<[u8; N]>,
}

impl MerkleKey {
    /// Generate a key with `2^height` one-time leaves. Cost is `2^height` WOTS keygens — keep `height`
    /// modest (≤ ~12).
    pub fn keygen(seed: &[u8; N], height: u32) -> MerkleKey {
        let n = 1u32 << height;
        let mut leaves = Vec::with_capacity(n as usize);
        for i in 0..n {
            let wots_pk = pqsig::keygen(&leaf_seed(seed, i));
            leaves.push(leaf_hash(&wots_pk));
        }
        let root = build_levels(&leaves).last().unwrap()[0];
        MerkleKey {
            seed: *seed,
            height,
            root,
            next: 0,
            leaves,
        }
    }

    /// Number of signatures already produced.
    pub fn used(&self) -> u32 {
        self.next
    }
    /// Total capacity (`2^height`).
    pub fn capacity(&self) -> u32 {
        1u32 << self.height
    }

    /// Sign the next message. Returns `None` once every leaf has been used (never reuse a leaf).
    pub fn sign(&mut self, msg: &[u8; N]) -> Option<MerkleSig> {
        if self.next >= self.capacity() {
            return None;
        }
        let index = self.next;
        self.next += 1;
        let wots = pqsig::sign(&leaf_seed(&self.seed, index), msg);
        let levels = build_levels(&self.leaves);
        let mut path = Vec::with_capacity(self.height as usize);
        let mut idx = index;
        for lv in levels.iter().take(self.height as usize) {
            path.push(lv[(idx ^ 1) as usize]);
            idx >>= 1;
        }
        Some(MerkleSig { index, wots, path })
    }
}

/// Verify a many-time signature against the published `root` and tree `height`. Recovers the leaf WOTS
/// public key, then folds the authentication path up to a root and checks it equals `root`.
pub fn verify(root: &[u8; N], height: u32, msg: &[u8; N], sig: &MerkleSig) -> bool {
    if sig.path.len() != height as usize || sig.index >= (1u32 << height) {
        return false;
    }
    let leaf_pk = match pqsig::pk_from_sig(msg, &sig.wots) {
        Some(pk) => pk,
        None => return false,
    };
    let mut node = leaf_hash(&leaf_pk);
    let mut idx = sig.index;
    for sib in &sig.path {
        node = if idx & 1 == 0 {
            node_hash(&node, sib)
        } else {
            node_hash(sib, &node)
        };
        idx >>= 1;
    }
    node == *root
}
