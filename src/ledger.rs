// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A **tamper-evident, append-only ledger** for proof results.
//!
//! A proof engine is only trustworthy if its outputs can't be quietly forged or a bad result deleted
//! from the record. This module records each verdict in a **hash chain**: every entry carries the
//! cryptographic hash of the entry before it, so altering *any* past entry — or deleting one — changes
//! every hash after it and is detected by [`Ledger::verify`]. It is a blockchain's core guarantee
//! (an immutable, verifiable history) without the distributed-consensus machinery a single authority
//! doesn't need.
//!
//! **Preventing deletion.** The chain makes tampering *evident*; to make deletion *provable* against a
//! third party, periodically anchor [`Ledger::head`] (the 64-byte head hash) somewhere out of the
//! writer's control — publish it, commit it, or write it to WORM storage. Any later divergence from the
//! anchored head is proof the log was cut or rewritten.
//!
//! **Post-quantum.** The hash is a self-contained pure-Rust **SHA-512** ([`sha512`]) — no dependencies,
//! `no_std`. Hash functions are quantum-resistant (Grover gives only a quadratic speedup, and SHA-512
//! keeps a full 256-bit collision-resistance margin even then), and there is no quantum-vulnerable
//! primitive (no RSA/ECC) anywhere here.

use alloc::vec::Vec;

/// The size of a SHA-512 digest / ledger hash, in bytes.
pub const HASH_LEN: usize = 64;

// ── SHA-512 (FIPS 180-4), pure Rust, no dependencies ──────────────────────────────────────────────

#[rustfmt::skip]
const K: [u64; 80] = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];

/// The SHA-512 digest of `data` (FIPS 180-4). Pure Rust, no dependencies. `no_std`.
pub fn sha512(data: &[u8]) -> [u8; 64] {
    let mut h: [u64; 8] = [
        0x6a09e667f3bcc908,
        0xbb67ae8584caa73b,
        0x3c6ef372fe94f82b,
        0xa54ff53a5f1d36f1,
        0x510e527fade682d1,
        0x9b05688c2b3e6c1f,
        0x1f83d9abfb41bd6b,
        0x5be0cd19137e2179,
    ];
    // Pad: append 0x80, then zeros, then the 128-bit big-endian bit length, to a multiple of 128 bytes.
    // Messages here are far below 2^64 bits, so the high 64 length bits are zero.
    let bitlen = (data.len() as u128).wrapping_mul(8);
    let mut msg = data.to_vec();
    msg.push(0x80);
    while msg.len() % 128 != 112 {
        msg.push(0);
    }
    msg.extend_from_slice(&bitlen.to_be_bytes());

    let mut w = [0u64; 80];
    for chunk in msg.chunks_exact(128) {
        for (i, wi) in w.iter_mut().enumerate().take(16) {
            let mut b = [0u8; 8];
            b.copy_from_slice(&chunk[i * 8..i * 8 + 8]);
            *wi = u64::from_be_bytes(b);
        }
        for i in 16..80 {
            let s0 = w[i - 15].rotate_right(1) ^ w[i - 15].rotate_right(8) ^ (w[i - 15] >> 7);
            let s1 = w[i - 2].rotate_right(19) ^ w[i - 2].rotate_right(61) ^ (w[i - 2] >> 6);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..80 {
            let s1 = e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41);
            let ch = (e & f) ^ ((!e) & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }
    let mut out = [0u8; 64];
    for (i, word) in h.iter().enumerate() {
        out[i * 8..i * 8 + 8].copy_from_slice(&word.to_be_bytes());
    }
    out
}

// ── The append-only proof ledger ──────────────────────────────────────────────────────────────────

/// One record in the ledger: its sequence number, the hash of the previous entry, its payload, and its
/// own hash (`SHA-512(seq ‖ prev ‖ data)`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Entry {
    pub seq: u64,
    pub prev: [u8; HASH_LEN],
    pub data: Vec<u8>,
    pub hash: [u8; HASH_LEN],
}

fn entry_hash(seq: u64, prev: &[u8; HASH_LEN], data: &[u8]) -> [u8; HASH_LEN] {
    let mut buf = Vec::with_capacity(8 + HASH_LEN + data.len());
    buf.extend_from_slice(&seq.to_be_bytes());
    buf.extend_from_slice(prev);
    buf.extend_from_slice(data);
    sha512(&buf)
}

/// An append-only hash chain of records. Appending is the only mutation; the chain of hashes makes any
/// later alteration or deletion detectable by [`verify`](Ledger::verify).
#[derive(Default, Clone)]
pub struct Ledger {
    entries: Vec<Entry>,
}

impl Ledger {
    pub fn new() -> Ledger {
        Ledger {
            entries: Vec::new(),
        }
    }

    /// Load a ledger from stored entries (e.g. read back from disk). The load is unchecked — call
    /// [`verify`](Ledger::verify) afterwards to confirm the persisted chain wasn't tampered with. This
    /// is the real integrity check: write the chain, reload it, and verify against the anchored head.
    pub fn from_entries(entries: Vec<Entry>) -> Ledger {
        Ledger { entries }
    }

    /// The current head hash — the 64-byte fingerprint of the whole history. Anchor this externally to
    /// make deletion provable. All-zero for an empty ledger.
    pub fn head(&self) -> [u8; HASH_LEN] {
        self.entries
            .last()
            .map(|e| e.hash)
            .unwrap_or([0u8; HASH_LEN])
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    pub fn entries(&self) -> &[Entry] {
        &self.entries
    }

    /// Append arbitrary bytes, chaining them to the current head. Returns the new head hash.
    pub fn append(&mut self, data: &[u8]) -> [u8; HASH_LEN] {
        let seq = self.entries.len() as u64;
        let prev = self.head();
        let hash = entry_hash(seq, &prev, data);
        self.entries.push(Entry {
            seq,
            prev,
            data: data.to_vec(),
            hash,
        });
        hash
    }

    /// Record a proof result: a label and whether it was proven. Returns the new head hash.
    pub fn record(&mut self, label: &str, proven: bool) -> [u8; HASH_LEN] {
        let mut d = Vec::with_capacity(label.len() + 2);
        d.extend_from_slice(label.as_bytes());
        d.push(0);
        d.push(u8::from(proven));
        self.append(&d)
    }

    /// Verify the chain is intact end to end. `Ok(())` means every entry's sequence, back-link, and
    /// hash are consistent — the history is authentic and complete. `Err(seq)` names the first entry
    /// where tampering (an altered payload, a broken link, or a deletion/insertion) is detected.
    pub fn verify(&self) -> Result<(), u64> {
        let mut prev = [0u8; HASH_LEN];
        for (i, e) in self.entries.iter().enumerate() {
            if e.seq != i as u64 {
                return Err(i as u64); // a gap = an entry was deleted or inserted
            }
            if e.prev != prev {
                return Err(e.seq); // back-link broken
            }
            if e.hash != entry_hash(e.seq, &e.prev, &e.data) {
                return Err(e.seq); // payload or stored hash altered
            }
            prev = e.hash;
        }
        Ok(())
    }
}
