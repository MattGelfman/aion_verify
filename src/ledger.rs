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
//! third party, periodically anchor [`Ledger::head`] (the 32-byte head hash) somewhere out of the
//! writer's control — publish it, commit it, or write it to WORM storage. Any later divergence from the
//! anchored head is proof the log was cut or rewritten.
//!
//! The hash is a self-contained pure-Rust **SHA-256** ([`sha256`]) — no dependencies, `no_std`.

use alloc::vec::Vec;

// ── SHA-256 (FIPS 180-4), pure Rust, no dependencies ──────────────────────────────────────────────

#[rustfmt::skip]
const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// The SHA-256 digest of `data` (FIPS 180-4). Pure Rust, allocation-light, no dependencies.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    // Pad: append 0x80, then zeros, then the 64-bit big-endian bit length, to a multiple of 64 bytes.
    let bitlen = (data.len() as u64).wrapping_mul(8);
    let mut msg = data.to_vec();
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bitlen.to_be_bytes());

    let mut w = [0u32; 64];
    for chunk in msg.chunks_exact(64) {
        for (i, wi) in w.iter_mut().enumerate().take(16) {
            *wi = u32::from_be_bytes([
                chunk[i * 4],
                chunk[i * 4 + 1],
                chunk[i * 4 + 2],
                chunk[i * 4 + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
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
    let mut out = [0u8; 32];
    for (i, word) in h.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

// ── The append-only proof ledger ──────────────────────────────────────────────────────────────────

/// One record in the ledger: its sequence number, the hash of the previous entry, its payload, and its
/// own hash (`SHA-256(seq ‖ prev ‖ data)`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Entry {
    pub seq: u64,
    pub prev: [u8; 32],
    pub data: Vec<u8>,
    pub hash: [u8; 32],
}

fn entry_hash(seq: u64, prev: &[u8; 32], data: &[u8]) -> [u8; 32] {
    let mut buf = Vec::with_capacity(8 + 32 + data.len());
    buf.extend_from_slice(&seq.to_be_bytes());
    buf.extend_from_slice(prev);
    buf.extend_from_slice(data);
    sha256(&buf)
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

    /// The current head hash — the 32-byte fingerprint of the whole history. Anchor this externally to
    /// make deletion provable. Zero for an empty ledger.
    pub fn head(&self) -> [u8; 32] {
        self.entries.last().map(|e| e.hash).unwrap_or([0u8; 32])
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
    pub fn append(&mut self, data: &[u8]) -> [u8; 32] {
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
    pub fn record(&mut self, label: &str, proven: bool) -> [u8; 32] {
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
        let mut prev = [0u8; 32];
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
