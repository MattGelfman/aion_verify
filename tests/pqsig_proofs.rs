// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Tests for the post-quantum (WOTS hash-based) signature, and signing a ledger head with it.
//!   P1 a genuine signature verifies against the published public key.
//!   P2 a signature does NOT verify on a DIFFERENT message (forgery resistance) — incl. sealing a ledger.
//!   P3 a tampered signature fails; the wrong public key fails.

use aion_verify::ledger::Ledger;
use aion_verify::pqsig::{keygen, sign, verify, Signature, LEN};

fn seed(byte: u8) -> [u8; 64] {
    [byte; 64]
}

#[test]
fn a_genuine_signature_verifies() {
    let s = seed(7);
    let pk = keygen(&s);
    let msg = [0xABu8; 64];
    let sig = sign(&s, &msg);
    assert_eq!(sig.0.len(), LEN);
    assert!(
        verify(&pk, &msg, &sig),
        "a real signature must verify against its public key"
    );
}

#[test]
fn a_signature_does_not_verify_on_a_different_message() {
    let s = seed(9);
    let pk = keygen(&s);
    let mut msg = [0x11u8; 64];
    let sig = sign(&s, &msg);
    assert!(verify(&pk, &msg, &sig));
    // Flip one bit of the message — the signature must no longer verify (forgery resistance).
    msg[0] ^= 1;
    assert!(
        !verify(&pk, &msg, &sig),
        "a signature must not transfer to another message"
    );
}

#[test]
fn a_tampered_signature_or_wrong_key_fails() {
    let s = seed(3);
    let pk = keygen(&s);
    let msg = [0x55u8; 64];
    let mut sig = sign(&s, &msg);
    assert!(verify(&pk, &msg, &sig));

    // Tamper one chain of the signature.
    sig.0[0][0] ^= 0xFF;
    assert!(!verify(&pk, &msg, &sig), "a tampered signature fails");

    // A different key's public key must reject a valid signature.
    let other_pk = keygen(&seed(4));
    let good = sign(&s, &msg);
    assert!(
        !verify(&other_pk, &msg, &good),
        "the wrong public key rejects the signature"
    );
}

#[test]
fn wrong_length_signature_is_rejected() {
    let s = seed(1);
    let pk = keygen(&s);
    let msg = [0u8; 64];
    assert!(
        !verify(&pk, &msg, &Signature(alloc_vec_short())),
        "a truncated signature is rejected"
    );
}

fn alloc_vec_short() -> Vec<[u8; 64]> {
    // A signature of the wrong length must be rejected without panicking.
    vec![[0u8; 64]; LEN - 1]
}

#[test]
fn sealing_a_ledger_head_is_post_quantum_authentic() {
    // The intended use: sign a ledger's head so the whole proof history is provably yours.
    let mut log = Ledger::new();
    log.record("proof over all u64", true);
    log.record("contract holds", true);
    let head = log.head();

    let s = seed(42);
    let pk = keygen(&s); // publish pk as the anchor
    let seal = sign(&s, &head);
    assert!(verify(&pk, &head, &seal), "the sealed head verifies");

    // If anyone rewrites the history, the head changes and the old seal no longer matches it.
    let mut tampered = Ledger::new();
    tampered.record("proof over all u64", false); // flipped
    tampered.record("contract holds", true);
    assert!(
        !verify(&pk, &tampered.head(), &seal),
        "the seal doesn't cover a rewritten history"
    );
}
