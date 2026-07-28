// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Tests for the many-time Merkle (XMSS-style) post-quantum signature.
//!   P1 ONE published root authenticates MANY signatures (different leaves), each verifying.
//!   P2 a tampered signature, a wrong message, or the wrong root all fail.
//!   P3 the key refuses to reuse a leaf — capacity is exactly 2^height, then sign() returns None.

use aion_verify::mss::{verify, MerkleKey};

fn seed(b: u8) -> [u8; 64] {
    [b; 64]
}

#[test]
fn one_root_authenticates_many_signatures() {
    let mut key = MerkleKey::keygen(&seed(1), 4); // 16 leaves
    let root = key.root;
    let height = key.height;

    // Sign several distinct messages; each verifies against the SAME published root.
    for i in 0..8u8 {
        let msg = [i.wrapping_mul(37); 64];
        let sig = key.sign(&msg).expect("capacity not exhausted");
        assert_eq!(sig.index, i as u32, "leaves are used in order");
        assert!(
            verify(&root, height, &msg, &sig),
            "signature {i} verifies against the one root"
        );
    }
}

#[test]
fn tampering_message_signature_or_root_fails() {
    let mut key = MerkleKey::keygen(&seed(2), 3);
    let root = key.root;
    let h = key.height;
    let msg = [0x5Au8; 64];
    let sig = key.sign(&msg).unwrap();
    assert!(verify(&root, h, &msg, &sig));

    // Wrong message.
    let mut other = msg;
    other[0] ^= 1;
    assert!(!verify(&root, h, &other, &sig), "a different message fails");

    // Tampered authentication path.
    let mut bad = MerkleKey::keygen(&seed(2), 3).sign(&msg).unwrap();
    bad.path[0][0] ^= 0xFF;
    assert!(!verify(&root, h, &msg, &bad), "a broken auth path fails");

    // Wrong root (another key's root).
    let wrong_root = MerkleKey::keygen(&seed(9), 3).root;
    assert!(
        !verify(&wrong_root, h, &msg, &sig),
        "the wrong root rejects the signature"
    );
}

#[test]
fn capacity_is_exactly_two_to_the_height_then_refuses() {
    let mut key = MerkleKey::keygen(&seed(3), 3); // 8 leaves
    assert_eq!(key.capacity(), 8);
    for i in 0..8 {
        assert!(key.sign(&[i as u8; 64]).is_some(), "leaf {i} available");
    }
    assert_eq!(key.used(), 8);
    assert!(
        key.sign(&[0u8; 64]).is_none(),
        "no leaf may be reused past capacity"
    );
}
