// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Tests for the tamper-evident proof ledger.
//!   P1 the pure-Rust SHA-256 matches the FIPS 180-4 known-answer vectors (the crypto is correct).
//!   P2 a well-formed chain verifies; the head changes with every record.
//!   P3 altering ANY past record's payload is detected by verify() (tamper-evidence).
//!   P4 deleting a record from the middle is detected (the log can't be silently cut).

use aion_verify::ledger::{sha512, Ledger};

fn hex(b: &[u8]) -> String {
    let mut s = String::new();
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

#[test]
fn sha512_matches_fips_known_answers() {
    assert_eq!(
        hex(&sha512(b"")),
        "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
    );
    assert_eq!(
        hex(&sha512(b"abc")),
        "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
    );
    assert_eq!(
        hex(&sha512(
            b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
        )),
        "204a8fc6dda82f0a0ced7beb8e08a41657c16ef468b228a8279be331a703c33596fd15c13b1b07f9aa1d3bea57789ca031ad85c7a71dd70354ec631238ca3445"
    );
}

#[test]
fn a_well_formed_chain_verifies_and_the_head_moves() {
    let mut l = Ledger::new();
    assert_eq!(l.head(), [0u8; 64], "empty ledger has a zero head");
    let h1 = l.record("x+1 > x over u8", true);
    let h2 = l.record("x <= 100 over u64", false); // a REFUTED result is recorded too
    let h3 = l.record("(x>>1) <= x refined", true);
    assert!(h1 != h2 && h2 != h3, "the head advances with every record");
    assert_eq!(l.len(), 3);
    assert_eq!(l.head(), h3);
    assert_eq!(l.verify(), Ok(()), "an untampered chain verifies");
}

#[test]
fn altering_a_past_record_is_detected() {
    let mut l = Ledger::new();
    l.record("proof A", true);
    l.record("proof B", true);
    l.record("proof C", true);

    // Reload the chain, then flip a "proven" flag on the FIRST record (forging a false proof).
    let mut entries = l.entries().to_vec();
    let last = entries[0].data.len() - 1;
    entries[0].data[last] ^= 1; // true -> false
    let tampered = Ledger::from_entries(entries);
    assert_eq!(
        tampered.verify(),
        Err(0),
        "altering record 0's payload is caught at seq 0"
    );
}

#[test]
fn deleting_a_record_is_detected() {
    let mut l = Ledger::new();
    for i in 0..5 {
        l.record("proof", i % 2 == 0);
    }
    // Cut the middle record out of the persisted chain.
    let mut entries = l.entries().to_vec();
    entries.remove(2);
    let cut = Ledger::from_entries(entries);
    // The entry now at index 2 has seq 3 -> sequence gap detected immediately.
    assert!(cut.verify().is_err(), "a deleted record breaks the chain");
    assert_eq!(cut.verify(), Err(2));
}

#[test]
fn a_diverged_head_proves_rewriting_against_an_anchor() {
    // The real deletion defence: anchor the head, later re-derive it; divergence = proof of rewriting.
    let mut a = Ledger::new();
    a.record("r0", true);
    a.record("r1", false);
    let anchored_head = a.head();

    // A rewritten history (r1 flipped to proven) produces a different head — detectable against the anchor.
    let mut b = Ledger::new();
    b.record("r0", true);
    b.record("r1", true);
    assert_ne!(
        b.head(),
        anchored_head,
        "any rewrite diverges from the anchored head"
    );
}
