//! Unused lemmas for byte-to-nat and word-to-nat conversion operations.
//!
//! These lemmas are kept for reference but are not currently used in the codebase.
//!
//! ## Why these lemmas are unused
//!
//! After simplifying `From<uXX>` implementations to use `bytes_to_nat_prefix` directly,
//! several Horner-related bridge lemmas became unnecessary:
//!
//! - `lemma_bytes32_to_nat_equals_horner`: No longer needed; `From<uXX>` now uses
//!   `lemma_bytes32_to_nat_with_trailing_zeros` directly instead of going through Horner form.
//!
//! - `lemma_bytes_seq_to_nat_trailing_zeros`: The simpler `lemma_prefix_ignores_trailing_zeros`
//!   is now used directly where needed.
//!
//! Note: The Horner form (`bytes_seq_to_nat`) is still actively used for 64-byte wide inputs
//! in `from_bytes_wide` and `from_bytes_mod_order_wide`. The lemmas here are specifically
//! those that became unnecessary after the `From<uXX>` simplification.
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
use crate::specs::core_specs::*;

verus! {

// ============================================================================
// Upper bound lemmas for bytes32_to_nat
// ============================================================================
/// Proves that bytes32_to_nat of a 32-byte array is strictly less than 2^256.
/// Also establishes that bytes32_to_nat(bytes) == bytes32_to_nat(bytes) % pow2(256).
pub proof fn bytes32_to_nat_le_pow2_256(bytes: &[u8; 32])
    ensures
        bytes32_to_nat(&bytes) < pow2(256),
        bytes32_to_nat(&bytes) == bytes32_to_nat(&bytes) % pow2(256),
{
    assert forall|i: nat| 0 <= i <= 31 implies #[trigger] bytes[i as int] * pow2(i * 8) <= pow2(
        (i + 1) * 8,
    ) - pow2(i * 8) by {
        let b = bytes[i as int];
        assert(b < pow2(8)) by {
            lemma_u8_lt_pow2_8(b);
        }
        lemma_pow2_mul_bound_general(b as nat, 8, i * 8);
        assert(i * 8 + 8 == (i + 1) * 8) by {
            lemma_mul_is_distributive_add_other_way(i as int, 1, 8);
        }
    }
    assert(pow2(0 * 8) == 1) by {
        lemma2_to64();
    }
    assert(bytes32_to_nat(&bytes) % pow2(256) == bytes32_to_nat(&bytes)) by {
        lemma_small_mod(bytes32_to_nat(&bytes), pow2(256));
    }
}

// ============================================================================
// 64-byte array lemmas
// ============================================================================
/// Upper bound for 64-byte array to nat: strictly less than 2^512
pub proof fn bytes_seq_to_nat_64_le_pow2_512(bytes: &[u8; 64])
    ensures
        bytes_seq_to_nat(bytes@) < pow2(512),
{
    lemma_bytes_seq_to_nat_equals_prefix(bytes@);
    lemma_bytes_to_nat_prefix_bounded(bytes@, 64);
}

// ============================================================================
// Bridge lemmas: connecting different byte-to-nat representations
// ============================================================================
/// Lemma: bytes32_to_nat (32-byte) equals bytes_to_nat_suffix starting at 0
pub proof fn lemma_bytes32_to_nat_equals_suffix_32(bytes: &[u8; 32])
    ensures
        bytes32_to_nat(bytes) == bytes_to_nat_suffix(bytes, 0),
{
    reveal_with_fuel(bytes_to_nat_suffix, 33);
}

/// Lemma: bytes32_to_nat (explicit form) equals bytes_seq_to_nat (Horner form)
///
/// This is the key bridge lemma that allows interchangeable use of:
/// - `bytes32_to_nat(&bytes)` - the 32-term explicit expansion
/// - `bytes_seq_to_nat(bytes@)` - the Horner-form recursion on sequences
///
/// This simplifies proofs that need to connect array-based and sequence-based
/// representations, such as Scalar::from<uXX> implementations.
pub proof fn lemma_bytes32_to_nat_equals_horner(bytes: &[u8; 32])
    ensures
        bytes32_to_nat(bytes) == bytes_seq_to_nat(bytes@),
{
    // Strategy: Both forms equal bytes_to_nat_prefix(bytes@, 32)
    //
    // Step 1: bytes_seq_to_nat(bytes@) == bytes_to_nat_prefix(bytes@, 32)
    lemma_bytes_seq_to_nat_equals_prefix(bytes@);

    // Step 2: bytes32_to_nat(bytes) == bytes_to_nat_prefix(bytes@, 32)
    // We use: bytes32_to_nat == bytes32_to_nat_rec(0) == prefix(32) + rec(32)
    // And rec(32) == 0, so bytes32_to_nat == prefix(32)
    lemma_bytes32_to_nat_equals_rec(bytes);
    lemma_decomposition_prefix_rec(bytes, 32);
    // bytes32_to_nat_rec(bytes, 32) == 0 by definition (index >= 32)
}

// ============================================================================
// Trailing zeros lemmas
// ============================================================================
/// Lemma: bytes_seq_to_nat ignores trailing zeros.
///
/// For a sequence where bytes after position n are all zero,
/// bytes_seq_to_nat of the full sequence equals bytes_seq_to_nat of the first n bytes.
///
/// This is because both equal bytes_to_nat_prefix(seq, n) - the prefix form
/// that sums only the first n terms.
pub proof fn lemma_bytes_seq_to_nat_trailing_zeros(seq: Seq<u8>, n: nat)
    requires
        n <= seq.len(),
        forall|i: int| n <= i < seq.len() ==> seq[i] == 0,
    ensures
        bytes_seq_to_nat(seq) == bytes_seq_to_nat(seq.take(n as int)),
{
    let prefix = seq.take(n as int);

    // Both sides equal bytes_to_nat_prefix of the appropriate sequence

    // LHS: bytes_seq_to_nat(seq) == bytes_to_nat_prefix(seq, seq.len())
    lemma_bytes_seq_to_nat_equals_prefix(seq);

    // RHS: bytes_seq_to_nat(prefix) == bytes_to_nat_prefix(prefix, n)
    lemma_bytes_seq_to_nat_equals_prefix(prefix);

    // Now we need: bytes_to_nat_prefix(seq, seq.len()) == bytes_to_nat_prefix(prefix, n)
    //
    // Key insight: bytes_to_nat_prefix(seq, seq.len()) == bytes_to_nat_prefix(seq, n)
    // because bytes n..len are all zero and contribute 0 to the sum.
    lemma_prefix_ignores_trailing_zeros(seq, n, seq.len() as nat);

    // And: bytes_to_nat_prefix(seq, n) == bytes_to_nat_prefix(prefix, n)
    // because the first n bytes are identical
    lemma_prefix_equal_when_bytes_match(seq, prefix, n);
}

/// Helper: bytes_to_nat_prefix ignores trailing zeros.
/// prefix(seq, k) == prefix(seq, n) when all bytes from n to k are zero.
proof fn lemma_prefix_ignores_trailing_zeros(seq: Seq<u8>, n: nat, k: nat)
    requires
        n <= k,
        k <= seq.len(),
        forall|i: int| n <= i < k ==> seq[i] == 0,
    ensures
        bytes_to_nat_prefix(seq, k) == bytes_to_nat_prefix(seq, n),
    decreases k - n,
{
    if n == k {
        // Trivial: same prefix
    } else {
        // Show prefix(k) == prefix(k-1) because seq[k-1] == 0
        assert(seq[(k - 1) as int] == 0);

        // prefix(k) = prefix(k-1) + seq[k-1] * pow2((k-1)*8)
        //           = prefix(k-1) + 0 * pow2(...)
        //           = prefix(k-1)
        reveal_with_fuel(bytes_to_nat_prefix, 2);
        lemma2_to64();
        assert(bytes_to_nat_prefix(seq, k) == bytes_to_nat_prefix(seq, (k - 1) as nat));

        // Recurse: prefix(k-1) == prefix(n)
        lemma_prefix_ignores_trailing_zeros(seq, n, (k - 1) as nat);
    }
}

} // verus!
