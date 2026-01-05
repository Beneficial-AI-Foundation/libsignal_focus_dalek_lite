//! Verified byte conversion utilities
//!
//! This module provides pure Verus implementations for converting integers to
//! little-endian byte arrays. All functions are fully verified with no `external_body`
//! or `assume` statements - the correctness of the byte decomposition is proven
//! using bit-vector SMT solver proofs.
//!
//! Each function ensures that `bytes_to_nat_prefix(bytes@, N) == x as nat`, meaning the
//! resulting byte array, when interpreted as a little-endian natural number,
//! equals the input integer value.
use crate::specs::core_specs::bytes_to_nat_prefix;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Convert u16 to little-endian bytes (pure Verus, no external_body)
pub fn u16_to_le_bytes(x: u16) -> (bytes: [u8; 2])
    ensures
        bytes_to_nat_prefix(bytes@, 2) == x as nat,
{
    // Extract low and high bytes using bit masking
    let masked0 = x & 0xff;
    let masked1 = (x >> 8) & 0xff;

    // Prove masked values fit in u8 (< 256)
    proof {
        assert(masked0 < 256) by (bit_vector)
            requires
                masked0 == x & 0xff,
        ;
        assert(masked1 < 256) by (bit_vector)
            requires
                masked1 == (x >> 8) & 0xff,
        ;
    }

    // Now casts are safe - Verus knows values fit in u8
    let b0 = masked0 as u8;
    let b1 = masked1 as u8;
    let bytes = [b0, b1];

    proof {
        lemma2_to64();

        // Unfold bytes_to_nat_prefix for 2 bytes
        reveal_with_fuel(bytes_to_nat_prefix, 3);

        // bytes_to_nat_prefix([b0, b1], 2) = prefix(1) + pow2(8) * b1 = b0 + 256 * b1

        // Prove b0 + 256 * b1 == x using bit_vector
        assert(b0 as nat + b1 as nat * 256 == x as nat) by (bit_vector)
            requires
                b0 == (x & 0xff) as u8,
                b1 == ((x >> 8) & 0xff) as u8,
        ;
    }
    bytes
}

/// Convert u32 to little-endian bytes (pure Verus, no external_body)
pub fn u32_to_le_bytes(x: u32) -> (bytes: [u8; 4])
    ensures
        bytes_to_nat_prefix(bytes@, 4) == x as nat,
{
    // Extract bytes using bit masking
    let masked0 = x & 0xff;
    let masked1 = (x >> 8) & 0xff;
    let masked2 = (x >> 16) & 0xff;
    let masked3 = (x >> 24) & 0xff;

    // Prove masked values fit in u8 (< 256)
    proof {
        assert(masked0 < 256) by (bit_vector)
            requires
                masked0 == x & 0xff,
        ;
        assert(masked1 < 256) by (bit_vector)
            requires
                masked1 == (x >> 8) & 0xff,
        ;
        assert(masked2 < 256) by (bit_vector)
            requires
                masked2 == (x >> 16) & 0xff,
        ;
        assert(masked3 < 256) by (bit_vector)
            requires
                masked3 == (x >> 24) & 0xff,
        ;
    }

    let b0 = masked0 as u8;
    let b1 = masked1 as u8;
    let b2 = masked2 as u8;
    let b3 = masked3 as u8;
    let bytes = [b0, b1, b2, b3];

    proof {
        lemma2_to64();
        reveal_with_fuel(bytes_to_nat_prefix, 5);

        // Prove byte decomposition equals x
        assert(b0 as u32 + b1 as u32 * 0x100 + b2 as u32 * 0x10000 + b3 as u32 * 0x1000000 == x)
            by (bit_vector)
            requires
                b0 == (x & 0xff) as u8,
                b1 == ((x >> 8) & 0xff) as u8,
                b2 == ((x >> 16) & 0xff) as u8,
                b3 == ((x >> 24) & 0xff) as u8,
        ;
    }
    bytes
}

/// Convert u64 to little-endian bytes (pure Verus, no external_body)
pub fn u64_to_le_bytes(x: u64) -> (bytes: [u8; 8])
    ensures
        bytes_to_nat_prefix(bytes@, 8) == x as nat,
{
    // Extract bytes using bit masking
    let masked0 = x & 0xff;
    let masked1 = (x >> 8) & 0xff;
    let masked2 = (x >> 16) & 0xff;
    let masked3 = (x >> 24) & 0xff;
    let masked4 = (x >> 32) & 0xff;
    let masked5 = (x >> 40) & 0xff;
    let masked6 = (x >> 48) & 0xff;
    let masked7 = (x >> 56) & 0xff;

    // Prove masked values fit in u8 (< 256)
    proof {
        assert(masked0 < 256) by (bit_vector)
            requires
                masked0 == x & 0xff,
        ;
        assert(masked1 < 256) by (bit_vector)
            requires
                masked1 == (x >> 8) & 0xff,
        ;
        assert(masked2 < 256) by (bit_vector)
            requires
                masked2 == (x >> 16) & 0xff,
        ;
        assert(masked3 < 256) by (bit_vector)
            requires
                masked3 == (x >> 24) & 0xff,
        ;
        assert(masked4 < 256) by (bit_vector)
            requires
                masked4 == (x >> 32) & 0xff,
        ;
        assert(masked5 < 256) by (bit_vector)
            requires
                masked5 == (x >> 40) & 0xff,
        ;
        assert(masked6 < 256) by (bit_vector)
            requires
                masked6 == (x >> 48) & 0xff,
        ;
        assert(masked7 < 256) by (bit_vector)
            requires
                masked7 == (x >> 56) & 0xff,
        ;
    }

    let b0 = masked0 as u8;
    let b1 = masked1 as u8;
    let b2 = masked2 as u8;
    let b3 = masked3 as u8;
    let b4 = masked4 as u8;
    let b5 = masked5 as u8;
    let b6 = masked6 as u8;
    let b7 = masked7 as u8;
    let bytes = [b0, b1, b2, b3, b4, b5, b6, b7];

    proof {
        lemma2_to64();
        reveal_with_fuel(bytes_to_nat_prefix, 9);

        // Prove byte decomposition equals x
        assert(b0 as u64 + b1 as u64 * 0x100u64 + b2 as u64 * 0x10000u64 + b3 as u64 * 0x1000000u64
            + b4 as u64 * 0x100000000u64 + b5 as u64 * 0x10000000000u64 + b6 as u64
            * 0x1000000000000u64 + b7 as u64 * 0x100000000000000u64 == x) by (bit_vector)
            requires
                b0 == (x & 0xff) as u8,
                b1 == ((x >> 8) & 0xff) as u8,
                b2 == ((x >> 16) & 0xff) as u8,
                b3 == ((x >> 24) & 0xff) as u8,
                b4 == ((x >> 32) & 0xff) as u8,
                b5 == ((x >> 40) & 0xff) as u8,
                b6 == ((x >> 48) & 0xff) as u8,
                b7 == ((x >> 56) & 0xff) as u8,
        ;
    }
    bytes
}

/// Convert u128 to little-endian bytes (pure Verus, no external_body)
pub fn u128_to_le_bytes(x: u128) -> (bytes: [u8; 16])
    ensures
        bytes_to_nat_prefix(bytes@, 16) == x as nat,
{
    // Extract bytes using bit masking
    let masked0 = x & 0xff;
    let masked1 = (x >> 8) & 0xff;
    let masked2 = (x >> 16) & 0xff;
    let masked3 = (x >> 24) & 0xff;
    let masked4 = (x >> 32) & 0xff;
    let masked5 = (x >> 40) & 0xff;
    let masked6 = (x >> 48) & 0xff;
    let masked7 = (x >> 56) & 0xff;
    let masked8 = (x >> 64) & 0xff;
    let masked9 = (x >> 72) & 0xff;
    let masked10 = (x >> 80) & 0xff;
    let masked11 = (x >> 88) & 0xff;
    let masked12 = (x >> 96) & 0xff;
    let masked13 = (x >> 104) & 0xff;
    let masked14 = (x >> 112) & 0xff;
    let masked15 = (x >> 120) & 0xff;

    // Prove masked values fit in u8 (< 256)
    proof {
        assert(masked0 < 256) by (bit_vector)
            requires
                masked0 == x & 0xff,
        ;
        assert(masked1 < 256) by (bit_vector)
            requires
                masked1 == (x >> 8) & 0xff,
        ;
        assert(masked2 < 256) by (bit_vector)
            requires
                masked2 == (x >> 16) & 0xff,
        ;
        assert(masked3 < 256) by (bit_vector)
            requires
                masked3 == (x >> 24) & 0xff,
        ;
        assert(masked4 < 256) by (bit_vector)
            requires
                masked4 == (x >> 32) & 0xff,
        ;
        assert(masked5 < 256) by (bit_vector)
            requires
                masked5 == (x >> 40) & 0xff,
        ;
        assert(masked6 < 256) by (bit_vector)
            requires
                masked6 == (x >> 48) & 0xff,
        ;
        assert(masked7 < 256) by (bit_vector)
            requires
                masked7 == (x >> 56) & 0xff,
        ;
        assert(masked8 < 256) by (bit_vector)
            requires
                masked8 == (x >> 64) & 0xff,
        ;
        assert(masked9 < 256) by (bit_vector)
            requires
                masked9 == (x >> 72) & 0xff,
        ;
        assert(masked10 < 256) by (bit_vector)
            requires
                masked10 == (x >> 80) & 0xff,
        ;
        assert(masked11 < 256) by (bit_vector)
            requires
                masked11 == (x >> 88) & 0xff,
        ;
        assert(masked12 < 256) by (bit_vector)
            requires
                masked12 == (x >> 96) & 0xff,
        ;
        assert(masked13 < 256) by (bit_vector)
            requires
                masked13 == (x >> 104) & 0xff,
        ;
        assert(masked14 < 256) by (bit_vector)
            requires
                masked14 == (x >> 112) & 0xff,
        ;
        assert(masked15 < 256) by (bit_vector)
            requires
                masked15 == (x >> 120) & 0xff,
        ;
    }

    let b0 = masked0 as u8;
    let b1 = masked1 as u8;
    let b2 = masked2 as u8;
    let b3 = masked3 as u8;
    let b4 = masked4 as u8;
    let b5 = masked5 as u8;
    let b6 = masked6 as u8;
    let b7 = masked7 as u8;
    let b8 = masked8 as u8;
    let b9 = masked9 as u8;
    let b10 = masked10 as u8;
    let b11 = masked11 as u8;
    let b12 = masked12 as u8;
    let b13 = masked13 as u8;
    let b14 = masked14 as u8;
    let b15 = masked15 as u8;
    let bytes = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15];

    proof {
        lemma2_to64();
        reveal_with_fuel(bytes_to_nat_prefix, 17);

        // Prove byte decomposition equals x
        assert(b0 as u128 + b1 as u128 * 0x100u128 + b2 as u128 * 0x10000u128 + b3 as u128
            * 0x1000000u128 + b4 as u128 * 0x100000000u128 + b5 as u128 * 0x10000000000u128
            + b6 as u128 * 0x1000000000000u128 + b7 as u128 * 0x100000000000000u128 + b8 as u128
            * 0x10000000000000000u128 + b9 as u128 * 0x1000000000000000000u128 + b10 as u128
            * 0x100000000000000000000u128 + b11 as u128 * 0x10000000000000000000000u128
            + b12 as u128 * 0x1000000000000000000000000u128 + b13 as u128
            * 0x100000000000000000000000000u128 + b14 as u128 * 0x10000000000000000000000000000u128
            + b15 as u128 * 0x1000000000000000000000000000000u128 == x) by (bit_vector)
            requires
                b0 == (x & 0xff) as u8,
                b1 == ((x >> 8) & 0xff) as u8,
                b2 == ((x >> 16) & 0xff) as u8,
                b3 == ((x >> 24) & 0xff) as u8,
                b4 == ((x >> 32) & 0xff) as u8,
                b5 == ((x >> 40) & 0xff) as u8,
                b6 == ((x >> 48) & 0xff) as u8,
                b7 == ((x >> 56) & 0xff) as u8,
                b8 == ((x >> 64) & 0xff) as u8,
                b9 == ((x >> 72) & 0xff) as u8,
                b10 == ((x >> 80) & 0xff) as u8,
                b11 == ((x >> 88) & 0xff) as u8,
                b12 == ((x >> 96) & 0xff) as u8,
                b13 == ((x >> 104) & 0xff) as u8,
                b14 == ((x >> 112) & 0xff) as u8,
                b15 == ((x >> 120) & 0xff) as u8,
        ;
    }
    bytes
}

} // verus!
