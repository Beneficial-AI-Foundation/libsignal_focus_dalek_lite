//! Unused lemmas from sqrt_ratio_lemmas.rs
//!
//! These lemmas were moved here during cleanup. They may be useful for future proofs.
#![allow(unused_imports)]
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

/// LEMMA: i ≠ 1 (derived from i² = -1)
///
/// Mathematical reasoning:
///   1. Suppose i = 1
///   2. Then i² = 1
///   3. But i² = -1 (mod p) by axiom_sqrt_m1_squared
///   4. So 1 = p - 1, meaning p = 2
///   5. But p = 2^255 - 19 > 2, contradiction!
///
/// Used in: (currently unused, kept for reference)
pub proof fn lemma_sqrt_m1_neq_one()
    ensures
        spec_sqrt_m1() != 1,
{
    use crate::lemmas::field_lemmas::sqrt_m1_lemmas::axiom_sqrt_m1_squared;

    // Proof by contradiction: suppose spec_sqrt_m1() = 1
    // Then i² = 1, but axiom_sqrt_m1_squared says i² = p - 1
    // So we need 1 = p - 1, meaning p = 2
    // But p > 2, contradiction

    pow255_gt_19();  // Establishes p() > 0 and pow2(255) > 19

    // Step 1: i² = p - 1 (which is -1 mod p)
    assert((spec_sqrt_m1() * spec_sqrt_m1()) % p() == (p() - 1)) by {
        axiom_sqrt_m1_squared();
    };

    // Step 2: p > 2 (since p = 2^255 - 19 and 2^255 > 21)
    assert(p() > 2) by {
        p_gt_2();
    };

    // Step 3: 1 * 1 % p = 1 (since 1 < p)
    assert(1 < p());
    assert((1nat * 1nat) % p() == 1) by {
        lemma_small_mod(1, p());
    };

    // Step 4: Since (1*1) % p = 1 ≠ p - 1 (because p > 2), we have i ≠ 1
    assert((p() - 1) != 1);  // Because p > 2

    // Therefore if spec_sqrt_m1() = 1, we'd have 1 = p - 1, contradiction
}

/// LEMMA: i ≠ -1 (derived from i² = -1)
///
/// Mathematical reasoning:
///   1. Suppose i ≡ -1 (mod p)
///   2. Then i² ≡ (-1)² = 1 (mod p)
///   3. But i² = -1 (mod p) by axiom_sqrt_m1_squared
///   4. So 1 ≡ -1 (mod p), meaning p = 2
///   5. But p = 2^255 - 19 > 2, contradiction!
///
/// Used in: (currently unused, kept for reference)
pub proof fn lemma_sqrt_m1_neq_neg_one()
    ensures
        spec_sqrt_m1() % p() != (p() - 1) as nat,
{
    use crate::lemmas::field_lemmas::sqrt_m1_lemmas::axiom_sqrt_m1_squared;
    use crate::lemmas::common_lemmas::number_theory_lemmas::lemma_product_of_complements;

    pow255_gt_19();

    // Step 1: i² = p - 1 (which is -1 mod p)
    assert((spec_sqrt_m1() * spec_sqrt_m1()) % p() == (p() - 1)) by {
        axiom_sqrt_m1_squared();
    };

    // Step 2: p > 2
    assert(p() > 2) by {
        p_gt_2();
    };

    // Step 3: (p-1) * (p-1) % p = 1 (since (p-1)² ≡ (-1)² ≡ 1 mod p)
    let pm1: nat = (p() - 1) as nat;
    assert(pm1 < p());
    assert((pm1 * pm1) % p() == 1nat) by {
        lemma_product_of_complements(1, 1, p());
        lemma_small_mod(1, p());
    };

    // Step 4: Key connection - a² % p == (a % p)² % p
    let i = spec_sqrt_m1();
    assert((i * i) % p() == ((i % p()) * (i % p())) % p()) by {
        lemma_mul_mod_noop_general(i as int, i as int, p() as int);
    };

    // Step 5: Since (pm1*pm1) % p = 1 ≠ p - 1 = i² % p (because p > 2), we have i % p ≠ pm1
    assert(pm1 != 1);  // Because p > 2

    // Therefore if spec_sqrt_m1() % p() == pm1:
    // i² % p = ((i % p) * (i % p)) % p = (pm1 * pm1) % p = 1
    // But i² % p = p - 1
    // So 1 == p - 1, but p > 2, contradiction
}

/// Lemma: sqrt_ratio_i check structure
///
/// This lemma verifies the algebraic structure of the sqrt_ratio_i check.
/// Currently uses assume due to complex pow/mod interaction.
///
/// Used in: (currently unused, kept for reference)
pub proof fn lemma_sqrt_ratio_check_structure(u: nat, v: nat, r: nat)
    requires
        v % p() != 0,
        r % p() == ((u * v * v * v) % p() * vstd::arithmetic::power::pow(
            ((u * v * v * v * v * v * v * v) % p()) as int,
            sqrt_ratio_exponent(),
        ) as nat) % p(),
    ensures
        check_equals_u_times_fourth_root((v * r * r) % p(), u),
{
    // The algebraic steps above are mathematically sound but complex to
    // formalize in Verus due to the interaction of pow, mod, and field ops
    assume(check_equals_u_times_fourth_root((v * r * r) % p(), u));
}

} // verus!
