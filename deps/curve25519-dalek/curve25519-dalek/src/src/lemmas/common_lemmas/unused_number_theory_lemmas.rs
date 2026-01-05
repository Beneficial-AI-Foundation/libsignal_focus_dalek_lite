#![allow(unused_imports)]
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

//=============================================================================
// Properties of p = 2^255 - 19
//=============================================================================
/// Proves that p ≡ 5 (mod 8)
///
/// Mathematical reasoning:
/// 1. p = 2^255 - 19
/// 2. 2^255 = 2^3 · 2^252 = 8 · 2^252, so 2^255 ≡ 0 (mod 8)
/// 3. 19 ≡ 3 (mod 8)
/// 4. p ≡ 0 - 3 ≡ -3 ≡ 5 (mod 8)
///
/// Used in: field.rs (sqrt_ratio_i verification)
pub proof fn lemma_p_mod_8_eq_5()
    ensures
        p() % 8 == 5,
{
    // Step 1: 2^3 = 8
    assert(pow2(3) == 8) by {
        lemma2_to64();
    }

    // Step 2: 2^255 = 2^3 · 2^252
    assert(pow2(255) == pow2(3) * pow2(252)) by {
        lemma_pow2_adds(3, 252);
    }

    // Step 3: 2^255 ≡ 0 (mod 8) since 2^255 = 8 · 2^252
    assert(pow2(255) % 8 == 0) by {
        lemma_mul_mod_noop_left(pow2(3) as int, pow2(252) as int, 8int);
    }

    // Step 4: p = 2^255 - 19 ≡ 0 - 3 ≡ -3 ≡ 5 (mod 8)
    assert((pow2(255) as int - 19) % 8 == 5) by {
        assert(19int % 8 == 3) by (compute);
        lemma_sub_mod_noop(pow2(255) as int, 19int, 8int);
        assert((-3int) % 8 == 5) by (compute);
    }

    assert(pow2(255) > 19) by {
        pow255_gt_19();
    }
}

/// Proof that p() is odd (p() % 2 == 1)
///
/// Since p() = 2^255 - 19:
/// - 2^255 is even (by lemma_pow2_even)
/// - 19 is odd (19 % 2 == 1)
/// - even - odd = odd
pub proof fn lemma_p_is_odd()
    ensures
        p() % 2 == 1,
{
    // 2^255 is even
    assert(pow2(255) % 2 == 0) by {
        lemma_pow2_even(255);
    }

    // p = 2^255 - 19 ≡ 0 - 1 ≡ -1 ≡ 1 (mod 2)
    assert((pow2(255) as int - 19) % 2 == 1) by {
        assert(19int % 2 == 1) by (compute);
        lemma_sub_mod_noop(pow2(255) as int, 19int, 2int);
        assert((-1int) % 2 == 1) by (compute);
    }

    assert(pow2(255) > 19) by {
        pow255_gt_19();
    }
}

} // verus!
