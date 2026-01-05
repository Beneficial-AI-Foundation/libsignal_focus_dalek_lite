//! Unused lemmas from field_algebra_lemmas.rs
//!
//! These lemmas were moved here during cleanup. They may be useful for future proofs.
#![allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

/// Lemma: (-u) · inv(u) = -1
///
/// Mathematical reasoning:
///   (-u) · inv(u) = -1 · u · inv(u) = -1 · 1 = -1
///
/// Used in: (currently unused, kept for reference)
pub proof fn lemma_neg_times_inv_is_neg_one(u: nat)
    requires
        u % p() != 0,
    ensures
        math_field_mul(math_field_neg(u), math_field_inv(u)) == math_field_neg(1),
{
    let p = p();
    p_gt_2();

    let neg_u = math_field_neg(u);
    let inv_u = math_field_inv(u);
    let u_mod = u % p;

    field_inv_property(u);
    assert(inv_u < p);
    assert((u_mod * inv_u) % p == 1);

    // neg_u = (p - u_mod) % p if u_mod != 0, else 0
    lemma_mod_bound(u as int, p as int);

    if u_mod == 0 {
        // This contradicts u % p != 0
        assert(false);
    }
    // neg_u = (p - u_mod) % p = p - u_mod (since 0 < u_mod < p)

    assert(neg_u == (p - u_mod) as nat) by {
        lemma_small_mod((p - u_mod) as nat, p);
    };

    // Goal: show (neg_u * inv_u) % p = (p - 1) % p = math_field_neg(1)
    // neg_u * inv_u = (p - u_mod) * inv_u = p * inv_u - u_mod * inv_u

    // Step 1: (p * inv_u) % p = 0
    assert((p * inv_u) % p == 0) by {
        lemma_mod_multiples_basic(inv_u as int, p as int);
    };

    // Step 2: (u_mod * inv_u) % p = 1
    assert((u_mod * inv_u) % p == 1);

    // Step 3: ((p - u_mod) * inv_u) = p*inv_u - u_mod*inv_u
    let neg_u_times_inv = neg_u * inv_u;
    assert(neg_u_times_inv == (p * inv_u) - (u_mod * inv_u)) by {
        assert(neg_u == (p - u_mod) as nat);
        lemma_mul_is_distributive_sub(inv_u as int, p as int, u_mod as int);
        lemma_mul_is_commutative((p - u_mod) as int, inv_u as int);
    };

    // Step 4: (p*inv_u - u_mod*inv_u) % p = (0 - 1) % p = -1 % p = p - 1
    assert(neg_u_times_inv % p == (p - 1) as nat) by {
        lemma_sub_mod_noop((p * inv_u) as int, (u_mod * inv_u) as int, p as int);
        // ((p*inv_u) % p - (u_mod*inv_u) % p) % p = (p*inv_u - u_mod*inv_u) % p
        // (0 - 1) % p = neg_u_times_inv % p

        // (0 - 1) % p = (-1) % p = (p - 1) % p = p - 1
        assert((0int - 1int) % (p as int) == (p - 1) as int) by {
            lemma_mod_sub_multiples_vanish(-1int, p as int);
            // Actually: (-1) % p = (p - 1) for Euclidean mod
            // Using: a % m = (a + m) % m when a is negative
            assert((-1int + p as int) % (p as int) == (-1int) % (p as int)) by {
                lemma_mod_add_multiples_vanish(-1int, p as int);
            };
            assert((p - 1) as int % (p as int) == (p - 1) as int) by {
                lemma_small_mod((p - 1) as nat, p);
            };
        };
    };

    // Step 5: math_field_mul(neg_u, inv_u) = neg_u_times_inv % p = p - 1
    //         math_field_neg(1) = (p - 1 % p) % p = (p - 1) % p = p - 1
    assert(math_field_neg(1) == (p - 1) as nat) by {
        lemma_small_mod(1nat, p);
        lemma_small_mod((p - 1) as nat, p);
    };
}

} // verus!
