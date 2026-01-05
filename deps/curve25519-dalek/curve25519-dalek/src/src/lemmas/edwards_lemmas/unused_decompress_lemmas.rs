#![allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
use crate::lemmas::edwards_lemmas::step1_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// Extended Coordinate Lemmas
// =============================================================================
/// Lemma: When Z = 1 and T = X * Y, the extended coordinate invariant holds
///
/// For an EdwardsPoint (X:Y:Z:T), the invariant is T·Z = X·Y
/// When Z = 1, this simplifies to T = X·Y
pub proof fn lemma_extended_coord_when_z_is_one(x: nat, y: nat, t: nat)
    requires
        t == math_field_mul(x, y),
    ensures
        math_field_mul(t, 1) == math_field_mul(x, y),  // T·Z = X·Y when Z = 1
{
    // Goal: t * 1 ≡ x * y (mod p)
    // Strategy: t * 1 = t (since t < p), and t = x*y from precondition
    pow255_gt_19();

    assert(math_field_mul(t, 1) == t) by {
        // t < p (since t = (x*y) % p)
        assert(t < p()) by {
            lemma_mod_bound((x * y) as int, p() as int);
        };

        // t % p = t
        lemma_small_mod(t, p());
    };

    // Conclusion: t * 1 = t = x * y
}

// =============================================================================
// Composition Lemma for Full Decompress
// =============================================================================
/// Top-level lemma: Full correctness of decompress
///
/// After sqrt_ratio_i and conditional_negate, the result is on the curve.
pub proof fn lemma_decompress_correct(repr_bytes: &[u8; 32], y: nat, x_sqrt: nat, sign_bit: u8)
    requires
        y == spec_field_element_from_bytes(repr_bytes),
        sign_bit == (repr_bytes[31] >> 7),
        math_is_valid_y_coordinate(y),
        ({
            let d = spec_field_element(&EDWARDS_D);
            let y2 = math_field_square(y);
            let u = math_field_sub(y2, 1);
            let v = math_field_add(math_field_mul(d, y2), 1);
            v != 0 && math_field_mul(math_field_square(x_sqrt), v) == u % p()
        }),
    ensures
        math_on_edwards_curve(x_sqrt, y),
        math_on_edwards_curve(
            if sign_bit == 1 {
                math_field_neg(x_sqrt)
            } else {
                x_sqrt % p()
            },
            y,
        ),
{
    // Goal: (x, y) and (±x, y) are both on the curve
    //
    // Part 1: Show (x_sqrt, y) is on curve using x² · v = u
    // Part 2: Show negation/reduction preserves curve membership
    let p = p();
    p_gt_2();
    let d = spec_field_element(&EDWARDS_D);
    let y2 = math_field_square(y);
    let u = math_field_sub(y2, 1);

    // Part 1: (x_sqrt, y) is on curve
    assert(math_on_edwards_curve(x_sqrt, y)) by {
        // u < p (field sub returns reduced), so u % p = u
        assert(u < p) by {
            lemma_mod_bound((((y2 % p) + p) - (1nat % p)) as int, p as int);
        };
        lemma_small_mod(u, p);

        // Now lemma_sqrt_ratio_implies_on_curve applies
        lemma_sqrt_ratio_implies_on_curve(x_sqrt, y);
    };

    // Part 2: After sign adjustment, still on curve
    if sign_bit == 1 {
        // -x preserves curve: (-x)² = x²
        lemma_negation_preserves_curve(x_sqrt, y);
    } else {
        // x % p preserves curve membership
        // Need to show: on_curve(x % p, y) when on_curve(x, y)
        // Use squaring absorbs mod property
        lemma_square_mod_noop(x_sqrt);
        let x2 = math_field_square(x_sqrt);
        let x2_red = math_field_square(x_sqrt % p);
        assert(x2 == x2_red);
        // Since x² = (x % p)², all curve components are equal
        // Therefore on_curve(x % p, y) ⟺ on_curve(x, y)
    }
}

} // verus!
