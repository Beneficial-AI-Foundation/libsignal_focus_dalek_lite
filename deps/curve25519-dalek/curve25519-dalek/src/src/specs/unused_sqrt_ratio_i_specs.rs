#[allow(unused_imports)]
use super::core_specs::*;
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)]
use crate::constants;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;

use vstd::prelude::*;

verus! {

//=============================================================================
// Specs for sqrt_ratio_i algebraic correctness
//=============================================================================
/// Check if x is a 4th root of unity: x^4 ≡ 1 (mod p)
pub open spec fn is_fourth_root_of_unity(x: nat) -> bool {
    pow(x as int, 4nat) as nat % p() == 1
}

/// The four 4th roots of unity mod p are: 1, -1, i, -i
/// where i = sqrt(-1) = SQRT_M1
pub open spec fn fourth_root_of_unity_values() -> (nat, nat, nat, nat) {
    let one = 1nat;
    let neg_one = (p() - 1) as nat;
    let i = spec_sqrt_m1();
    let neg_i = ((p() - spec_sqrt_m1()) as int % p() as int) as nat;
    (one, neg_one, i, neg_i)
}

/// Check if x is one of the four 4th roots of unity
pub open spec fn is_one_of_fourth_roots(x: nat) -> bool {
    let (one, neg_one, i, neg_i) = fourth_root_of_unity_values();
    x % p() == one || x % p() == neg_one || x % p() == i || x % p() == neg_i
}

/// The exponent (p-5)/8 used in sqrt_ratio_i
pub open spec fn sqrt_ratio_exponent() -> nat {
    ((p() - 5) / 8) as nat
}

/// Spec: v*r² is u times a 4th root of unity
/// This is the key algebraic property that makes sqrt_ratio_i work
pub open spec fn check_equals_u_times_fourth_root(check: nat, u: nat) -> bool {
    let (one, neg_one, i, neg_i) = fourth_root_of_unity_values();
    check % p() == (u * one) % p()  // check = u
     || check % p() == (u * neg_one) % p()  // check = -u
     || check % p() == (u * i) % p()  // check = u*i
     || check % p() == (u * neg_i) % p()  // check = -u*i

}

} // verus!
