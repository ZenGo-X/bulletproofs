/*

Copyright 2018 by Kzen Networks

This file is part of bulletproof library
(https://github.com/KZen-networks/bulletproof)

bulletproof is free software: you can redistribute
it and/or modify it under the terms of the GNU General Public
License as published by the Free Software Foundation, either
version 3 of the License, or (at your option) any later version.

@license GPL-3.0+ <https://github.com/KZen-networks/bulletproof/blob/master/LICENSE>
*/

// based on the paper: https://eprint.iacr.org/2017/1066.pdf
#[macro_use]
extern crate serde_derive;
extern crate serde;

extern crate curv;
extern crate itertools;

pub mod proofs;

#[derive(Copy, PartialEq, Eq, Clone, Debug)]
pub enum Errors {
    InnerProductError,
    WeightedInnerProdError,
    RangeProofError,
}

#[cfg(test)]
#[macro_export]
macro_rules! test_for_all_curves {
    (#[should_panic] $fn: ident) => {
        crate::test_for_all_curves!([#[should_panic]] $fn);
    };
    ($fn: ident) => {
        crate::test_for_all_curves!([] $fn);
    };
    ([$($attrs:tt)*] $fn: ident) => {
        paste::paste!{
            #[test]
            $($attrs)*
            fn [<$fn _secp256k1>]() {
                $fn::<curv::elliptic::curves::secp256_k1::GE>()
            }
            #[test]
            $($attrs)*
            fn [<$fn _ristretto>]() {
                $fn::<curv::elliptic::curves::curve_ristretto::GE>()
            }
            #[test]
            $($attrs)*
            fn [<$fn _ed25519>]() {
                $fn::<curv::elliptic::curves::ed25519::GE>()
            }
            #[test]
            $($attrs)*
            fn [<$fn _bls12_381>]() {
                $fn::<curv::elliptic::curves::bls12_381::GE>()
            }
            #[test]
            $($attrs)*
            fn [<$fn _p256>]() {
                $fn::<curv::elliptic::curves::p256::GE>()
            }
        }
    };
}
