/*

Copyright 2018 by Kzen Networks

This file is part of escrow-recovery library
(https://github.com/KZen-networks/cryptography-utils)

bulletproof is free software: you can redistribute
it and/or modify it under the terms of the GNU General Public
License as published by the Free Software Foundation, either
version 3 of the License, or (at your option) any later version.

@license GPL-3.0+ <https://github.com/KZen-networks/bulletproof-utils/blob/master/LICENSE>
*/

// based on the paper: https://eprint.iacr.org/2017/1066.pdf
use cryptography_utils::BigInt;
use cryptography_utils::arithmetic::traits::{Converter,Modulo};
use cryptography_utils::{GE,FE};
use cryptography_utils::elliptic::curves::traits::*;
use cryptography_utils::cryptographic_primitives::hashing::traits::*;
use cryptography_utils::cryptographic_primitives::hashing::hash_sha256::HSha256;
use std::ops::Shr;

pub struct RangeProof {

}

impl RangeProof{

    pub fn prove(G: &GE, H: &GE, secret: &FE, blinding: &FE, bit_length: usize) -> RangeProof{
        let alpha : FE = ECScalar::new_random();
        let rho : FE = ECScalar::new_random();
        let KZen: &[u8] = &[75,90,101,110];
        let kzen_label = BigInt::from(KZen);

        let g_vec = (0..bit_length).map(|i| {
            let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
            let hash_i = HSha256::create_hash(&[&kzen_label_i]);
            ECPoint::from(&Converter::to_vec(&hash_i))
        }).collect::<Vec<GE>>();

        // can run in parallel to g_vec:
        let h_vec = (0..bit_length).map(|i| {
            let kzen_label_j = BigInt::from(bit_length as u32) +  BigInt::from(i as u32) + &kzen_label;
            let hash_j = HSha256::create_hash(&[&kzen_label_j]);
              ECPoint::from(&Converter::to_vec(&hash_j))
        }).collect::<Vec<GE>>();

        let mut A = H.clone() * &alpha;
        let S = H.clone() * rho;
        let secret_bn = secret.to_big_int();
        let two = BigInt::from(2);
        let one = BigInt::from(1);
        let order = alpha.q();
        let aL = (0..order.bit_length()).map(|i| {
            secret_bn.clone().shr(i).modulus(&two)
        }).collect::<Vec<BigInt>>();

        let aR = (0..order.bit_length()).map(|i| {
            BigInt::mod_sub(&aL[i],&one,&order)
        }).collect::<Vec<BigInt>>();
        let mut index:usize = 0;
        A = aL.iter().zip(&aR).fold(A, |acc, x| {
            let aLi_fe: FE = ECScalar::from(&x.0);
            let aRi_fe: FE = ECScalar::from(&x.1);
            let g_vec_i : GE = g_vec[index].clone();
            let h_vec_i: GE = h_vec[index].clone();
            index = index + 1;
            let g_vec_i_aLi = g_vec_i * aLi_fe;
            let h_vec_i_aRi = h_vec_i * aRi_fe;
            let aRhi_plus_aLgi = h_vec_i_aRi + g_vec_i_aLi;
            acc + aRhi_plus_aLgi});

        return RangeProof{};

    }
}