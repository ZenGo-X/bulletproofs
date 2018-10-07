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
use cryptography_utils::cryptographic_primitives::hashing::hash_sha512::HSha512;
use cryptography_utils::cryptographic_primitives::hashing::hash_sha256::HSha256;
use std::ops::Shr;
use itertools::Itertools;
use proofs::inner_product::InnerProductArg;

pub struct RangeProof {
    A: GE,
    S: GE,
    T1: GE,
    T2: GE,
    tau_x: FE,
    miu: FE,
    tx: FE,
    inner_product_proof:InnerProductArg
}

impl RangeProof{

    pub fn prove(G: &GE, H: &GE, secret: &FE, blinding: &FE, bit_length: usize) -> RangeProof{
        let alpha : FE = ECScalar::new_random();
        let rho : FE = ECScalar::new_random();
        let KZen: &[u8] = &[75,90,101,110];
        let kzen_label = BigInt::from(KZen);

        let g_vec = (0..bit_length).map(|i| {
            let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
            let hash_i = HSha512::create_hash(&[&kzen_label_i]);
            generate_random_point(&Converter::to_vec(&hash_i))
        }).collect::<Vec<GE>>();

        // can run in parallel to g_vec:
        let h_vec = (0..bit_length).map(|i| {
            let kzen_label_j = BigInt::from(bit_length as u32) +  BigInt::from(i as u32) + &kzen_label;
            let hash_j = HSha512::create_hash(&[&kzen_label_j]);
            generate_random_point(&Converter::to_vec(&hash_j))
        }).collect::<Vec<GE>>();

        let mut A = H.clone() * &alpha;
        let mut S = H.clone() * &rho;
        let secret_bn = secret.to_big_int();
        let two = BigInt::from(2);
        let one = BigInt::from(1);
        let order = alpha.q();
        let aL = (0..bit_length).map(|i| {
            secret_bn.clone().shr(i).modulus(&two)
        }).collect::<Vec<BigInt>>();

        let aR = (0..bit_length).map(|i| {
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

        let SR = (0..bit_length).map(|_| ECScalar::new_random())
            .collect::<Vec<FE>>();
        let SL = (0..bit_length).map(|_| ECScalar::new_random())
            .collect::<Vec<FE>>();

        S = SL.iter().zip(&SR).fold(S, |acc, x| {
            let g_vec_i : GE = g_vec[index].clone();
            let h_vec_i: GE = h_vec[index].clone();
            index = index + 1;
            let g_vec_i_SLi = g_vec_i * x.0;
            let h_vec_i_SRi = h_vec_i * x.1;
            let SRhi_plus_SLgi = h_vec_i_SRi + g_vec_i_SLi;
            acc + SRhi_plus_SLgi});

        let y = HSha256::create_hash_from_ge(&[&A,&S]);
        let base_point: GE = ECPoint::generator();
        let yG : GE = base_point * &y;
        let z = HSha256::create_hash_from_ge(&[&yG]);

        let z_squared = BigInt::mod_pow(&z.to_big_int(), &BigInt::from(2), &order);
        let z_cubed = BigInt::mod_pow(&z.to_big_int(), &BigInt::from(3), &order);
        let t0 = BigInt::mod_mul(&z_squared, &secret_bn, &order);

        let yi = (0..bit_length).map(|i| BigInt::mod_pow(&y.to_big_int(), &BigInt::from(i as u32), &order))
            .collect::<Vec<BigInt>>();

        let t2 = (0..bit_length).map(|i|{
            let t2_1 = BigInt::mod_mul(&SR[i].to_big_int(),&yi[i],&order);
            let t2_2 = BigInt::mod_mul(&t2_1,&SL[i].to_big_int(), &order);
            t2_2
        }).fold(BigInt::zero(),|acc,x| acc + x);

        let t0 = (0..bit_length).map(|i|{
            let t0_1 = BigInt::mod_mul(&z.to_big_int(),&yi[i], &order);
            let t0_2 = BigInt::mod_mul(&z_squared,&yi[i], &order);
            let two_to_the_i = BigInt::mod_pow(&two, &BigInt::from(i as u32), &order);
            let t0_3 = BigInt::mod_mul(&z_cubed,&two_to_the_i, &order);
            let t0_12 = BigInt::mod_sub(&t0_1, &t0_2, &order);
            BigInt::mod_sub(&t0_12,&t0_3,&order)
        }).fold(t0,|acc,x| acc + x);

        let t1 = (0..bit_length).map(|i|{
            let t1_1 = BigInt::mod_add(&aR[i],&z.to_big_int(),&order);
            let t1_2 = BigInt::mod_mul(&t1_1,&yi[i], &order);
            let t1_3 = BigInt::mod_add(&SL[i].to_big_int(),&t1_2,&order);
            let t1_4 = BigInt::mod_mul(&aL[i],&z.to_big_int(), &order);
            let t1_5 = BigInt::mod_add(&SR[i].to_big_int(),&yi[i],&order);
            let t1_6 = BigInt::mod_mul(&t1_4,&t1_5, &order);
            let two_to_the_i = BigInt::mod_pow(&two, &BigInt::from(i as u32), &order);
            let t1_7 = BigInt::mod_add(&z_squared,&two_to_the_i,&order);
            let t1_8 = BigInt::mod_mul(&t1_7,&SL[i].to_big_int(), &order);
            let t1_68 = BigInt::mod_add(&t1_6,&t1_8, &order);
            BigInt::mod_add(&t1_3, &t1_68, &order)
        }).fold(BigInt::zero(),|acc,x| acc + x);

        let tau1: FE = ECScalar::new_random();
        let tau2: FE = ECScalar::new_random();
        let t1_fe = ECScalar::from(&t1);
        let t2_fe = ECScalar::from(&t2);
        let T1 = (G.clone() * &t1_fe) + (H.clone() * &tau1);
        let T2 = (G.clone() * &t2_fe) + (H.clone() * &tau2);

        let fs_challenge = HSha256::create_hash_from_ge(&[&T1,&T2, G,H]);
        let fs_challenge_square = fs_challenge.mul(&fs_challenge.get_element());
        let taux_1 = fs_challenge.mul(&tau1.get_element());
        let taux_2 = fs_challenge_square.mul(&tau2.get_element());
        let z_squared_fe: FE = ECScalar::from(&z_squared);
        let taux_3 = z_squared_fe.mul(&blinding.get_element());
        let tau_x = taux_1.add(&taux_2.get_element()).add(&taux_3.get_element());
        let miu = (rho.mul(&fs_challenge.get_element())).add(&alpha.get_element());

        let Lp = (0..bit_length).map(|i| {
            let Lp_1 =  (SL[i].mul(&fs_challenge.get_element())).to_big_int();
            let Lp_2 = BigInt::mod_sub(&aL[i],&z.to_big_int(), &order);
            BigInt::mod_add(&Lp_1, &Lp_2, &order)
        }).collect::<Vec<BigInt>>();

        let Rp = (0..bit_length).map(|i| {
            let Rp_1 =  (SR[i].mul(&fs_challenge.get_element())).to_big_int();
            let two_to_the_i = BigInt::mod_pow(&two, &BigInt::from(i as u32), &order);
            let Rp_2 = BigInt::mod_mul(&z_squared, &two_to_the_i, &order);
            let Rp_3 = BigInt::mod_add(&BigInt::mod_add(&z.to_big_int(),&aR[i], &order),&Rp_1, &order);
            let Rp_4 = BigInt::mod_mul(&yi[i],&Rp_3, &order);
            BigInt::mod_add(&Rp_4, &Rp_2, &order)
        }).collect::<Vec<BigInt>>();
        let tx = Lp.iter().zip(&Rp).fold(BigInt::zero(),|acc, x|{
            let Lp_iRp_i = BigInt::mod_mul(x.0,x.1, &order);
            acc + Lp_iRp_i
        });
        let tx_fe: FE = ECScalar::from(&tx);
        let challenge_x = HSha256::create_hash(&[&tau_x.to_big_int(),&miu.to_big_int(), &tx]);
        let challenge_x: FE = ECScalar::from(&challenge_x);
        let Gx = G.clone() * &challenge_x;
        // P' = u^{xc}
        let P = Gx.clone() * &tx_fe;

        let yi_inv = (0..bit_length).map(|i| {
            yi[i].invert(&order).unwrap()
        }).collect::<Vec<BigInt>>();

        let hi_tag = (0..bit_length).map(|i| {
            h_vec[i].clone() * &ECScalar::from(&yi_inv[i])
        }).collect::<Vec<GE>>();

        // P' = P' g^l
        let P = g_vec.iter().zip(&Lp).fold(P,|acc, x|{
            let g_vec_i_lp_i = x.0.clone() * &ECScalar::from(x.1);
            acc + g_vec_i_lp_i
        });
        // P' = P' h'^r
        let P = hi_tag.iter().zip(&Rp).fold(P,|acc, x|{
            let h_vec_i_rp_i = x.0.clone() * &ECScalar::from(x.1);
            acc + h_vec_i_rp_i
        });
        // line 9
        // public input : g,h,u^x,P' = g_vec, hi_tag, Gx,P
        // private input: a,b  = Lp,Rp
        let mut L_vec = Vec::with_capacity(bit_length);
        let mut R_vec = Vec::with_capacity(bit_length);
         let inner_product_proof = InnerProductArg::prove( g_vec, hi_tag,Gx, P, Lp,Rp, L_vec, R_vec);

        return RangeProof{
            A,
            S,
            T1,
            T2,
            tau_x,
            miu,
            tx: tx_fe,
            inner_product_proof,
        };

    }
}

pub fn generate_random_point( bytes: &[u8]) -> GE{

    let result: Result<GE,_> = ECPoint::from_bytes(&bytes);
    if result.is_ok(){ return result.unwrap()}
    else {
        let two = BigInt::from(2);
        let temp : FE = ECScalar::new_random();
        let bn = BigInt::from(bytes);
        let bn_times_two = BigInt::mod_mul(&bn,&two, &temp.q());
        let bytes = BigInt::to_vec(&bn_times_two);
        return generate_random_point(&bytes);
    }



}