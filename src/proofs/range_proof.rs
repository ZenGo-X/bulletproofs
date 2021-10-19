#![allow(non_snake_case)]

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

use curv::arithmetic::traits::*;
use curv::cryptographic_primitives::hashing::{Digest, DigestExt};
use curv::elliptic::curves::{secp256_k1::Secp256k1, Curve, ECPoint, Point, Scalar};
use curv::BigInt;
use sha2::Sha256;

use generic_array::{typenum::Unsigned, GenericArray};
use itertools::iterate;
use proofs::inner_product::InnerProductArg;
use std::ops::{Shl, Shr};
use Errors::{self, RangeProofError};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RangeProof {
    A: Point<Secp256k1>,
    S: Point<Secp256k1>,
    T1: Point<Secp256k1>,
    T2: Point<Secp256k1>,
    tau_x: Scalar<Secp256k1>,
    miu: Scalar<Secp256k1>,
    tx: Scalar<Secp256k1>,
    inner_product_proof: InnerProductArg,
}

impl RangeProof {
    pub fn prove(
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        G: &Point<Secp256k1>,
        H: &Point<Secp256k1>,
        mut secret: Vec<Scalar<Secp256k1>>,
        blinding: &[Scalar<Secp256k1>],
        bit_length: usize,
    ) -> RangeProof {
        let num_of_proofs = secret.len();
        //num of proofs times bit length
        let nm = num_of_proofs * bit_length;
        let alpha = Scalar::<Secp256k1>::random();
        let rho = Scalar::<Secp256k1>::random();

        let g_vec = g_vec.to_vec();
        let h_vec = h_vec.to_vec();

        let mut A = H * &alpha;
        let mut S = H * &rho;
        let two = BigInt::from(2);
        let one = BigInt::from(1);
        let order = Scalar::<Secp256k1>::group_order();

        //concat all secrets:
        secret.reverse();
        let secret_agg = secret
            .iter()
            .fold(BigInt::zero(), |acc, x| acc.shl(bit_length) + x.to_bigint());

        let aL = (0..nm)
            .map(|i| {
                let shr_secret = secret_agg.clone().shr(i);
                shr_secret.modulus(&two)
            })
            .collect::<Vec<BigInt>>();
        let aR = (0..nm)
            .map(|i| BigInt::mod_sub(&aL[i], &one, order))
            .collect::<Vec<BigInt>>();

        let secret_bits = (0..nm)
            .map(|i| {
                let bignum_bit: BigInt = aL[i].clone() & BigInt::one();
                let byte = BigInt::to_bytes(&bignum_bit);
                byte[0] == 1
            })
            .collect::<Vec<bool>>();
        let mut index: usize = 0;
        A = g_vec.iter().zip(secret_bits.clone()).fold(
            A,
            |acc, x| {
                if x.1 {
                    acc + x.0
                } else {
                    acc
                }
            },
        );

        A = h_vec
            .iter()
            .zip(secret_bits)
            .fold(A, |acc, x| if !x.1 { acc - x.0 } else { acc });

        let SR = (0..nm)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();
        let SL = (0..nm)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        S = SL.iter().zip(&SR).fold(S, |acc, x| {
            let g_vec_i_SLi = &g_vec[index] * x.0;
            let h_vec_i_SRi = &h_vec[index] * x.1;
            index += 1;
            let SRhi_plus_SLgi = h_vec_i_SRi + g_vec_i_SLi;
            acc + SRhi_plus_SLgi
        });

        let y = Sha256::new().chain_points([&A, &S]).result_scalar();
        let base_point = Point::<Secp256k1>::generator();
        let yG: Point<Secp256k1> = base_point * &y;
        let z: Scalar<Secp256k1> = Sha256::new().chain_points([&yG]).result_scalar();
        let z_bn = z.to_bigint();

        let one_fe = Scalar::<Secp256k1>::from(&one);
        let yi = iterate(one_fe.clone(), |i| i.clone() * &y)
            .take(nm)
            .collect::<Vec<Scalar<Secp256k1>>>();

        let t2 = (0..nm)
            .map(|i| SR[i].clone() * &yi[i] * &SL[i])
            .fold(Scalar::<Secp256k1>::zero(), |acc, x| acc + x);
        let t2 = t2.to_bigint();

        let two_fe = Scalar::<Secp256k1>::from(&two);
        let vec_2n = iterate(one_fe, |i| i.clone() * &two_fe)
            .take(bit_length)
            .collect::<Vec<Scalar<Secp256k1>>>();

        let t1 = (0..nm)
            .map(|i| {
                let t1_1 = BigInt::mod_add(&aR[i], &z_bn, order);
                let t1_2 = BigInt::mod_mul(&t1_1, &yi[i].to_bigint(), order);
                let t1_3 = BigInt::mod_mul(&SL[i].to_bigint(), &t1_2, order);
                let t1_4 = BigInt::mod_sub(&aL[i], &z_bn, order);
                let t1_5 = BigInt::mod_mul(&SR[i].to_bigint(), &yi[i].to_bigint(), order);
                let t1_6 = BigInt::mod_mul(&t1_4, &t1_5, order);
                let j = i / bit_length + 2;
                let k = i % bit_length;
                let z_index = BigInt::mod_pow(&z_bn, &BigInt::from(j as u32), order);
                let two_to_the_i = vec_2n[k].clone().to_bigint();
                let t1_7 = BigInt::mod_mul(&z_index, &two_to_the_i, order);
                let t1_8 = BigInt::mod_mul(&t1_7, &SL[i].to_bigint(), order);
                let t1_68 = BigInt::mod_add(&t1_6, &t1_8, order);
                BigInt::mod_add(&t1_3, &t1_68, order)
            })
            .fold(BigInt::zero(), |acc, x| BigInt::mod_add(&acc, &x, order));

        let tau1 = Scalar::<Secp256k1>::random();
        let tau2 = Scalar::<Secp256k1>::random();
        let t1_fe = Scalar::<Secp256k1>::from(&t1);
        let t2_fe = Scalar::<Secp256k1>::from(&t2);
        let T1 = G * &t1_fe + H * &tau1;
        let T2 = G * &t2_fe + H * &tau2;

        let fs_challenge = Sha256::new().chain_points([&T1, &T2, G, H]).result_scalar();
        let fs_challenge_square = &fs_challenge * &fs_challenge;
        let taux_1 = &fs_challenge * &tau1;
        let taux_2 = fs_challenge_square * &tau2;
        let taux_3 = (0..num_of_proofs)
            .map(|i| {
                let j = BigInt::mod_add(&two, &BigInt::from(i as u32), order);
                let z_j = BigInt::mod_pow(&z_bn, &j, order);
                let z_j_fe = Scalar::<Secp256k1>::from(&z_j);
                z_j_fe * &blinding[i]
            })
            .fold(taux_2, |acc, x| acc + &x);
        let tau_x = taux_1 + &taux_3;
        let miu = (rho * &fs_challenge) + &alpha;

        let Lp = (0..nm)
            .map(|i| {
                let Lp_1 = (&SL[i] * &fs_challenge).to_bigint();
                let Lp_2 = BigInt::mod_sub(&aL[i], &z_bn, order);
                BigInt::mod_add(&Lp_1, &Lp_2, order)
            })
            .collect::<Vec<BigInt>>();

        let Rp = (0..nm)
            .map(|i| {
                let Rp_1 = (&SR[i] * &fs_challenge).to_bigint();

                let j = i / bit_length + 2;
                let k = i % bit_length;
                let z_index = BigInt::mod_pow(&z_bn, &BigInt::from(j as u32), order);
                let two_to_the_i = vec_2n[k].clone().to_bigint();
                let Rp_2 = BigInt::mod_mul(&z_index, &two_to_the_i, order);
                let Rp_3 = BigInt::mod_add(&BigInt::mod_add(&z_bn, &aR[i], order), &Rp_1, order);
                let Rp_4 = BigInt::mod_mul(&yi[i].to_bigint(), &Rp_3, order);
                BigInt::mod_add(&Rp_4, &Rp_2, order)
            })
            .collect::<Vec<BigInt>>();
        let tx = Lp.iter().zip(&Rp).fold(BigInt::zero(), |acc, x| {
            let Lp_iRp_i = BigInt::mod_mul(x.0, x.1, order);
            BigInt::mod_add(&acc, &Lp_iRp_i, order)
        });
        let tx_fe = Scalar::<Secp256k1>::from(&tx);

        let challenge_x: Scalar<Secp256k1> = Sha256::new()
            .chain_bigint(&tau_x.to_bigint())
            .chain_bigint(&miu.to_bigint())
            .chain_bigint(&tx)
            .result_scalar();
        let Gx = G * &challenge_x;
        // P' = u^{xc}
        let P = &Gx * &tx_fe;

        let yi_inv = (0..nm)
            .map(|i| {
                //     let yi_fe = Scalar::<Secp256k1>::from(&yi[i]);
                //     yi_fe.invert()
                yi[i].invert().unwrap()
            })
            .collect::<Vec<Scalar<Secp256k1>>>();

        let hi_tag = (0..nm)
            .map(|i| &h_vec[i] * &yi_inv[i])
            .collect::<Vec<Point<Secp256k1>>>();

        // P' = P' g^l
        let P = g_vec.iter().zip(&Lp).fold(P, |acc, x| {
            let g_vec_i_lp_i = x.0 * &Scalar::<Secp256k1>::from(x.1);
            acc + g_vec_i_lp_i
        });
        // P' = P' h'^r
        let P = hi_tag.iter().zip(&Rp).fold(P, |acc, x| {
            let h_vec_i_rp_i = x.0 * &Scalar::<Secp256k1>::from(x.1);
            acc + h_vec_i_rp_i
        });
        // line 9
        // public input : g,h,u^x,P' = g_vec, hi_tag, Gx,P
        // private input: a,b  = Lp,Rp
        let L_vec = Vec::with_capacity(nm);
        let R_vec = Vec::with_capacity(nm);
        let inner_product_proof =
            InnerProductArg::prove(&g_vec, &hi_tag, &Gx, &P, &Lp, &Rp, L_vec, R_vec);

        RangeProof {
            A,
            S,
            T1,
            T2,
            tau_x,
            miu,
            tx: tx_fe,
            inner_product_proof,
        }
    }

    pub fn verify(
        &self,
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        G: &Point<Secp256k1>,
        H: &Point<Secp256k1>,
        ped_com: &[Point<Secp256k1>],
        bit_length: usize,
    ) -> Result<(), Errors> {
        let num_of_proofs = ped_com.len();
        let nm = num_of_proofs * bit_length;

        let y = Sha256::new()
            .chain_points([&self.A, &self.S])
            .result_scalar();
        let base_point = Point::<Secp256k1>::generator();
        let yG: Point<Secp256k1> = base_point * &y;
        let z: Scalar<Secp256k1> = Sha256::new().chain_points([&yG]).result_scalar();
        let z_bn = z.to_bigint();
        let order = Scalar::<Secp256k1>::group_order();
        let z_minus = BigInt::mod_sub(order, &z.to_bigint(), order);
        let z_minus_fe = Scalar::<Secp256k1>::from(&z_minus);
        let z_squared = BigInt::mod_pow(&z.to_bigint(), &BigInt::from(2), order);
        // delta(x,y):
        let one_bn = BigInt::one();
        let one_fe = Scalar::<Secp256k1>::from(&one_bn);
        let yi = iterate(one_fe.clone(), |i| i.clone() * &y)
            .take(nm)
            .collect::<Vec<Scalar<Secp256k1>>>();

        let scalar_mul_yn = yi
            .iter()
            .fold(Scalar::<Secp256k1>::zero(), |acc, x| acc + x);
        let scalar_mul_yn = scalar_mul_yn.to_bigint();
        let two = BigInt::from(2);

        let two_fe = Scalar::<Secp256k1>::from(&two);
        let vec_2n = iterate(one_fe, |i| i.clone() * &two_fe)
            .take(bit_length)
            .collect::<Vec<Scalar<Secp256k1>>>();

        let scalar_mul_2n = vec_2n
            .iter()
            .fold(Scalar::<Secp256k1>::zero(), |acc, x| acc + x);
        let scalar_mul_2n = scalar_mul_2n.to_bigint();

        let z_cubed_scalar_mul_2n = (0..num_of_proofs)
            .map(|i| {
                let j = BigInt::mod_add(&BigInt::from(3), &BigInt::from(i as u32), order);
                let z_j = BigInt::mod_pow(&z_bn, &j, order);
                BigInt::mod_mul(&z_j, &scalar_mul_2n, order)
            })
            .fold(BigInt::zero(), |acc, x| BigInt::mod_add(&acc, &x, order));

        let z_minus_zsq = BigInt::mod_sub(&z_bn, &z_squared, order);
        let z_minus_zsq_scalar_mul_yn = BigInt::mod_mul(&z_minus_zsq, &scalar_mul_yn, order);
        let delta = BigInt::mod_sub(&z_minus_zsq_scalar_mul_yn, &z_cubed_scalar_mul_2n, order);

        let yi_inv = (0..nm)
            .map(|i| yi[i].invert().unwrap())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let hi_tag = (0..nm)
            .map(|i| &h_vec[i] * &yi_inv[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let fs_challenge = Sha256::new()
            .chain_points([&self.T1, &self.T2, G, H])
            .result_scalar();
        let fs_challenge_square = &fs_challenge * &fs_challenge;

        // eq 65:
        let Gtx = G * &self.tx;
        let Htaux = H * &self.tau_x;
        let left_side = Gtx + Htaux;
        let delta_fe = Scalar::<Secp256k1>::from(&delta);
        let Gdelta = G * &delta_fe;
        let Tx = &self.T1 * &fs_challenge;
        let Tx_sq = &self.T2 * &fs_challenge_square;

        let mut vec_ped_zm = (0..num_of_proofs)
            .map(|i| {
                let z_2_m = BigInt::mod_pow(&z_bn, &BigInt::from((2 + i) as u32), order);
                let z_2_m_fe = Scalar::<Secp256k1>::from(&z_2_m);
                &ped_com[i] * &z_2_m_fe
            })
            .collect::<Vec<Point<Secp256k1>>>();
        let vec_ped_zm_1 = vec_ped_zm.remove(0);
        let ped_com_sum = vec_ped_zm.iter().fold(vec_ped_zm_1, |acc, x| acc + x);
        let right_side = ped_com_sum + Gdelta + Tx + Tx_sq;

        let challenge_x = Sha256::new()
            .chain_bigint(&self.tau_x.to_bigint())
            .chain_bigint(&self.miu.to_bigint())
            .chain_bigint(&self.tx.to_bigint())
            .result_scalar();
        let Gx = G * &challenge_x;
        // P' = u^{xc}

        let P = &Gx * &self.tx;
        let minus_miu = BigInt::mod_sub(
            Scalar::<Secp256k1>::group_order(),
            &self.miu.to_bigint(),
            Scalar::<Secp256k1>::group_order(),
        );
        let minus_miu_fe = Scalar::<Secp256k1>::from(&minus_miu);
        let Hmiu = H * &minus_miu_fe;
        let Sx = &self.S * &fs_challenge;
        let P = Hmiu + P + self.A.clone() + Sx;

        let P1 = (0..nm)
            .map(|i| {
                let z_yn = BigInt::mod_mul(&z_bn, &yi[i].to_bigint(), order);
                let j = i / bit_length;
                let k = i % bit_length;
                let z_j = BigInt::mod_pow(&z_bn, &BigInt::from((2 + j) as u32), order);
                let z_j_2_n = BigInt::mod_mul(&z_j, &vec_2n[k].to_bigint(), order);
                // let z_sq_2n = BigInt::mod_mul(&z_squared, &vec_2n[i], &order);
                let zyn_zsq2n = BigInt::mod_add(&z_yn, &z_j_2_n, order);
                let zyn_zsq2n_fe = Scalar::<Secp256k1>::from(&zyn_zsq2n);
                &hi_tag[i] * &zyn_zsq2n_fe
            })
            .fold(P, |acc, x| acc + x);

        let P = (0..nm)
            .map(|i| &g_vec[i] * &z_minus_fe)
            .fold(P1, |acc, x| acc + x);
        let verify = self.inner_product_proof.verify(g_vec, &hi_tag, &Gx, &P);
        if verify.is_ok() && left_side == right_side {
            Ok(())
        } else {
            Err(RangeProofError)
        }
    }

    pub fn fast_verify(
        &self,
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        G: &Point<Secp256k1>,
        H: &Point<Secp256k1>,
        ped_com: &[Point<Secp256k1>],
        bit_length: usize,
    ) -> Result<(), Errors> {
        let num_of_proofs = ped_com.len();
        let nm = num_of_proofs * bit_length;

        let y = Sha256::new()
            .chain_points([&self.A, &self.S])
            .result_scalar();
        let base_point = Point::<Secp256k1>::generator();
        let yG: Point<Secp256k1> = base_point * &y;
        let z: Scalar<Secp256k1> = Sha256::new().chain_points([&yG]).result_scalar();
        let z_bn = z.to_bigint();
        let order = Scalar::<Secp256k1>::group_order();
        let z_minus = BigInt::mod_sub(order, &z.to_bigint(), order);
        let z_minus_fe = Scalar::<Secp256k1>::from(&z_minus);
        let z_squared = BigInt::mod_pow(&z.to_bigint(), &BigInt::from(2), order);
        // delta(x,y):
        let one_bn = BigInt::one();
        let one_fe = Scalar::<Secp256k1>::from(&one_bn);
        let yi = iterate(one_fe.clone(), |i| i.clone() * &y)
            .take(nm)
            .collect::<Vec<Scalar<Secp256k1>>>();

        let scalar_mul_yn = yi
            .iter()
            .fold(Scalar::<Secp256k1>::zero(), |acc, x| acc + x);
        let scalar_mul_yn = scalar_mul_yn.to_bigint();
        let two = BigInt::from(2);

        let two_fe = Scalar::<Secp256k1>::from(&two);
        let vec_2n = iterate(one_fe, |i| i.clone() * &two_fe)
            .take(bit_length)
            .collect::<Vec<Scalar<Secp256k1>>>();

        let scalar_mul_2n = vec_2n
            .iter()
            .fold(Scalar::<Secp256k1>::zero(), |acc, x| acc + x);
        let scalar_mul_2n = scalar_mul_2n.to_bigint();

        let z_cubed_scalar_mul_2n = (0..num_of_proofs)
            .map(|i| {
                let j = BigInt::mod_add(&BigInt::from(3), &BigInt::from(i as u32), order);
                let z_j = BigInt::mod_pow(&z_bn, &j, order);
                BigInt::mod_mul(&z_j, &scalar_mul_2n, order)
            })
            .fold(BigInt::zero(), |acc, x| BigInt::mod_add(&acc, &x, order));

        let z_minus_zsq = BigInt::mod_sub(&z_bn, &z_squared, order);
        let z_minus_zsq_scalar_mul_yn = BigInt::mod_mul(&z_minus_zsq, &scalar_mul_yn, order);
        let delta = BigInt::mod_sub(&z_minus_zsq_scalar_mul_yn, &z_cubed_scalar_mul_2n, order);

        let yi_inv = (0..nm)
            .map(|i| yi[i].invert().unwrap())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let hi_tag = (0..nm)
            .map(|i| &h_vec[i] * &yi_inv[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let fs_challenge = Sha256::new()
            .chain_points([&self.T1, &self.T2, G, H])
            .result_scalar();
        let fs_challenge_square = &fs_challenge * &fs_challenge;

        // eq 65:
        let Gtx = G * &self.tx;
        let Htaux = H * &self.tau_x;
        let left_side = Gtx + Htaux;
        let delta_fe = Scalar::<Secp256k1>::from(&delta);
        let Gdelta = G * &delta_fe;
        let Tx = &self.T1 * &fs_challenge;
        let Tx_sq = &self.T2 * &fs_challenge_square;

        let mut vec_ped_zm = (0..num_of_proofs)
            .map(|i| {
                let z_2_m = BigInt::mod_pow(&z_bn, &BigInt::from((2 + i) as u32), order);
                let z_2_m_fe = Scalar::<Secp256k1>::from(&z_2_m);
                &ped_com[i] * &z_2_m_fe
            })
            .collect::<Vec<Point<Secp256k1>>>();
        let vec_ped_zm_1 = vec_ped_zm.remove(0);
        let ped_com_sum = vec_ped_zm.iter().fold(vec_ped_zm_1, |acc, x| acc + x);
        let right_side = ped_com_sum + Gdelta + Tx + Tx_sq;

        let challenge_x = Sha256::new()
            .chain_bigint(&self.tau_x.to_bigint())
            .chain_bigint(&self.miu.to_bigint())
            .chain_bigint(&self.tx.to_bigint())
            .result_scalar();
        let Gx = G * &challenge_x;
        // P' = u^{xc}

        let P = &Gx * &self.tx;
        let minus_miu = BigInt::mod_sub(
            Scalar::<Secp256k1>::group_order(),
            &self.miu.to_bigint(),
            Scalar::<Secp256k1>::group_order(),
        );
        let minus_miu_fe = Scalar::<Secp256k1>::from(&minus_miu);
        let Hmiu = H * &minus_miu_fe;
        let Sx = &self.S * &fs_challenge;
        let P = Hmiu + P + self.A.clone() + Sx;

        let P1 = (0..nm)
            .map(|i| {
                let z_yn = BigInt::mod_mul(&z_bn, &yi[i].to_bigint(), order);
                let j = i / bit_length;
                let k = i % bit_length;
                let z_j = BigInt::mod_pow(&z_bn, &BigInt::from((2 + j) as u32), order);
                let z_j_2_n = BigInt::mod_mul(&z_j, &vec_2n[k].to_bigint(), order);
                // let z_sq_2n = BigInt::mod_mul(&z_squared, &vec_2n[i], &order);
                let zyn_zsq2n = BigInt::mod_add(&z_yn, &z_j_2_n, order);
                let zyn_zsq2n_fe = Scalar::<Secp256k1>::from(&zyn_zsq2n);
                &hi_tag[i] * &zyn_zsq2n_fe
            })
            .fold(P, |acc, x| acc + x);

        let P = (0..nm)
            .map(|i| &g_vec[i] * &z_minus_fe)
            .fold(P1, |acc, x| acc + x);
        let verify = self
            .inner_product_proof
            .fast_verify(g_vec, &hi_tag, &Gx, &P);
        if verify.is_ok() && left_side == right_side {
            Ok(())
        } else {
            Err(RangeProofError)
        }
    }

    pub fn aggregated_verify(
        &self,
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        G: &Point<Secp256k1>,
        H: &Point<Secp256k1>,
        ped_com: &[Point<Secp256k1>],
        bit_length: usize,
    ) -> Result<(), Errors> {
        let n = bit_length;
        let m = ped_com.len();
        let nm = m * n;
        let lg_nm = self.inner_product_proof.L.len();
        let order = Scalar::<Secp256k1>::group_order();
        let two = BigInt::from(2);
        let one = BigInt::from(1);
        let zero = BigInt::zero();

        // All of the input vectors must have the same length.
        assert_eq!(g_vec.len(), nm);
        assert_eq!(h_vec.len(), nm);
        assert!(nm.is_power_of_two(), "(n*m) must be a power of two!");
        assert!(
            lg_nm <= 64,
            "Not compatible for vector sizes greater than 2^64!"
        );

        // regenerate challenges y, z, x, x_u from transcript
        let y = Sha256::new()
            .chain_points([&self.A, &self.S])
            .result_scalar();
        let y_bn = y.to_bigint();
        let y_inv_bn = BigInt::mod_inv(&y_bn, order).unwrap();
        let base_point = Point::<Secp256k1>::generator();
        let yG: Point<Secp256k1> = base_point * &y;
        let z: Scalar<Secp256k1> = Sha256::new().chain_points([&yG]).result_scalar();
        let z_bn = z.to_bigint();
        let z_squared = BigInt::mod_pow(&z_bn, &BigInt::from(2), order);

        let challenge_x: Scalar<Secp256k1> = Sha256::new()
            .chain_points([&self.T1, &self.T2, G, H])
            .result_scalar();
        let challenge_x_sq = &challenge_x * &challenge_x;

        let x_u_fe = Sha256::new()
            .chain_bigint(&self.tau_x.to_bigint())
            .chain_bigint(&self.miu.to_bigint())
            .chain_bigint(&self.tx.to_bigint())
            .result_scalar();

        // ux = g^{x_u}
        let ux = G * &x_u_fe;

        // generate a random scalar to combine 2 verification equations
        let challenge_ver: Scalar<Secp256k1> = Sha256::new()
            .chain_points([&self.A, &self.S, &self.T1, &self.T2, G, H])
            .result_scalar();
        let challenge_ver_bn = challenge_ver.to_bigint();

        // z2_vec = (z^2, z^3, z^4, ..., z^{m+1})
        let z2_vec = iterate(z_squared.clone(), |i| i.clone() * &z_bn)
            .take(m)
            .collect::<Vec<BigInt>>();

        // y_vec = (1, y, y^2, ..., y^{nm-1})
        let y_vec = iterate(one.clone(), |i| i.clone() * &y_bn)
            .take(nm)
            .collect::<Vec<BigInt>>();

        // sum_y_pow = 1 + y + ... + y^{nm}
        let sum_y_pow = y_vec
            .iter()
            .fold(zero.clone(), |acc, x| BigInt::mod_add(&acc, x, order));

        // vec_2n = (1, 2, 2^2, 2^3, ..., 2^{n})
        let vec_2n = iterate(one.clone(), |i| i.clone() * &two)
            .take(n)
            .collect::<Vec<BigInt>>();

        // y_inv_vec = (1, y^{-1}, y^{-2}, ..., y^{-(nm-1)})
        let y_inv_vec = iterate(one, |i| i.clone() * &y_inv_bn)
            .take(nm)
            .collect::<Vec<BigInt>>();

        // d = z^2 d1 + z^3 d2 + ... + z^{m+1} dm
        // where dj = (0^{(j-1)n} || 2^{n} || 0^{(m-j)n}) \in \Z_q^{mn}
        let d = (0..nm)
            .map(|i| {
                let k = i % n;
                let two_i = vec_2n[k].clone();
                let j = i / n;
                let z_j_2 = z2_vec[j].clone();
                BigInt::mod_mul(&two_i, &z_j_2, order)
            })
            .collect::<Vec<BigInt>>();

        // sum_d = <1^{mn}, d>
        let sum_d = d
            .iter()
            .fold(zero.clone(), |acc, x| BigInt::mod_add(&acc, x, order));

        // compute delta(y, z):
        let z_minus_zsq = BigInt::mod_sub(&z_bn, &z_squared, order);
        let z_minus_zsq_sum_y = BigInt::mod_mul(&z_minus_zsq, &sum_y_pow, order);
        let sum_d_z = BigInt::mod_mul(&sum_d, &z_bn, order);
        let delta = BigInt::mod_sub(&z_minus_zsq_sum_y, &sum_d_z, order);

        // compute sg and sh vectors (unrolling ipp verification)
        let mut x_sq_vec: Vec<BigInt> = Vec::with_capacity(lg_nm);
        let mut x_inv_sq_vec: Vec<BigInt> = Vec::with_capacity(lg_nm);
        let mut minus_x_sq_vec: Vec<BigInt> = Vec::with_capacity(lg_nm);
        let mut minus_x_inv_sq_vec: Vec<BigInt> = Vec::with_capacity(lg_nm);
        let mut allinv = BigInt::one();
        for (Li, Ri) in self
            .inner_product_proof
            .L
            .iter()
            .zip(self.inner_product_proof.R.iter())
        {
            let x: Scalar<Secp256k1> = Sha256::new().chain_points([Li, Ri, &ux]).result_scalar();
            let x_bn = x.to_bigint();
            let x_inv_fe = x.invert().unwrap();
            let x_inv_bn = x_inv_fe.to_bigint();
            let x_sq_bn = BigInt::mod_mul(&x_bn, &x_bn, order);
            let x_inv_sq_bn = BigInt::mod_mul(&x_inv_fe.to_bigint(), &x_inv_fe.to_bigint(), order);

            x_sq_vec.push(x_sq_bn.clone());
            x_inv_sq_vec.push(x_inv_sq_bn.clone());
            minus_x_sq_vec.push(BigInt::mod_sub(&BigInt::zero(), &x_sq_bn, order));
            minus_x_inv_sq_vec.push(BigInt::mod_sub(&BigInt::zero(), &x_inv_sq_bn, order));
            allinv *= x_inv_bn;
        }

        let mut s: Vec<BigInt> = Vec::with_capacity(nm);
        s.push(allinv);
        for i in 1..nm {
            let lg_i =
                (std::mem::size_of_val(&nm) * 8) - 1 - ((i as usize).leading_zeros() as usize);
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [x_k,...,x_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let x_lg_i_sq = x_sq_vec[(lg_nm - 1) - lg_i].clone();
            s.push(s[i - k].clone() * x_lg_i_sq);
        }

        let a_times_s: Vec<BigInt> = (0..nm)
            .map(|i| BigInt::mod_mul(&s[i], &self.inner_product_proof.a_tag, order))
            .collect();

        let b_times_sinv: Vec<BigInt> = (0..nm)
            .map(|i| {
                let s_inv_i = BigInt::mod_inv(&s[i], order).unwrap();
                BigInt::mod_mul(&s_inv_i, &self.inner_product_proof.b_tag, order)
            })
            .collect();

        // exponent of g_vec
        let scalar_g_vec: Vec<BigInt> = (0..nm)
            .map(|i| BigInt::mod_add(&a_times_s[i], &z_bn, order))
            .collect();

        // exponent of h_vec
        let scalar_h_vec: Vec<BigInt> = (0..nm)
            .map(|i| {
                let b_sinv_plus_di = BigInt::mod_sub(&b_times_sinv[i], &d[i], order);
                let y_inv_b_sinv_plus_di = BigInt::mod_mul(&y_inv_vec[i], &b_sinv_plus_di, order);
                BigInt::mod_sub(&y_inv_b_sinv_plus_di, &z_bn, order)
            })
            .collect();

        // exponent of G
        let ab = BigInt::mod_mul(
            &self.inner_product_proof.a_tag,
            &self.inner_product_proof.b_tag,
            order,
        );
        let ab_minus_tx = BigInt::mod_sub(&ab, &self.tx.to_bigint(), order);
        let scalar_G1 = BigInt::mod_mul(&x_u_fe.to_bigint(), &ab_minus_tx, order);

        let delta_minus_tx = BigInt::mod_sub(&delta, &self.tx.to_bigint(), order);
        let scalar_G2 = BigInt::mod_mul(&challenge_ver_bn, &delta_minus_tx, order);

        let scalar_G = BigInt::mod_add(&scalar_G1, &scalar_G2, order);

        // exponent of H
        let c_times_taux = BigInt::mod_mul(&challenge_ver_bn, &self.tau_x.to_bigint(), order);
        let scalar_H = BigInt::mod_sub(&self.miu.to_bigint(), &c_times_taux, order);

        // exponents of A, S
        // let scalar_A = BigInt::mod_sub(&zero, &one, &order);
        let scalar_S = BigInt::mod_sub(&zero, &challenge_x.to_bigint(), order);

        // exponent of L, R
        let scalar_L = minus_x_sq_vec.clone();
        let scalar_R = minus_x_inv_sq_vec.clone();

        // exponents of commitments
        let scalar_coms: Vec<BigInt> = (0..m)
            .map(|i| BigInt::mod_mul(&challenge_ver_bn, &z2_vec[i], order))
            .collect();

        // exponents of T_1, T_2
        let scalar_T1 = BigInt::mod_mul(&challenge_ver_bn, &challenge_x.to_bigint(), order);
        let scalar_T2 = BigInt::mod_mul(&challenge_ver_bn, &challenge_x_sq.to_bigint(), order);

        // compute concatenated exponent vector
        let mut scalars: Vec<BigInt> = Vec::with_capacity(2 * nm + 2 * lg_nm + m + 6);
        scalars.extend_from_slice(&scalar_g_vec);
        scalars.extend_from_slice(&scalar_h_vec);
        scalars.push(scalar_G);
        // scalars.push(scalar_H);
        // scalars.push(scalar_A);
        scalars.push(scalar_S);
        scalars.extend_from_slice(&scalar_L);
        scalars.extend_from_slice(&scalar_R);
        scalars.extend_from_slice(&scalar_coms);
        scalars.push(scalar_T1);
        scalars.push(scalar_T2);

        // compute concatenated base vector
        let mut points: Vec<Point<Secp256k1>> = Vec::with_capacity(2 * nm + 2 * lg_nm + m + 6);
        points.extend_from_slice(g_vec);
        points.extend_from_slice(h_vec);
        points.push(G.clone());
        // points.push(*H);
        // points.push(self.A);
        points.push(self.S.clone());
        points.extend_from_slice(&self.inner_product_proof.L);
        points.extend_from_slice(&self.inner_product_proof.R);
        points.extend_from_slice(ped_com);
        points.push(self.T1.clone());
        points.push(self.T2.clone());

        let H_times_scalar_H = H * &Scalar::<Secp256k1>::from(&scalar_H);
        let tot_len = points.len();
        let lhs = (0..tot_len)
            .map(|i| &points[i] * &Scalar::<Secp256k1>::from(&scalars[i]))
            .fold(H_times_scalar_H, |acc, x| acc + x as Point<Secp256k1>);

        // single multi-exponentiation check
        if lhs == self.A {
            Ok(())
        } else {
            Err(RangeProofError)
        }
    }
}

pub fn generate_random_point(bytes: &[u8]) -> Point<Secp256k1> {
    let compressed_point_len =
        <<Secp256k1 as Curve>::Point as ECPoint>::CompressedPointLength::USIZE;
    let truncated = if bytes.len() > compressed_point_len - 1 {
        &bytes[0..compressed_point_len - 1]
    } else {
        &bytes
    };
    let mut buffer = GenericArray::<
        u8,
        <<Secp256k1 as Curve>::Point as ECPoint>::CompressedPointLength,
    >::default();
    buffer.as_mut_slice()[0] = 0x2;
    buffer.as_mut_slice()[1..1 + truncated.len()].copy_from_slice(truncated);
    if let Ok(point) = Point::from_bytes(buffer.as_slice()) {
        return point;
    }

    let bn = BigInt::from_bytes(bytes);
    let two = BigInt::from(2);
    let bn_times_two = BigInt::mod_mul(&bn, &two, Scalar::<Secp256k1>::group_order());
    let bytes = BigInt::to_bytes(&bn_times_two);
    generate_random_point(&bytes)
}

#[cfg(test)]
mod tests {
    use curv::arithmetic::traits::*;
    use curv::cryptographic_primitives::hashing::{Digest, DigestExt};
    use curv::elliptic::curves::{secp256_k1::Secp256k1, Point, Scalar};
    use curv::BigInt;
    use sha2::Sha512;

    use curv::elliptic::curves::secp256_k1::hash_to_curve::generate_random_point;
    use proofs::range_proof::RangeProof;

    pub fn test_helper(seed: &BigInt, n: usize, m: usize) {
        let nm = n * m;
        let G = Point::<Secp256k1>::generator();
        let label = BigInt::from(1);
        let hash = Sha512::new().chain_bigint(&label).result_bigint();
        let H = generate_random_point(&Converter::to_bytes(&hash));

        let g_vec = (0..nm)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + seed;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to g_vec:
        let h_vec = (0..nm)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + seed;
                let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_j))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        let range = BigInt::from(2).pow(n as u32);
        let v_vec = (0..m)
            .map(|_| Scalar::<Secp256k1>::from(&BigInt::sample_below(&range)))
            .collect::<Vec<Scalar<Secp256k1>>>();

        let r_vec = (0..m)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let ped_com_vec = (0..m)
            .map(|i| &*G * &v_vec[i] + &H * &r_vec[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let range_proof = RangeProof::prove(&g_vec, &h_vec, &G, &H, v_vec, &r_vec, n);
        let result = RangeProof::verify(&range_proof, &g_vec, &h_vec, &G, &H, &ped_com_vec, n);
        assert!(result.is_ok());
    }

    pub fn test_helper_aggregated(seed: &BigInt, n: usize, m: usize) {
        let nm = n * m;
        let G = Point::<Secp256k1>::generator();
        let label = BigInt::from(1);
        let hash = Sha512::new().chain_bigint(&label).result_bigint();
        let H = generate_random_point(&Converter::to_bytes(&hash));

        let g_vec = (0..nm)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + seed;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to g_vec:
        let h_vec = (0..nm)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + seed;
                let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_j))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        let range = BigInt::from(2).pow(n as u32);
        let v_vec = (0..m)
            .map(|_| Scalar::<Secp256k1>::from(&BigInt::sample_below(&range)))
            .collect::<Vec<Scalar<Secp256k1>>>();

        let r_vec = (0..m)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let ped_com_vec = (0..m)
            .map(|i| &*G * &v_vec[i] + &H * &r_vec[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let range_proof = RangeProof::prove(&g_vec, &h_vec, &G, &H, v_vec, &r_vec, n);
        let result =
            RangeProof::aggregated_verify(&range_proof, &g_vec, &h_vec, &G, &H, &ped_com_vec, n);
        assert!(result.is_ok());
    }

    #[test]
    pub fn test_batch_4_range_proof_32() {
        let n = 32;
        // num of proofs
        let m = 4;
        let nm = n * m;
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);

        let G = Point::<Secp256k1>::generator();
        let label = BigInt::from(1);
        let hash = Sha512::new().chain_bigint(&label).result_bigint();
        let H = generate_random_point(&Converter::to_bytes(&hash));

        let g_vec = (0..nm)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to g_vec:
        let h_vec = (0..nm)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_j))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        let range = BigInt::from(2).pow(n as u32);
        let v_vec = (0..m)
            .map(|_| Scalar::<Secp256k1>::from(&BigInt::sample_below(&range)))
            .collect::<Vec<Scalar<Secp256k1>>>();

        let r_vec = (0..m)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let ped_com_vec = (0..m)
            .map(|i| &*G * &v_vec[i] + &H * &r_vec[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let range_proof = RangeProof::prove(&g_vec, &h_vec, &G, &H, v_vec, &r_vec, n);
        let result = RangeProof::verify(&range_proof, &g_vec, &h_vec, &G, &H, &ped_com_vec, n);
        assert!(result.is_ok());
    }

    #[test]
    #[should_panic]
    pub fn test_batch_4_range_proof_32_out_of_range() {
        let n = 32;
        // num of proofs
        let m = 4;
        let nm = n * m;
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);

        let G = Point::<Secp256k1>::generator();
        let label = BigInt::from(1);
        let hash = Sha512::new().chain_bigint(&label).result_bigint();
        let H = generate_random_point(&Converter::to_bytes(&hash));

        let g_vec = (0..nm)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to g_vec:
        let h_vec = (0..nm)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_j))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        let range = BigInt::from(2).pow(n as u32);
        let mut v_vec = (0..m - 1)
            .map(|_| Scalar::<Secp256k1>::from(&BigInt::sample_below(&range)))
            .collect::<Vec<Scalar<Secp256k1>>>();

        let bad_v = BigInt::from(2).pow(33);
        v_vec.push(Scalar::<Secp256k1>::from(&bad_v));

        let r_vec = (0..m)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let ped_com_vec = (0..m)
            .map(|i| &*G * &v_vec[i] + &H * &r_vec[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let range_proof = RangeProof::prove(&g_vec, &h_vec, &G, &H, v_vec, &r_vec, n);
        let result = RangeProof::verify(&range_proof, &g_vec, &h_vec, &G, &H, &ped_com_vec, n);
        assert!(result.is_ok());
    }

    #[test]
    pub fn test_batch_2_range_proof_16() {
        let n = 16;
        // num of proofs
        let m = 2;
        let nm = n * m;
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);

        let G = Point::<Secp256k1>::generator();
        let label = BigInt::from(1);
        let hash = Sha512::new().chain_bigint(&label).result_bigint();
        let H = generate_random_point(&Converter::to_bytes(&hash));

        let g_vec = (0..nm)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to g_vec:
        let h_vec = (0..nm)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_j))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        let range = BigInt::from(2).pow(n as u32);
        let v_vec = (0..m)
            .map(|_| Scalar::<Secp256k1>::from(&BigInt::sample_below(&range)))
            .collect::<Vec<Scalar<Secp256k1>>>();

        let r_vec = (0..m)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let ped_com_vec = (0..m)
            .map(|i| &*G * &v_vec[i] + &H * &r_vec[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let range_proof = RangeProof::prove(&g_vec, &h_vec, &G, &H, v_vec, &r_vec, n);
        let result = RangeProof::verify(&range_proof, &g_vec, &h_vec, &G, &H, &ped_com_vec, n);
        assert!(result.is_ok());
    }

    #[test]
    pub fn test_batch_1_range_proof_8() {
        // bit range
        let n = 8;
        // batch size
        let m = 1;
        let nm = n * m;
        // some seed for generating g and h vectors
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);

        // G,H - points for pederson commitment: com  = vG + rH
        let G = Point::<Secp256k1>::generator();
        let label = BigInt::from(1);
        let hash = Sha512::new().chain_bigint(&label).result_bigint();
        let H = generate_random_point(&Converter::to_bytes(&hash));

        let g_vec = (0..nm)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to g_vec:
        let h_vec = (0..nm)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_j))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        let range = BigInt::from(2).pow(n as u32);
        let v_vec = (0..m)
            .map(|_| Scalar::<Secp256k1>::from(&BigInt::sample_below(&range)))
            .collect::<Vec<Scalar<Secp256k1>>>();

        let r_vec = (0..m)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let ped_com_vec = (0..m)
            .map(|i| &*G * &v_vec[i] + &H * &r_vec[i])
            .collect::<Vec<Point<Secp256k1>>>();

        let range_proof = RangeProof::prove(&g_vec, &h_vec, &G, &H, v_vec, &r_vec, n);
        let result = RangeProof::verify(&range_proof, &g_vec, &h_vec, &G, &H, &ped_com_vec, n);
        assert!(result.is_ok());
    }

    #[test]
    pub fn test_batch_4_range_proof_64() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper(&kzen_label, 64, 4);
    }

    #[test]
    pub fn test_agg_batch_4_range_proof_64() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper_aggregated(&kzen_label, 64, 4);
    }
}
