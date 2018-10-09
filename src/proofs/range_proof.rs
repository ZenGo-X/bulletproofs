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
use cryptography_utils::arithmetic::traits::{Converter, Modulo};
use cryptography_utils::cryptographic_primitives::hashing::hash_sha256::HSha256;
use cryptography_utils::cryptographic_primitives::hashing::hash_sha512::HSha512;
use cryptography_utils::cryptographic_primitives::hashing::traits::*;
use cryptography_utils::elliptic::curves::traits::*;
use cryptography_utils::BigInt;
use cryptography_utils::{FE, GE};
use itertools::Itertools;
use proofs::inner_product::InnerProductArg;
use std::ops::Shr;
use Errors::{self, RangeProofError};
pub struct RangeProof {
    A: GE,
    S: GE,
    T1: GE,
    T2: GE,
    tau_x: FE,
    miu: FE,
    tx: FE,
    inner_product_proof: InnerProductArg,
}

impl RangeProof {
    pub fn prove(
        g_vec: &Vec<GE>,
        h_vec: &Vec<GE>,
        G: &GE,
        H: &GE,
        secret: &FE,
        blinding: &FE,
        bit_length: usize,
    ) -> RangeProof {
        let alpha: FE = ECScalar::new_random();
        let rho: FE = ECScalar::new_random();

        let g_vec = g_vec.to_vec();
        let h_vec = h_vec.to_vec();

        let mut A = H.clone() * &alpha;
        let mut S = H.clone() * &rho;
        let secret_bn = secret.to_big_int();
        let two = BigInt::from(2);
        let one = BigInt::from(1);
        let order = alpha.q();

        let aL = (0..bit_length)
            .map(|i| secret_bn.clone().shr(i).modulus(&two))
            .collect::<Vec<BigInt>>();

        let aR = (0..bit_length)
            .map(|i| BigInt::mod_sub(&aL[i], &one, &order))
            .collect::<Vec<BigInt>>();

        let secret_bits = (0..bit_length)
            .map(|i| {
                let bignum_bit: BigInt = (&secret_bn >> i) & BigInt::one();
                let byte = BigInt::to_vec(&bignum_bit);
                byte[0]
            }).collect::<Vec<u8>>();
        let mut index: usize = 0;

        A = g_vec.iter().zip(&secret_bits).fold(A, |acc, x| {
            if *x.1 == 1u8 {
                acc.add_point(&x.0.get_element())
            } else {
                acc
            }
        });

        A = h_vec.iter().zip(&secret_bits).fold(A, |acc, x| {
            if *x.1 == 0u8 {
                acc.sub_point(&x.0.get_element())
            } else {
                acc
            }
        });

        let SR = (0..bit_length)
            .map(|_| ECScalar::new_random())
            .collect::<Vec<FE>>();
        let SL = (0..bit_length)
            .map(|_| ECScalar::new_random())
            .collect::<Vec<FE>>();

        S = SL.iter().zip(&SR).fold(S, |acc, x| {
            let g_vec_i: GE = g_vec[index].clone();
            let h_vec_i: GE = h_vec[index].clone();
            index = index + 1;
            let g_vec_i_SLi = g_vec_i * x.0;
            let h_vec_i_SRi = h_vec_i * x.1;
            let SRhi_plus_SLgi = h_vec_i_SRi + g_vec_i_SLi;
            acc + SRhi_plus_SLgi
        });

        let y = HSha256::create_hash_from_ge(&[&A, &S]);
        let base_point: GE = ECPoint::generator();
        let yG: GE = base_point * &y;
        let z = HSha256::create_hash_from_ge(&[&yG]);
        let z_bn = z.to_big_int();
        let z_squared = BigInt::mod_pow(&z.to_big_int(), &BigInt::from(2), &order);
        let z_cubed = BigInt::mod_pow(&z.to_big_int(), &BigInt::from(3), &order);

        let yi = (0..bit_length)
            .map(|i| BigInt::mod_pow(&y.to_big_int(), &BigInt::from(i as u32), &order))
            .collect::<Vec<BigInt>>();

        let t2 = (0..bit_length)
            .map(|i| {
                let t2_1 = BigInt::mod_mul(&SR[i].to_big_int(), &yi[i], &order);
                let t2_2 = BigInt::mod_mul(&t2_1, &SL[i].to_big_int(), &order);
                t2_2
            }).fold(BigInt::zero(), |acc, x| BigInt::mod_add(&acc, &x, &order));

        let t0 = (0..bit_length)
            .map(|i| {
                let t0_1 = BigInt::mod_sub(&aL[i], &z_bn, &order);
                let t0_2 = BigInt::mod_add(&aR[i], &z_bn, &order);
                let t0_3 = BigInt::mod_mul(&yi[i], &t0_2, &order);
                let two_to_the_i = BigInt::mod_pow(&two, &BigInt::from(i as u32), &order);
                let t0_4 = BigInt::mod_mul(&z_squared, &two_to_the_i, &order);
                let t0_5 = BigInt::mod_add(&t0_4, &t0_3, &order);
                BigInt::mod_mul(&t0_5, &t0_1, &order)
            }).fold(BigInt::zero(), |acc, x| BigInt::mod_add(&acc, &x, &order));

        let t1 = (0..bit_length)
            .map(|i| {
                let t1_1 = BigInt::mod_add(&aR[i], &z_bn, &order);
                let t1_2 = BigInt::mod_mul(&t1_1, &yi[i], &order);
                let t1_3 = BigInt::mod_mul(&SL[i].to_big_int(), &t1_2, &order);
                let t1_4 = BigInt::mod_sub(&aL[i], &z_bn, &order);
                let t1_5 = BigInt::mod_mul(&SR[i].to_big_int(), &yi[i], &order);
                let t1_6 = BigInt::mod_mul(&t1_4, &t1_5, &order);
                let two_to_the_i = BigInt::mod_pow(&two, &BigInt::from(i as u32), &order);
                let t1_7 = BigInt::mod_mul(&z_squared, &two_to_the_i, &order);
                let t1_8 = BigInt::mod_mul(&t1_7, &SL[i].to_big_int(), &order);
                let t1_68 = BigInt::mod_add(&t1_6, &t1_8, &order);
                BigInt::mod_add(&t1_3, &t1_68, &order)
            }).fold(BigInt::zero(), |acc, x| BigInt::mod_add(&acc, &x, &order));

        let tau1: FE = ECScalar::new_random();
        let tau2: FE = ECScalar::new_random();
        let t1_fe = ECScalar::from(&t1);
        let t2_fe = ECScalar::from(&t2);
        let T1 = (G.clone() * &t1_fe) + (H.clone() * &tau1);
        let T2 = (G.clone() * &t2_fe) + (H.clone() * &tau2);

        let fs_challenge = HSha256::create_hash_from_ge(&[&T1, &T2, G, H]);
        let fs_challenge_square = fs_challenge.mul(&fs_challenge.get_element());
        let taux_1 = fs_challenge.mul(&tau1.get_element());
        let taux_2 = fs_challenge_square.mul(&tau2.get_element());
        let z_squared_fe: FE = ECScalar::from(&z_squared);
        let taux_3 = z_squared_fe.mul(&blinding.get_element());
        let tau_x = taux_1.add(&taux_2.get_element()).add(&taux_3.get_element());
        let miu = (rho.mul(&fs_challenge.get_element())).add(&alpha.get_element());

        let Lp = (0..bit_length)
            .map(|i| {
                let Lp_1 = (SL[i].mul(&fs_challenge.get_element())).to_big_int();
                let Lp_2 = BigInt::mod_sub(&aL[i], &z.to_big_int(), &order);
                BigInt::mod_add(&Lp_1, &Lp_2, &order)
            }).collect::<Vec<BigInt>>();

        let Rp = (0..bit_length)
            .map(|i| {
                let Rp_1 = (SR[i].mul(&fs_challenge.get_element())).to_big_int();
                let two_to_the_i = BigInt::mod_pow(&two, &BigInt::from(i as u32), &order);
                let Rp_2 = BigInt::mod_mul(&z_squared, &two_to_the_i, &order);
                let Rp_3 = BigInt::mod_add(
                    &BigInt::mod_add(&z.to_big_int(), &aR[i], &order),
                    &Rp_1,
                    &order,
                );
                let Rp_4 = BigInt::mod_mul(&yi[i], &Rp_3, &order);
                BigInt::mod_add(&Rp_4, &Rp_2, &order)
            }).collect::<Vec<BigInt>>();
        let tx = Lp.iter().zip(&Rp).fold(BigInt::zero(), |acc, x| {
            let Lp_iRp_i = BigInt::mod_mul(x.0, x.1, &order);
            BigInt::mod_add(&acc, &Lp_iRp_i, &order)
        });
        let tx_fe: FE = ECScalar::from(&tx);
        let challenge_x = HSha256::create_hash(&[&tau_x.to_big_int(), &miu.to_big_int(), &tx]);
        let challenge_x: FE = ECScalar::from(&challenge_x);
        let Gx = G.clone() * &challenge_x;
        // P' = u^{xc}
        let P = Gx.clone() * &tx_fe;

        let yi_inv = (0..bit_length)
            .map(|i| {
                let yi_fe: FE = ECScalar::from(&yi[i]);
                yi_fe.invert()
            }).collect::<Vec<FE>>();

        let hi_tag = (0..bit_length)
            .map(|i| h_vec[i].clone() * &yi_inv[i])
            .collect::<Vec<GE>>();

        // P' = P' g^l
        let P = g_vec.iter().zip(&Lp).fold(P, |acc, x| {
            let g_vec_i_lp_i = x.0.clone() * &ECScalar::from(x.1);
            acc + g_vec_i_lp_i
        });
        // P' = P' h'^r
        let P = hi_tag.iter().zip(&Rp).fold(P, |acc, x| {
            let h_vec_i_rp_i = x.0.clone() * &ECScalar::from(x.1);
            acc + h_vec_i_rp_i
        });
        // line 9
        // public input : g,h,u^x,P' = g_vec, hi_tag, Gx,P
        // private input: a,b  = Lp,Rp
        let mut L_vec = Vec::with_capacity(bit_length);
        let mut R_vec = Vec::with_capacity(bit_length);
        let inner_product_proof =
            InnerProductArg::prove(g_vec, hi_tag, Gx, P, Lp, Rp, L_vec, R_vec);

        let chal_bn = fs_challenge.to_big_int();
        let chal_sq_bn = fs_challenge_square.to_big_int();
        let res1 = BigInt::mod_mul(&t1, &chal_bn, &order);
        let res2 = BigInt::mod_mul(&t2, &chal_sq_bn, &order);
        let res3 = BigInt::mod_add(&res1, &res2, &order);
        let res4 = BigInt::mod_add(&res3, &t0, &order);
        return RangeProof {
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

    pub fn verify(
        &self,
        g_vec: &Vec<GE>,
        h_vec: &Vec<GE>,
        G: &GE,
        H: &GE,
        ped_com: &GE,
        bit_length: usize,
    ) -> Result<bool, Errors> {
        let g_vec = g_vec.to_vec();
        let h_vec = h_vec.to_vec();

        let y = HSha256::create_hash_from_ge(&[&self.A, &self.S]);
        let base_point: GE = ECPoint::generator();
        let yG: GE = base_point * &y;
        let z = HSha256::create_hash_from_ge(&[&yG]);
        let order = self.tau_x.q();
        let z_minus = BigInt::mod_sub(&order, &z.to_big_int(), &order);
        let z_minus_fe: FE = ECScalar::from(&z_minus);
        let z_squared = BigInt::mod_pow(&z.to_big_int(), &BigInt::from(2), &order);
        let z_cubed = BigInt::mod_pow(&z.to_big_int(), &BigInt::from(3), &order);
        let z_sq_fe: FE = ECScalar::from(&z_squared);
        // delta(x,y):
        let yi = (0..bit_length)
            .map(|i| BigInt::mod_pow(&y.to_big_int(), &BigInt::from(i as u32), &order))
            .collect::<Vec<BigInt>>();

        let scalar_mul_yn = yi
            .iter()
            .fold(BigInt::zero(), |acc, x| BigInt::mod_add(&acc, x, &order));

        let two = BigInt::from(2);
        let vec_2n = (0..bit_length)
            .map(|i| BigInt::mod_pow(&two, &BigInt::from(i as u32), &order))
            .collect::<Vec<BigInt>>();

        let scalar_mul_2n = vec_2n.iter().fold(BigInt::zero(), |acc, x: &BigInt| {
            BigInt::mod_add(&acc, x, &order)
        });

        let z_minus_zsq = BigInt::mod_sub(&z.to_big_int(), &z_squared, &order);
        let z_minus_zsq_scalar_mul_yn = BigInt::mod_mul(&z_minus_zsq, &scalar_mul_yn, &order);
        let z_cubed_scalar_mul_2n = BigInt::mod_mul(&z_cubed, &scalar_mul_2n, &order);
        let delta = BigInt::mod_sub(&z_minus_zsq_scalar_mul_yn, &z_cubed_scalar_mul_2n, &order);

        let yi_inv = (0..bit_length)
            .map(|i| {
                let yi_fe: FE = ECScalar::from(&yi[i]);
                yi_fe.invert()
            }).collect::<Vec<FE>>();

        let hi_tag = (0..bit_length)
            .map(|i| h_vec[i].clone() * &yi_inv[i])
            .collect::<Vec<GE>>();

        let fs_challenge = HSha256::create_hash_from_ge(&[&self.T1, &self.T2, G, H]);
        let fs_challenge_square = fs_challenge.mul(&fs_challenge.get_element());

        // eq 65:
        let Gtx = G.clone() * &self.tx;
        let Htaux = H.clone() * &self.tau_x;
        let left_side = Gtx + Htaux;
        let delta_fe: FE = ECScalar::from(&delta);
        let Gdelta = G.clone() * &delta_fe;
        let Tx = self.T1.clone() * &fs_challenge;
        let Tx_sq = self.T2.clone() * &fs_challenge_square;
        let ped_com_z_sq = ped_com.clone() * &z_sq_fe;
        let right_side = ped_com_z_sq + Gdelta + Tx + Tx_sq;

        let challenge_x = HSha256::create_hash(&[
            &self.tau_x.to_big_int(),
            &self.miu.to_big_int(),
            &self.tx.to_big_int(),
        ]);
        let challenge_x: FE = ECScalar::from(&challenge_x);
        let Gx = G.clone() * &challenge_x;
        // P' = u^{xc}

        let P = Gx.clone() * &self.tx;
        let minus_miu = BigInt::mod_sub(&self.miu.q(), &self.miu.to_big_int(), &self.miu.q());
        let minus_miu_fe: FE = ECScalar::from(&minus_miu);
        let Hmiu = H.clone() * minus_miu_fe;
        let Sx = self.S.clone() * &fs_challenge;
        let P = Hmiu + P + self.A.clone() + Sx;

        let P1 = (0..bit_length)
            .map(|i| {
                let z_yn = BigInt::mod_mul(&z.to_big_int(), &yi[i], &order);
                let z_sq_2n = BigInt::mod_mul(&z_squared, &vec_2n[i], &order);
                let zyn_zsq2n = BigInt::mod_add(&z_yn, &z_sq_2n, &order);
                let zyn_zsq2n_fe: FE = ECScalar::from(&zyn_zsq2n);
                hi_tag[i].clone() * zyn_zsq2n_fe
            }).fold(P, |acc, x| acc + x);

        let P = (0..bit_length)
            .map(|i| g_vec[i].clone() * &z_minus_fe)
            .fold(P1, |acc, x| acc + x);

        let verify = self.inner_product_proof.verify(g_vec, hi_tag, Gx, P);

        if verify.is_ok() && left_side.get_element() == right_side.get_element() {
            Ok(true)
        } else {
            Err(RangeProofError)
        }
    }
}

pub fn generate_random_point(bytes: &[u8]) -> GE {
    let result: Result<GE, _> = ECPoint::from_bytes(&bytes);
    if result.is_ok() {
        return result.unwrap();
    } else {
        let two = BigInt::from(2);
        let temp: FE = ECScalar::new_random();
        let bn = BigInt::from(bytes);
        let bn_times_two = BigInt::mod_mul(&bn, &two, &temp.q());
        let bytes = BigInt::to_vec(&bn_times_two);
        return generate_random_point(&bytes);
    }
}

#[cfg(test)]
mod tests {
    use super::generate_random_point;
    use super::RangeProof;
    use cryptography_utils::arithmetic::traits::{Converter, Modulo};
    use cryptography_utils::cryptographic_primitives::hashing::hash_sha256::HSha256;
    use cryptography_utils::cryptographic_primitives::hashing::hash_sha512::HSha512;
    use cryptography_utils::cryptographic_primitives::hashing::traits::*;
    use cryptography_utils::elliptic::curves::traits::*;
    use cryptography_utils::BigInt;
    use cryptography_utils::{FE, GE};
    use itertools::Itertools;
    use proofs::inner_product::InnerProductArg;
    use std::ops::Shr;
    use Errors::{self, RangeProofError};

    #[test]
    pub fn test_range_proof_64() {
        let n = 64;
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from(KZen);

        let g_vec = (0..n)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = HSha512::create_hash(&[&kzen_label_i]);
                generate_random_point(&Converter::to_vec(&hash_i))
            }).collect::<Vec<GE>>();

        // can run in parallel to g_vec:
        let h_vec = (0..n)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = HSha512::create_hash(&[&kzen_label_j]);
                generate_random_point(&Converter::to_vec(&hash_j))
            }).collect::<Vec<GE>>();

        let two = BigInt::from(2);
        let v = two.pow(5) + BigInt::one();
        let v_fe: FE = ECScalar::from(&v);
        let r: FE = ECScalar::new_random();
        let G: GE = ECPoint::generator();

        let label = BigInt::from(1);
        let hash = HSha512::create_hash(&[&label]);
        let H = generate_random_point(&Converter::to_vec(&hash));

        let Gv = G.clone() * &v_fe;
        let Hr = H.clone() * &r;
        let ped_com = Gv + Hr;
        let range_proof = RangeProof::prove(&g_vec, &h_vec, &G, &H, &v_fe, &r, n);
        let result = RangeProof::verify(&range_proof, &g_vec, &h_vec, &G, &H, &ped_com, n);
        assert!(result.is_ok());
    }
    #[test]
    pub fn test_range_proof_16() {
        let n = 16;
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from(KZen);

        let g_vec = (0..n)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = HSha512::create_hash(&[&kzen_label_i]);
                generate_random_point(&Converter::to_vec(&hash_i))
            }).collect::<Vec<GE>>();

        // can run in parallel to g_vec:
        let h_vec = (0..n)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = HSha512::create_hash(&[&kzen_label_j]);
                generate_random_point(&Converter::to_vec(&hash_j))
            }).collect::<Vec<GE>>();

        let two = BigInt::from(2);
        let v = two.pow(13) + BigInt::one();
        let v_fe: FE = ECScalar::from(&v);
        let r: FE = ECScalar::new_random();
        let G: GE = ECPoint::generator();

        let label = BigInt::from(1);
        let hash = HSha512::create_hash(&[&label]);
        let H = generate_random_point(&Converter::to_vec(&hash));

        let Gv = G.clone() * &v_fe;
        let Hr = H.clone() * &r;
        let ped_com = Gv + Hr;
        let range_proof = RangeProof::prove(&g_vec, &h_vec, &G, &H, &v_fe, &r, n);
        let result = RangeProof::verify(&range_proof, &g_vec, &h_vec, &G, &H, &ped_com, n);
        assert!(result.is_ok());
    }

    #[test]
    #[should_panic]
    pub fn test_range_proof_32_out_of_range() {
        let n = 32;
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from(KZen);

        let g_vec = (0..n)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = HSha512::create_hash(&[&kzen_label_i]);
                generate_random_point(&Converter::to_vec(&hash_i))
            }).collect::<Vec<GE>>();

        // can run in parallel to g_vec:
        let h_vec = (0..n)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = HSha512::create_hash(&[&kzen_label_j]);
                generate_random_point(&Converter::to_vec(&hash_j))
            }).collect::<Vec<GE>>();

        let two = BigInt::from(2);
        let v = two.pow(34) + BigInt::one();
        let v_fe: FE = ECScalar::from(&v);
        let r: FE = ECScalar::new_random();
        let G: GE = ECPoint::generator();

        let label = BigInt::from(1);
        let hash = HSha512::create_hash(&[&label]);
        let H = generate_random_point(&Converter::to_vec(&hash));

        let Gv = G.clone() * &v_fe;
        let Hr = H.clone() * &r;
        let ped_com = Gv + Hr;
        let range_proof = RangeProof::prove(&g_vec, &h_vec, &G, &H, &v_fe, &r, n);
        let result = RangeProof::verify(&range_proof, &g_vec, &h_vec, &G, &H, &ped_com, n);
        assert!(result.is_ok());
    }

}
