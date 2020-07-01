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

// based on the paper: https://eprint.iacr.org/2020/735.pdf
// This is an implementation of figure 3 - aggregated range proof protocol from the above paper.
//
// Bulletproofs (https://eprint.iacr.org/2017/1066) uses the inner product argument.
// Bulletproofs+ (https://eprint.iacr.org/2020/735.pdf) uses the weighted inner product argument
// which reduces the overall prover communication by ~15%
// 
use curv::arithmetic::traits::{Converter, Modulo};
use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
use curv::cryptographic_primitives::hashing::hash_sha512::HSha512;
use curv::cryptographic_primitives::hashing::traits::*;
use curv::elliptic::curves::traits::*;
use curv::BigInt;
use curv::{FE, GE};
use itertools::iterate;
use proofs::range_proof::generate_random_point;
use proofs::weighted_inner_product::WeightedInnerProdArg;
use std::ops::{Shl, Shr};
use Errors::{self, RangeProofError};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StatementRP {
    pub g_vec: Vec<GE>,
    pub h_vec: Vec<GE>,
    pub G: GE,
    pub H: GE,
    pub bit_length: usize,
}

impl StatementRP {
    pub fn generate_bases(
        init_seed: &BigInt,
        num_of_proofs: usize,
        bit_length: usize,
    ) -> StatementRP {

        let n = bit_length;
        let m = num_of_proofs;
        let nm = n * m;

        // G,H - points for pederson commitment: com  = vG + rH
        let G: GE = ECPoint::generator();
        let label = BigInt::mod_sub(&init_seed, &BigInt::one(), &FE::q());
        let hash = HSha512::create_hash(&[&label]);
        let H = generate_random_point(&Converter::to_vec(&hash));

        let g_vec = (0..nm)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + init_seed;
                let hash_i = HSha512::create_hash(&[&kzen_label_i]);
                generate_random_point(&Converter::to_vec(&hash_i))
            })
            .collect::<Vec<GE>>();

        // can run in parallel to g_vec:
        let h_vec = (0..nm)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + init_seed;
                let hash_j = HSha512::create_hash(&[&kzen_label_j]);
                generate_random_point(&Converter::to_vec(&hash_j))
            })
            .collect::<Vec<GE>>();
        
        return StatementRP{
            g_vec,
            h_vec,
            G,
            H,
            bit_length,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RangeProofWIP {
    A: GE,
    weighted_inner_product_proof: WeightedInnerProdArg,
}

impl RangeProofWIP {
    pub fn prove(
        stmt: StatementRP,
        mut secret: Vec<FE>,
        blinding: &[FE],
    ) -> RangeProofWIP {

        let num_of_proofs = secret.len();
        let bit_length = stmt.bit_length;
        //num of proofs times bit length
        let nm = num_of_proofs * bit_length;
        
        let g_vec = stmt.g_vec.to_vec();
        let h_vec = stmt.h_vec.to_vec();
        let G = stmt.G;
        let H = stmt.H;

        let N = g_vec.len();
        let two = BigInt::from(2);
        let one = BigInt::from(1);
        let order = FE::q();

        // All of the input vectors must have the same length.
        assert_eq!(h_vec.len(), N);
        assert!(N.is_power_of_two());

        //concat all secrets:
        secret.reverse();
        let secret_agg = secret.iter().fold(BigInt::zero(), |acc, x| {
            acc.shl(bit_length) + x.to_big_int()
        });

        let aL = (0..nm)
            .map(|i| {
                let shr_secret = secret_agg.clone().shr(i);
                shr_secret.modulus(&two)
            })
            .collect::<Vec<BigInt>>();
        let aR = (0..nm)
            .map(|i| BigInt::mod_sub(&aL[i], &one, &order))
            .collect::<Vec<BigInt>>();

        let secret_bits = (0..nm)
            .map(|i| {
                let bignum_bit: BigInt = aL[i].clone() & BigInt::one();
                let byte = BigInt::to_vec(&bignum_bit);
                byte[0] == 1
            })
            .collect::<Vec<bool>>();

        // let mut index: usize = 0;
        let alpha: FE = ECScalar::new_random();
        let mut A = H * &alpha;
        A = g_vec.iter().zip(secret_bits.clone()).fold(A, |acc, x| {
            if x.1 {
                acc.add_point(&x.0.get_element())
            } else {
                acc
            }
        });
        A = h_vec.iter().zip(secret_bits.clone()).fold(A, |acc, x| {
            if !x.1 {
                acc.sub_point(&x.0.get_element())
            } else {
                acc
            }
        });

        let y = HSha256::create_hash_from_ge(&[&A]);
        let y_bn = y.to_big_int();
        let base_point: GE = ECPoint::generator();
        let yG: GE = base_point * &y;
        let z = HSha256::create_hash_from_ge(&[&A, &yG]);
        let z_bn = z.to_big_int();
        let z_sq_bn = BigInt::mod_mul(&z_bn, &z_bn, &order);
        
        // y_vec = (y, y^2, ..., y^{nm})
        let y_powers = iterate(y_bn.clone(), |i| BigInt::mod_mul(&i, &y_bn, &order))
            .take(nm)
            .collect::<Vec<BigInt>>();
        let mut y_powers_rev = y_powers.clone();
        y_powers_rev.reverse();

        // vec_2n = (1, 2, 4, ..., 2^{n-1})
        let vec_2n = iterate(one.clone(), |i| i.clone() * &two)
            .take(bit_length)
            .collect::<Vec<BigInt>>();

        // vec_z2m = (z^2, z^4, ..., z^{2m})
        let vec_z2m = iterate(z_sq_bn.clone(), |i| i.clone() * &z_sq_bn)
            .take(num_of_proofs)
            .collect::<Vec<BigInt>>();

        // d = z^2 d1 + z^4 d2 + ... + z^{2m} dm
        let d = (0..nm)
            .map(|i| {
                let k = i % bit_length;
                let two_i = vec_2n[k].clone();
                let j = i / bit_length;
                let z_2j = vec_z2m[j].clone();
                BigInt::mod_mul(&two_i, &z_2j, &order)
            })
            .collect::<Vec<BigInt>>();

        // compute exponent of h
        let y_pow = BigInt::mod_pow(&y_bn, &BigInt::from((nm + 1) as u32), &order);
        let ip_blinding = (0..num_of_proofs)
            .map(|i| {
                BigInt::mod_mul(&blinding[i].to_big_int(), &vec_z2m[i].clone(), &order)
            })
            .fold(BigInt::zero(), |acc, x| BigInt::mod_add(&acc, &x, &order));
        let scalar_H = BigInt::mod_mul(&ip_blinding, &y_pow, &order);

        // compute exponent of g
        let ip_secrets = (0..num_of_proofs)
            .map(|i| {
                BigInt::mod_mul(&secret[i].to_big_int(),  &vec_z2m[i].clone(), &order)
            })
            .fold(BigInt::zero(), |acc, x| BigInt::mod_add(&acc, &x, &order));
        let scalar1_G = BigInt::mod_mul(&ip_secrets, &y_pow, &order);

        let scalar_G = (0..nm)
            .map(|i| {
                let z_minus_z2 = BigInt::mod_sub(&z_bn, &z_sq_bn, &order);
                let yi_z_minus_z2 = BigInt::mod_mul(&z_minus_z2, &y_powers[i].clone(), &order);
                let z_y_pow = BigInt::mod_mul(&z_bn, &y_pow, &order);
                let di_z_y_pow = BigInt::mod_mul(&d[i], &z_y_pow, &order);
                BigInt::mod_sub(&yi_z_minus_z2, &di_z_y_pow, &order)
            })
            .fold(scalar1_G, |acc, x| BigInt::mod_add(&acc, &x, &order));

        // compute exponents of g_vec
        let scalars_g_vec = (0..nm)
            .map(|_| {
                BigInt::mod_sub(&BigInt::zero(), &z_bn, &order)
            })
            .collect::<Vec<BigInt>>();

        // compute exponents of h_vec
        let scalars_h_vec = (0..nm)
            .map(|i| {
                let di_yi_rev = BigInt::mod_mul(&d[i], &y_powers_rev[i].clone(), &order);
                BigInt::mod_add(&di_yi_rev, &z_bn, &order)
            })
            .collect::<Vec<BigInt>>();     

        let mut A_hat_scalars: Vec<BigInt> = Vec::with_capacity(2*nm + 2);
        A_hat_scalars.extend_from_slice(&scalars_g_vec);
        A_hat_scalars.extend_from_slice(&scalars_h_vec);
        A_hat_scalars.extend_from_slice(&[scalar_G.clone(), scalar_H.clone()]);

        let mut A_hat_bases: Vec<GE> = Vec::with_capacity(2*nm + 2);
        A_hat_bases.extend_from_slice(&g_vec);
        A_hat_bases.extend_from_slice(&h_vec);
        A_hat_bases.extend_from_slice(&[G, H]);

        let A_hat = (0..(2*nm + 2))
            .map(|i| A_hat_bases[i] * &ECScalar::from(&A_hat_scalars[i]))
            .fold(A.clone(), |acc, x| acc + x as GE);

        // compute aL_hat, aR_hat, alpha_hat
        let aL_hat = (0..nm)
            .map(|i| {
                BigInt::mod_add(&aL[i], &scalars_g_vec[i], &order)
            })
            .collect::<Vec<BigInt>>();

        let aR_hat = (0..nm)
            .map(|i| {
                BigInt::mod_add(&aR[i], &scalars_h_vec[i], &order)
            })
            .collect::<Vec<BigInt>>();

        let alpha_hat = BigInt::mod_add(&alpha.to_big_int(), &scalar_H, &order);
        
        let L_vec = Vec::with_capacity(nm);
        let R_vec = Vec::with_capacity(nm);
        let weighted_inner_product_proof = 
            WeightedInnerProdArg::prove(&g_vec, &h_vec, &G, &H, &A_hat, &aL_hat, &aR_hat, &alpha_hat, &y_bn, L_vec, R_vec);

        return RangeProofWIP {
            A,
            weighted_inner_product_proof,
        }   
    }

    pub fn verify(
        &self,
        stmt: StatementRP,
        ped_com: &[GE],
    ) -> Result<(), Errors> {

        let bit_length = stmt.bit_length;
        let num_of_proofs = ped_com.len();
        let nm = num_of_proofs * bit_length;

        let g_vec = stmt.g_vec.to_vec();
        let h_vec = stmt.h_vec.to_vec();
        let G = stmt.G;
        let H = stmt.H;

        let two = BigInt::from(2);
        let one = BigInt::from(1);
        let order = FE::q();

        let y = HSha256::create_hash_from_ge(&[&self.A]);
        let y_bn = y.to_big_int();
        let base_point: GE = ECPoint::generator();
        let yG: GE = base_point * &y;
        let z = HSha256::create_hash_from_ge(&[&self.A, &yG]);
        let z_bn = z.to_big_int();
        let z_sq_bn = BigInt::mod_mul(&z_bn, &z_bn, &order);
        
        // y_vec = (y, y^2, ..., y^{nm})
        let y_powers = iterate(y_bn.clone(), |i| BigInt::mod_mul(&i, &y_bn, &order))
            .take(nm)
            .collect::<Vec<BigInt>>();
        let mut y_powers_rev = y_powers.clone();
        y_powers_rev.reverse();

        // vec_2n = (1, 2, 4, ..., 2^{n-1})
        let vec_2n = iterate(one.clone(), |i| i.clone() * &two)
            .take(bit_length)
            .collect::<Vec<BigInt>>();

        // vec_z2m = (z^2, z^4, ..., z^{2m})
        let vec_z2m = iterate(z_sq_bn.clone(), |i| i.clone() * &z_sq_bn)
            .take(num_of_proofs)
            .collect::<Vec<BigInt>>();

        // d = z^2 d1 + z^4 d2 + ... + z^{2m} dm
        let d = (0..nm)
            .map(|i| {
                let k = i % bit_length;
                let two_i = vec_2n[k].clone();
                let j = i / bit_length;
                let z_2j = vec_z2m[j].clone();
                BigInt::mod_mul(&two_i, &z_2j, &order)
            })
            .collect::<Vec<BigInt>>();

        // compute exponent of g
        let y_pow = BigInt::mod_pow(&y_bn, &BigInt::from((nm + 1) as u32), &order);
        let scalar_G = (0..nm)
            .map(|i| {
                let z_minus_z2 = BigInt::mod_sub(&z_bn, &z_sq_bn, &order);
                let yi_z_minus_z2 = BigInt::mod_mul(&z_minus_z2, &y_powers[i].clone(), &order);
                let z_y_pow = BigInt::mod_mul(&z_bn, &y_pow, &order);
                let di_z_y_pow = BigInt::mod_mul(&d[i], &z_y_pow, &order);
                BigInt::mod_sub(&yi_z_minus_z2, &di_z_y_pow, &order)
            })
            .fold(BigInt::zero(), |acc, x| BigInt::mod_add(&acc, &x, &order));

        // compute exponents of g_vec
        let scalars_g_vec = (0..nm)
            .map(|_| {
                BigInt::mod_sub(&BigInt::zero(), &z_bn, &order)
            })
            .collect::<Vec<BigInt>>();

        // compute exponents of h_vec
        let scalars_h_vec = (0..nm)
            .map(|i| {
                let di_yi_rev = BigInt::mod_mul(&d[i], &y_powers_rev[i].clone(), &order);
                BigInt::mod_add(&di_yi_rev, &z_bn, &order)
            })
            .collect::<Vec<BigInt>>();
        
        // compute product of commitments
        let sum_com = (0..num_of_proofs)
            .map(|i| {
                let y_pow_z2i = BigInt::mod_mul(&y_pow, &vec_z2m[i].clone(), &order);
                ped_com[i] * &ECScalar::from(&y_pow_z2i)
            })  
            .fold(self.A, |acc,x| acc + x as GE);

        // compute A_hat
        let mut A_hat_scalars: Vec<BigInt> = Vec::with_capacity(2*nm + 2);
        A_hat_scalars.extend_from_slice(&scalars_g_vec);
        A_hat_scalars.extend_from_slice(&scalars_h_vec);
        A_hat_scalars.extend_from_slice(&[scalar_G.clone()]);

        let mut A_hat_bases: Vec<GE> = Vec::with_capacity(2*nm + 2);
        A_hat_bases.extend_from_slice(&g_vec);
        A_hat_bases.extend_from_slice(&h_vec);
        A_hat_bases.extend_from_slice(&[G]);

        let A_hat = (0..(2*nm + 1))
            .map(|i| A_hat_bases[i] * &ECScalar::from(&A_hat_scalars[i]))
            .fold(sum_com.clone(), |acc, x| acc + x as GE);
        
        let verify = self.weighted_inner_product_proof.fast_verify(&g_vec, &h_vec, &G, &H, &A_hat, &y_bn);
        if verify.is_ok() {
            Ok(())
        } else {
            Err(RangeProofError)
        }
    }
}

#[cfg(test)]
mod tests {
    use curv::arithmetic::traits::{Samplable};
    use curv::elliptic::curves::traits::*;
    use curv::BigInt;
    use curv::{FE, GE};
    use proofs::range_proof_wip::{RangeProofWIP, StatementRP};

    pub fn test_helper(
        seed: &BigInt, 
        n: usize, 
        m: usize) {
            // generate stmt
            let stmt = StatementRP::generate_bases(&seed, m, n);
    
            // generate witness
            let G = stmt.G;
            let H = stmt.H;
            let range = BigInt::from(2).pow(n as u32);
            let v_vec = (0..m)
                .map(|_| ECScalar::from(&BigInt::sample_below(&range)))
                .collect::<Vec<FE>>();
    
            let r_vec = (0..m).map(|_| ECScalar::new_random()).collect::<Vec<FE>>();
    
            let ped_com_vec = (0..m)
                .map(|i| {
                    let ped_com = &G * &v_vec[i] + &H * &r_vec[i];
                    ped_com
                })
                .collect::<Vec<GE>>();
    
            // simulate range proof
            let range_proof_wip = RangeProofWIP::prove(stmt.clone(), v_vec, &r_vec);
            let result = RangeProofWIP::verify(&range_proof_wip, stmt.clone(), &ped_com_vec);
            assert!(result.is_ok());  
    }

    #[test]
    pub fn test_batch_4_wip_range_proof_32() {
        let n = 32;
        // num of proofs
        let m = 4;
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from(KZen);

        let stmt = StatementRP::generate_bases(&kzen_label, m, n);

        // generate witness
        let G = stmt.G;
        let H = stmt.H;
        let range = BigInt::from(2).pow(n as u32);
        let v_vec = (0..m)
            .map(|_| ECScalar::from(&BigInt::sample_below(&range)))
            .collect::<Vec<FE>>();

        let r_vec = (0..m).map(|_| ECScalar::new_random()).collect::<Vec<FE>>();

        let ped_com_vec = (0..m)
            .map(|i| {
                let ped_com = &G * &v_vec[i] + &H * &r_vec[i];
                ped_com
            })
            .collect::<Vec<GE>>();

        let range_proof_wip = RangeProofWIP::prove(stmt.clone(), v_vec, &r_vec);
        let result = RangeProofWIP::verify(&range_proof_wip, stmt.clone(), &ped_com_vec);
        assert!(result.is_ok());
    }

    #[test]
    #[should_panic]
    pub fn test_batch_4_wip_range_proof_32_out_of_range() {
        let n = 32;
        // num of proofs
        let m = 4;
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from(KZen);

        let stmt = StatementRP::generate_bases(&kzen_label, m, n);

        // generate witness
        let G = stmt.G;
        let H = stmt.H;
        let range = BigInt::from(2).pow(n as u32);
        let mut v_vec = (0..m - 1)
            .map(|_| ECScalar::from(&BigInt::sample_below(&range)))
            .collect::<Vec<FE>>();

        let bad_v = BigInt::from(2).pow(33);
        v_vec.push(ECScalar::from(&bad_v));

        let r_vec = (0..m).map(|_| ECScalar::new_random()).collect::<Vec<FE>>();

        let ped_com_vec = (0..m)
            .map(|i| {
                let ped_com = &G * &v_vec[i] + &H * &r_vec[i];
                ped_com
            })
            .collect::<Vec<GE>>();

        let range_proof_wip = RangeProofWIP::prove(stmt.clone(), v_vec, &r_vec);
        let result = RangeProofWIP::verify(&range_proof_wip, stmt.clone(), &ped_com_vec);
        assert!(result.is_ok());
    }

    #[test]
    pub fn test_batch_2_wip_range_proof_16() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from(KZen);
        test_helper(&kzen_label, 16, 2);
    }

    #[test]
    pub fn test_batch_1_wip_range_proof_8() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from(KZen);
        test_helper(&kzen_label, 8, 1);
    }
}
