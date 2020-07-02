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
//
// Bulletproofs (https://eprint.iacr.org/2017/1066) uses the inner product argument.
// Bulletproofs+ (https://eprint.iacr.org/2020/735.pdf) uses the weighted inner product argument
// which reduces the overall prover communication by ~15%
// 
use curv::arithmetic::traits::Modulo;
use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
use curv::cryptographic_primitives::hashing::traits::*;
use curv::elliptic::curves::traits::*;
use curv::BigInt;
use curv::{FE, GE};
use itertools::iterate;

use Errors::{self, WeightedInnerProdError};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WeightedInnerProdArg {
    L: Vec<GE>,
    R: Vec<GE>,
    a_tag: GE,
    b_tag: GE,
    r_prime: BigInt,
    s_prime: BigInt,
    delta_prime: BigInt,
}

impl WeightedInnerProdArg {
    pub fn prove(
        G: &[GE],
        H: &[GE],
        g: &GE,
        h: &GE,
        P: &GE,
        a: &[BigInt],
        b: &[BigInt],
        alpha: &BigInt,
        y: &BigInt,
        mut L_vec: Vec<GE>,
        mut R_vec: Vec<GE>,
    ) -> WeightedInnerProdArg {
        let n = G.len();
        let order = FE::q();

        // All of the input vectors must have the same length.
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert!(n.is_power_of_two());

        // compute powers of y
        let y_inv = BigInt::mod_inv(&y, &order);
        let powers_y = iterate(y.clone(), |i| i.clone() * y)
            .take(n)
            .collect::<Vec<BigInt>>();
        let powers_yinv = iterate(y_inv.clone(), |i| i.clone() * y_inv.clone())
            .take(n)
            .collect::<Vec<BigInt>>();

        //   let mut L_vec = Vec::with_capacity(n);
        //   let mut R_vec = Vec::with_capacity(n);
        if n != 1 {
            let n = n / 2;

            // we use notation a_L for the left half of vector a and so on
            // Note: Bulletproofs+ paper uses (a_1, a_2) for (a_L, a_R) 
            let (a_L, a_R) = a.split_at(n);
            let (b_L, b_R) = b.split_at(n);
            let (G_L, G_R) = G.split_at(n);
            let (H_L, H_R) = H.split_at(n);

            let yn_aR = (0..n)
                .map(|i| BigInt::mod_mul(&powers_y[n - 1], &a_R[i], &order))
                .collect::<Vec<BigInt>>();
            let yninv_aL = (0..n)
                .map(|i| BigInt::mod_mul(&powers_yinv[n - 1], &a_L[i], &order))
                .collect::<Vec<BigInt>>();

            let c_L = weighted_inner_product(&a_L, &b_R, y.clone());
            let c_R = weighted_inner_product(&yn_aR, b_L, y.clone());

            // Note that no element in vectors a_L and b_R can be 0
            // since 0 is an invalid secret key!
            //
            // L = <yninv_aL * G_R> + <b_R * H_L> + (c_L * g) + (d_L * h)
            let c_L_fe: FE = ECScalar::from(&c_L);
            let g_cL: GE = g * &c_L_fe;
            let d_L_fe: FE = ECScalar::new_random();
            let h_dL = h * &d_L_fe;
            let g_cL_h_dL = g_cL.add_point(&h_dL.get_element());
            let yninv_aL_GR = G_R.iter().zip(yninv_aL.clone()).fold(g_cL_h_dL, |acc, x| {
                if x.1 != BigInt::zero() {
                    let aLi: FE = ECScalar::from(&x.1);
                    let aLi_GRi: GE = x.0 * &aLi;
                    acc.add_point(&aLi_GRi.get_element())
                } else {
                    acc
                }
            });
            let L = H_L.iter().zip(b_R.clone()).fold(yninv_aL_GR, |acc, x| {
                if x.1 != &BigInt::zero() {
                    let bRi: FE = ECScalar::from(&x.1);
                    let bRi_HLi: GE = x.0 * &bRi;
                    acc.add_point(&bRi_HLi.get_element())
                } else {
                    acc
                }
            });

            // Note that no element in vectors a_R and b_L can be 0
            // since 0 is an invalid secret key!
            //
            // R = <yn_aR * G_R> + <b_R * H_L> + (c_R * g) + (d_R * h)
            let c_R_fe: FE = ECScalar::from(&c_R);
            let g_cR: GE = g * &c_R_fe;
            let d_R_fe: FE = ECScalar::new_random();
            let h_dR = h * &d_R_fe;
            let g_cR_h_dR = g_cR.add_point(&h_dR.get_element());
            let aR_GL = G_L.iter().zip(yn_aR.clone()).fold(g_cR_h_dR, |acc, x| {
                if x.1 != BigInt::zero() {
                    let aRi: FE = ECScalar::from(&x.1);
                    let aRi_GLi: GE = x.0 * &aRi;
                    acc.add_point(&aRi_GLi.get_element())
                } else {
                    acc
                }
            });
            let R = H_R.iter().zip(b_L.clone()).fold(aR_GL, |acc, x| {
                if x.1 != &BigInt::zero() {
                    let bLi: FE = ECScalar::from(&x.1);
                    let bLi_HRi: GE = x.0 * &bLi;
                    acc.add_point(&bLi_HRi.get_element())
                } else {
                    acc
                }
            });

            // the challenges in pre-final rounds are used as [x_1, x_2, ...]
            // to avoid confusion with the challenge `e` in last round
            let x = HSha256::create_hash_from_ge(&[&L, &R, &g, &h]);
            let x_bn = x.to_big_int();
            let x_sq_bn = BigInt::mod_mul(&x_bn, &x_bn, &order);
            let x_sq_inv_bn = BigInt::mod_inv(&x_sq_bn, &order);
            let x_inv_fe = x.invert();

            let a_hat = (0..n)
                .map(|i| {
                    let aLx = BigInt::mod_mul(&a_L[i], &x_bn, &order);
                    let aR_minusx = BigInt::mod_mul(&yn_aR[i], &x_inv_fe.to_big_int(), &order);
                    BigInt::mod_add(&aLx, &aR_minusx, &order)
                })
                .collect::<Vec<BigInt>>();
            //   a = &mut a_hat[..];

            let b_hat = (0..n)
                .map(|i| {
                    let bRx = BigInt::mod_mul(&b_R[i], &x_bn, &order);
                    let bL_minusx = BigInt::mod_mul(&b_L[i], &x_inv_fe.to_big_int(), &order);
                    BigInt::mod_add(&bRx, &bL_minusx, &order)
                })
                .collect::<Vec<BigInt>>();
            //    b = &mut b_hat[..];

            let x2_dL = BigInt::mod_mul(&x_sq_bn, &d_L_fe.to_big_int(), &order);
            let xinv2_dR = BigInt::mod_mul(&x_sq_inv_bn, &d_R_fe.to_big_int(), &order);
            let x2_dL_xinv2_dR = BigInt::mod_add(&x2_dL, &xinv2_dR, &order);
            let alpha_hat = BigInt::mod_add(&alpha, &x2_dL_xinv2_dR, &order);

            let x_yinv = BigInt::mod_mul(&x_bn, &powers_yinv[n - 1], &order);
            let x_yinv_fe = ECScalar::from(&x_yinv);
            let G_hat = (0..n)
                .map(|i| {
                    let GLx_inv = &G_L[i] * &x_inv_fe;
                    let GRx_yinv = &G_R[i] * &x_yinv_fe;
                    GRx_yinv + GLx_inv
                })
                .collect::<Vec<GE>>();
            //   G = &mut G_hat[..];

            let H_hat = (0..n)
                .map(|i| {
                    let HLx = &H_L[i] * &x;
                    let HRx_inv = &H_R[i] * &x_inv_fe;
                    HLx + HRx_inv
                })
                .collect::<Vec<GE>>();
            //    H = &mut H_hat[..];

            L_vec.push(L);
            R_vec.push(R);
            return WeightedInnerProdArg::prove(
                &G_hat, &H_hat, &g, &h, &P, &a_hat, &b_hat, &alpha_hat, &y, L_vec, R_vec,
            );
        } else {
            let r: FE = ECScalar::new_random();
            let r_bn: BigInt = r.to_big_int();
            let s: FE = ECScalar::new_random();
            let s_bn: BigInt = s.to_big_int();
            let delta: FE = ECScalar::new_random();
            let delta_bn: BigInt = delta.to_big_int();
            let eta: FE = ECScalar::new_random();
            let eta_bn: BigInt = eta.to_big_int();

            // compute A
            let Gr = &G[0] * &r;
            let Hs = &H[0] * &s;
            let a_s = BigInt::mod_mul(&a[0], &s_bn, &order);
            let a_sy = BigInt::mod_mul(&a_s, &y, &order);
            let b_r = BigInt::mod_mul(&b[0], &r_bn, &order);
            let b_ry = BigInt::mod_mul(&b_r, &y, &order);
            let a_sy_b_ry = BigInt::mod_add(&a_sy, &b_ry, &order);
            let g_a_sy_b_ry = g * &ECScalar::from(&a_sy_b_ry);
            let h_delta = h * &delta;
            let A = Gr + Hs + g_a_sy_b_ry + h_delta;

            // compute B
            let r_s = BigInt::mod_mul(&r_bn, &s_bn, &order);
            let r_sy = BigInt::mod_mul(&y, &r_s, &order);
            let g_r_sy = g * &ECScalar::from(&r_sy);
            let h_eta = h * &eta;
            let B = g_r_sy + h_eta;

            // compute challenge e
            // let lg_n = L_vec.len();
            let e = HSha256::create_hash_from_ge(&[&A, &B, &g, &h]);
            let e_bn = e.to_big_int();
            let e_sq_bn = BigInt::mod_mul(&e_bn, &e_bn, &order);

            // compute r_prime, s_prime, delta_prime
            let ax = BigInt::mod_mul(&a[0], &e_bn, &order);
            let bx = BigInt::mod_mul(&b[0], &e_bn, &order);
            let r_prime = BigInt::mod_add(&r_bn, &ax, &order);
            let s_prime = BigInt::mod_add(&s_bn, &bx, &order);

            let deltax = BigInt::mod_mul(&delta_bn, &e_bn, &order);
            let alpha_x2 = BigInt::mod_mul(&alpha, &e_sq_bn, &order);
            let deltax_alpha_x2 = BigInt::mod_add(&deltax, &alpha_x2, &order);
            let delta_prime = BigInt::mod_add(&eta_bn, &deltax_alpha_x2, &order);

            return WeightedInnerProdArg {
                L: L_vec,
                R: R_vec,
                a_tag: A,
                b_tag: B,
                r_prime: r_prime,
                s_prime: s_prime,
                delta_prime: delta_prime,
            };
        }
    }

    pub fn verify(
        &self,
        g_vec: &[GE],
        hi_tag: &[GE],
        g: &GE,
        h: &GE,
        P: &GE,
        y: &BigInt,
    ) -> Result<(), Errors> {
        let G = &g_vec[..];
        let H = &hi_tag[..];
        let n = G.len();
        let order = FE::q();

        // All of the input vectors must have the same length.
        assert_eq!(H.len(), n);
        assert!(n.is_power_of_two());

        // compute powers of y
        let y_inv = BigInt::mod_inv(&y, &order);
        let powers_yinv = iterate(y_inv.clone(), |i| i.clone() * y_inv.clone())
            .take(n)
            .collect::<Vec<BigInt>>();

        if n != 1 {
            let n = n / 2;
            let (G_L, G_R) = G.split_at(n);
            let (H_L, H_R) = H.split_at(n);

            let x = HSha256::create_hash_from_ge(&[&self.L[0], &self.R[0], &g, &h]);
            let x_bn = x.to_big_int();
            let order = FE::q();
            let x_inv_fe = x.invert();
            let x_sq_bn = BigInt::mod_mul(&x_bn, &x_bn, &order);
            let x_inv_sq_bn =
                BigInt::mod_mul(&x_inv_fe.to_big_int(), &x_inv_fe.to_big_int(), &order);
            let x_sq_fe: FE = ECScalar::from(&x_sq_bn);
            let x_inv_sq_fe: FE = ECScalar::from(&x_inv_sq_bn);

            let x_yinv = BigInt::mod_mul(&x_bn, &powers_yinv[n - 1], &order);
            let x_yinv_fe = ECScalar::from(&x_yinv);
            let G_hat = (0..n)
                .map(|i| {
                    let GLx_inv = &G_L[i] * &x_inv_fe;
                    let GRx_yinv = &G_R[i] * &x_yinv_fe;
                    GRx_yinv + GLx_inv
                })
                .collect::<Vec<GE>>();
            //   G = &mut G_hat[..];

            let H_hat = (0..n)
                .map(|i| {
                    let HLx = &H_L[i] * &x;
                    let HRx_inv = &H_R[i] * &x_inv_fe;
                    HLx + HRx_inv
                })
                .collect::<Vec<GE>>();
            //    H = &mut H_hat[..];

            let Lx_sq = &self.L[0] * &x_sq_fe;
            let Rx_sq_inv = &self.R[0] * &x_inv_sq_fe;
            let P_tag = Lx_sq + Rx_sq_inv + P;

            let ip = WeightedInnerProdArg {
                L: (&self.L[1..]).to_vec(),
                R: (&self.R[1..]).to_vec(),
                a_tag: self.a_tag.clone(),
                b_tag: self.b_tag.clone(),
                r_prime: self.r_prime.clone(),
                s_prime: self.s_prime.clone(),
                delta_prime: self.delta_prime.clone(),
            };
            return ip.verify(&G_hat, &H_hat, g, h, &P_tag, &y);
        }

        // compute challenge e
        let e = HSha256::create_hash_from_ge(&[&self.a_tag, &self.b_tag, &g, &h]);
        let e_bn = e.to_big_int();
        let e_sq_bn = BigInt::mod_mul(&e_bn, &e_bn, &order);
        let e_sq_fe: FE = ECScalar::from(&e_sq_bn);

        // left hand side of verification
        // LHS = e^2*P + e*A + B
        let P_e2 = P * &e_sq_fe;
        let Ae = self.a_tag * &e;
        let left = P_e2 + Ae + self.b_tag;

        // RHS = (er')*G + (es')*H + (r's'y)*g + (delta')*h
        let er_prime = BigInt::mod_mul(&e_bn, &self.r_prime, &order);
        let Ger_prime = &G[0] * &ECScalar::from(&er_prime);
        let es_prime = BigInt::mod_mul(&e_bn, &self.s_prime, &order);
        let Hes_prime = &H[0] * &ECScalar::from(&es_prime);
        let rs_prime = BigInt::mod_mul(&self.s_prime, &self.r_prime, &order);
        let yrs_prime = BigInt::mod_mul(&rs_prime, &y, &order);
        let g_yrs_prime = g * &ECScalar::from(&yrs_prime);
        let h_delta_prime = h * &ECScalar::from(&self.delta_prime);
        let right = Ger_prime + Hes_prime + g_yrs_prime + h_delta_prime;

        if left == right {
            Ok(())
        } else {
            Err(WeightedInnerProdError)
        }
    }

    ///
    /// Returns Ok() if the given inner product satisfies the verification equations,
    /// else returns `WeightedInnerProdErrorError`.
    ///
    /// Uses a single multiexponentiation (multiscalar multiplication in additive notation)
    /// check to verify an inner product proof.
    ///
    pub fn fast_verify(
        &self,
        g_vec: &[GE],
        hi_tag: &[GE],
        g: &GE,
        h: &GE,
        P: &GE,
        y: &BigInt,
    ) -> Result<(), Errors> {
        let G = &g_vec[..];
        let H = &hi_tag[..];
        let n = G.len();
        let order = FE::q();

        // All of the input vectors must have the same length.
        assert_eq!(H.len(), n);
        assert!(n.is_power_of_two());

        // compute powers of y
        let y_inv = BigInt::mod_inv(&y, &order);
        let powers_yinv = iterate(y_inv.clone(), |i| i.clone() * y_inv.clone())
            .take(n)
            .collect::<Vec<BigInt>>();

        let lg_n = self.L.len();
        assert!(
            lg_n <= 64,
            "Not compatible for vector sizes greater than 2^64!"
        );

        // compute challenge e
        let e = HSha256::create_hash_from_ge(&[&self.a_tag, &self.b_tag, &g, &h]);
        let e_bn = e.to_big_int();
        let e_sq_bn = BigInt::mod_mul(&e_bn, &e_bn, &order);

        let mut x_sq_vec: Vec<BigInt> = Vec::with_capacity(lg_n);
        let mut minus_e_sq_x_sq_vec: Vec<BigInt> = Vec::with_capacity(lg_n);
        let mut minus_e_sq_x_inv_sq_vec: Vec<BigInt> = Vec::with_capacity(lg_n);
        let mut allinv = BigInt::one();
        let mut all = BigInt::one();
        for (Li, Ri) in self.L.iter().zip(self.R.iter()) {
            let x = HSha256::create_hash_from_ge(&[&Li, &Ri, &g, &h]);
            let x_bn = x.to_big_int();
            let x_inv_fe = x.invert();
            let x_inv_bn = x_inv_fe.to_big_int();
            let x_sq_bn = BigInt::mod_mul(&x_bn, &x_bn, &order);
            let x_inv_sq_bn =
                BigInt::mod_mul(&x_inv_fe.to_big_int(), &x_inv_fe.to_big_int(), &order);
            let e_sq_x_sq_bn = BigInt::mod_mul(&e_sq_bn, &x_sq_bn, &order);
            let e_sq_x_inv_sq_bn = BigInt::mod_mul(&e_sq_bn, &x_inv_sq_bn, &order);

            x_sq_vec.push(x_sq_bn.clone());
            minus_e_sq_x_sq_vec.push(BigInt::mod_sub(&BigInt::zero(), &e_sq_x_sq_bn, &order));
            minus_e_sq_x_inv_sq_vec.push(BigInt::mod_sub(
                &BigInt::zero(),
                &e_sq_x_inv_sq_bn,
                &order,
            ));
            allinv = allinv * x_inv_bn;
            all = all * x_bn;
        }

        let mut s: Vec<BigInt> = Vec::with_capacity(n);
        let mut sg: Vec<BigInt> = Vec::with_capacity(n);
        let mut sh: Vec<BigInt> = Vec::with_capacity(n);
        s.push(allinv.clone());
        sg.push(allinv.clone());
        sh.push(all.clone());
        for i in 1..n {
            let lg_i =
                (std::mem::size_of_val(&n) * 8) - 1 - ((i as usize).leading_zeros() as usize);
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [x_k,...,x_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let x_lg_i_sq = x_sq_vec[(lg_n - 1) - lg_i].clone();
            s.push(s[i - k].clone() * x_lg_i_sq);
            let s_inv_i = BigInt::mod_inv(&s[i], &order);
            let si_yi = BigInt::mod_mul(&s[i], &powers_yinv[i - 1], &order);

            sg.push(si_yi);
            sh.push(s_inv_i);
        }

        // Scalar exponent of LHS
        let er_times_sg: Vec<BigInt> = (0..n)
            .map(|i| {
                let e_sg_i = BigInt::mod_mul(&e_bn, &sg[i], &order);
                BigInt::mod_mul(&self.r_prime, &e_sg_i, &order)
            })
            .collect();
        let es_times_sg: Vec<BigInt> = (0..n)
            .map(|i| {
                let e_sh_i = BigInt::mod_mul(&e_bn, &sh[i], &order);
                BigInt::mod_mul(&self.s_prime, &e_sh_i, &order)
            })
            .collect();
        let r_times_s = BigInt::mod_mul(&self.r_prime, &self.s_prime, &order);
        let r_times_s_y = BigInt::mod_mul(&r_times_s, &y, &order);

        let mut scalars: Vec<BigInt> = Vec::with_capacity(2 * n + 2 * lg_n + 1);
        scalars.extend_from_slice(&er_times_sg);
        scalars.extend_from_slice(&es_times_sg);
        scalars.extend_from_slice(&minus_e_sq_x_sq_vec);
        scalars.extend_from_slice(&minus_e_sq_x_inv_sq_vec);
        scalars.push(r_times_s_y);

        let mut points: Vec<GE> = Vec::with_capacity(2 * n + 2 * lg_n + 1);
        points.extend_from_slice(g_vec);
        points.extend_from_slice(hi_tag);
        points.extend_from_slice(&self.L);
        points.extend_from_slice(&self.R);
        points.push(*g);

        let h_delta_prime = h * &ECScalar::from(&self.delta_prime);
        let tot_len = points.len();
        let lhs = (0..tot_len)
            .map(|i| points[i] * &ECScalar::from(&scalars[i]))
            .fold(h_delta_prime, |acc, x| acc + x as GE);

        let Ae = self.a_tag * &ECScalar::from(&e_bn);
        let Pe_sq = P * &ECScalar::from(&e_sq_bn);
        let rhs = Pe_sq + Ae + self.b_tag;

        if lhs == rhs {
            Ok(())
        } else {
            Err(WeightedInnerProdError)
        }
    }
}

fn weighted_inner_product(a: &[BigInt], b: &[BigInt], y: BigInt) -> BigInt {
    assert_eq!(
        a.len(),
        b.len(),
        "weighted_inner_product(a,b): lengths of vectors do not match"
    );
    let order = FE::q();
    let y_powers = iterate(y.clone(), |i| i.clone() * y.clone())
            .take(a.len())
            .collect::<Vec<BigInt>>();
    let n = a.len();
    let out = (0..n)
        .map(|i| {
            let aibi = BigInt::mod_mul(&a[i], &b[i], &order);
            BigInt::mod_mul(&aibi, &y_powers[i], &order)
        })
        .fold(BigInt::zero(), |acc, x| BigInt::mod_add(&acc, &x, &order));

    return out;
}

#[cfg(test)]
mod tests {
    use curv::arithmetic::traits::{Converter, Modulo};
    use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
    use curv::cryptographic_primitives::hashing::hash_sha512::HSha512;
    use curv::cryptographic_primitives::hashing::traits::*;
    use curv::elliptic::curves::traits::*;
    use curv::BigInt;
    use curv::{FE, GE};
    use proofs::range_proof::generate_random_point;
    use proofs::weighted_inner_product::WeightedInnerProdArg;
    use proofs::weighted_inner_product::{weighted_inner_product};
    use itertools::iterate;

    fn test_helper(n: usize) {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from(KZen);

        let g_vec = (0..n)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = HSha512::create_hash(&[&kzen_label_i]);
                generate_random_point(&Converter::to_vec(&hash_i))
            })
            .collect::<Vec<GE>>();

        // can run in parallel to g_vec:
        let h_vec = (0..n)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = HSha512::create_hash(&[&kzen_label_j]);
                generate_random_point(&Converter::to_vec(&hash_j))
            })
            .collect::<Vec<GE>>();

        let label = BigInt::from(2);
        let hash = HSha512::create_hash(&[&label]);
        let g = generate_random_point(&Converter::to_vec(&hash));
        let label = BigInt::from(3);
        let hash = HSha512::create_hash(&[&label]);
        let h = generate_random_point(&Converter::to_vec(&hash));

        let a: Vec<_> = (0..n)
            .map(|_| {
                let rand: FE = ECScalar::new_random();
                rand.to_big_int()
            })
            .collect();

        let b: Vec<_> = (0..n)
            .map(|_| {
                let rand: FE = ECScalar::new_random();
                rand.to_big_int()
            })
            .collect();

        let y_scalar: BigInt =
            HSha256::create_hash_from_slice("Seed string decided by P,V!".as_bytes());
        let c = super::weighted_inner_product(&a, &b, y_scalar.clone());

        let alpha_fe: FE = ECScalar::new_random();
        let alpha = alpha_fe.to_big_int();

        let y: FE = ECScalar::new_random();
        let order = FE::q();
        let yi = (0..n)
            .map(|i| BigInt::mod_pow(&y.to_big_int(), &BigInt::from(i as u32), &order))
            .collect::<Vec<BigInt>>();

        let yi_inv = (0..n)
            .map(|i| {
                let yi_fe: FE = ECScalar::from(&yi[i]);
                yi_fe.invert()
            })
            .collect::<Vec<FE>>();

        let hi_tag = (0..n).map(|i| &h_vec[i] * &yi_inv[i]).collect::<Vec<GE>>();

        // R = <a * G> + <b_L * H_R> + c * g + alpha*h
        let c_fe: FE = ECScalar::from(&c);
        let g_c: GE = &g * &c_fe;
        let h_alpha: GE = &h * &alpha_fe;
        let gc_halpha = g_c + h_alpha;
        let a_G = (0..n)
            .map(|i| {
                let ai: FE = ECScalar::from(&a[i]);
                &g_vec[i] * &ai
            })
            .fold(gc_halpha, |acc, x: GE| acc + x as GE);
        let P = (0..n)
            .map(|i| {
                let bi: FE = ECScalar::from(&b[i]);
                &hi_tag[i] * &bi
            })
            .fold(a_G, |acc, x: GE| acc + x as GE);

        let L_vec = Vec::with_capacity(n);
        let R_vec = Vec::with_capacity(n);
        let ipp =
            WeightedInnerProdArg::prove(&g_vec, &hi_tag, &g, &h, &P, &a, &b, &alpha, &y_scalar, L_vec, R_vec);
        let verifier = ipp.verify(&g_vec, &hi_tag, &g, &h, &P, &y_scalar);
        assert!(verifier.is_ok())
    }

    fn test_helper_fast_verify(n: usize) {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from(KZen);

        let g_vec = (0..n)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = HSha512::create_hash(&[&kzen_label_i]);
                generate_random_point(&Converter::to_vec(&hash_i))
            })
            .collect::<Vec<GE>>();

        // can run in parallel to g_vec:
        let h_vec = (0..n)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = HSha512::create_hash(&[&kzen_label_j]);
                generate_random_point(&Converter::to_vec(&hash_j))
            })
            .collect::<Vec<GE>>();

        let label = BigInt::from(2);
        let hash = HSha512::create_hash(&[&label]);
        let g = generate_random_point(&Converter::to_vec(&hash));
        let label = BigInt::from(3);
        let hash = HSha512::create_hash(&[&label]);
        let h = generate_random_point(&Converter::to_vec(&hash));

        let a: Vec<_> = (0..n)
            .map(|_| {
                let rand: FE = ECScalar::new_random();
                rand.to_big_int()
            })
            .collect();

        let b: Vec<_> = (0..n)
            .map(|_| {
                let rand: FE = ECScalar::new_random();
                rand.to_big_int()
            })
            .collect();

        let y_scalar: BigInt =
            HSha256::create_hash_from_slice("Seed string decided by P,V!".as_bytes());
        let c = super::weighted_inner_product(&a, &b, y_scalar.clone());

        let alpha_fe: FE = ECScalar::new_random();
        let alpha = alpha_fe.to_big_int();

        let y: FE = ECScalar::new_random();
        let order = FE::q();
        let yi = (0..n)
            .map(|i| BigInt::mod_pow(&y.to_big_int(), &BigInt::from(i as u32), &order))
            .collect::<Vec<BigInt>>();

        let yi_inv = (0..n)
            .map(|i| {
                let yi_fe: FE = ECScalar::from(&yi[i]);
                yi_fe.invert()
            })
            .collect::<Vec<FE>>();

        let hi_tag = (0..n).map(|i| &h_vec[i] * &yi_inv[i]).collect::<Vec<GE>>();

        // R = <a * G> + <b_L * H_R> + c * g + alpha*h
        let c_fe: FE = ECScalar::from(&c);
        let g_c: GE = &g * &c_fe;
        let h_alpha: GE = &h * &alpha_fe;
        let gc_halpha = g_c + h_alpha;
        let a_G = (0..n)
            .map(|i| {
                let ai: FE = ECScalar::from(&a[i]);
                &g_vec[i] * &ai
            })
            .fold(gc_halpha, |acc, x: GE| acc + x as GE);
        let P = (0..n)
            .map(|i| {
                let bi: FE = ECScalar::from(&b[i]);
                &hi_tag[i] * &bi
            })
            .fold(a_G, |acc, x: GE| acc + x as GE);

        let L_vec = Vec::with_capacity(n);
        let R_vec = Vec::with_capacity(n);
        let ipp =
            WeightedInnerProdArg::prove(&g_vec, &hi_tag, &g, &h, &P, &a, &b, &alpha, &y_scalar, L_vec, R_vec);
        let verifier = ipp.fast_verify(&g_vec, &hi_tag, &g, &h, &P, &y_scalar);
        assert!(verifier.is_ok())
    }

    fn test_helper_non_power_2(m: usize, n: usize, a: &[BigInt], b: &[BigInt]) {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from(KZen);

        let g_vec = (0..n)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = HSha512::create_hash(&[&kzen_label_i]);
                generate_random_point(&Converter::to_vec(&hash_i))
            })
            .collect::<Vec<GE>>();

        // can run in parallel to g_vec:
        let h_vec = (0..n)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = HSha512::create_hash(&[&kzen_label_j]);
                generate_random_point(&Converter::to_vec(&hash_j))
            })
            .collect::<Vec<GE>>();

        // generate g, h
        let label = BigInt::from(2);
        let hash = HSha512::create_hash(&[&label]);
        let g = generate_random_point(&Converter::to_vec(&hash));
        let label = BigInt::from(3);
        let hash = HSha512::create_hash(&[&label]);
        let h = generate_random_point(&Converter::to_vec(&hash));

        let y_scalar: BigInt =
            HSha256::create_hash_from_slice("Seed string decided by P,V!".as_bytes());
        let c = super::weighted_inner_product(&a, &b, y_scalar.clone());

        let alpha_fe: FE = ECScalar::new_random();
        let alpha = alpha_fe.to_big_int();

        let y: FE = ECScalar::new_random();
        let order = FE::q();
        let yi = (0..n)
            .map(|i| BigInt::mod_pow(&y.to_big_int(), &BigInt::from(i as u32), &order))
            .collect::<Vec<BigInt>>();

        let yi_inv = (0..n)
            .map(|i| {
                let yi_fe: FE = ECScalar::from(&yi[i]);
                yi_fe.invert()
            })
            .collect::<Vec<FE>>();

        let hi_tag = (0..n).map(|i| &h_vec[i] * &yi_inv[i]).collect::<Vec<GE>>();

        // R = <a * G> + <b_L * H_R> + c * g + alpha*h
        let c_fe: FE = ECScalar::from(&c);
        let g_c: GE = &g * &c_fe;
        let h_alpha: GE = &h * &alpha_fe;
        let gc_halpha = g_c + h_alpha;
        let a_G = (0..m)
            .map(|i| {
                let ai: FE = ECScalar::from(&a[i]);
                &g_vec[i] * &ai
            })
            .fold(gc_halpha, |acc, x: GE| acc + x as GE);
        let P = (0..m)
            .map(|i| {
                let bi: FE = ECScalar::from(&b[i]);
                &hi_tag[i] * &bi
            })
            .fold(a_G, |acc, x: GE| acc + x as GE);

        let L_vec = Vec::with_capacity(n);
        let R_vec = Vec::with_capacity(n);
        let ipp =
            WeightedInnerProdArg::prove(&g_vec, &hi_tag, &g, &h, &P, &a, &b, &alpha, &y_scalar, L_vec, R_vec);
        let verifier = ipp.verify(&g_vec, &hi_tag, &g, &h, &P, &y_scalar);
        assert!(verifier.is_ok())
    }

    #[test]
    fn test_wip() {
        let a: Vec<BigInt> = vec![
            BigInt::from(3),
            BigInt::from(2),
            BigInt::from(1),
            BigInt::from(0),
        ];
        let b: Vec<BigInt> = vec![
            BigInt::from(1),
            BigInt::from(2),
            BigInt::from(3),
            BigInt::from(4),
        ];
        let y = BigInt::from(2);

        let y_powers = iterate(y.clone(), |i| i.clone() * y.clone())
            .take(4)
            .collect::<Vec<BigInt>>();
        
        let expect_y_powers = vec![
            BigInt::from(2),
            BigInt::from(4),
            BigInt::from(8),
            BigInt::from(16),
        ];
        assert_eq!(y_powers, expect_y_powers, "Scalar powers of y fails!");

        let a_weighted_b = weighted_inner_product(&a, &b, y.clone());
        assert_eq!(
            a_weighted_b,
            BigInt::from(46),
            "Weighted inner product fails!"
        );
    }

    #[test]
    fn make_wip_32() {
        test_helper(32);
    }

    #[test]
    fn make_wip_16() {
        test_helper(16);
    }
    #[test]
    fn make_wip_8() {
        test_helper(8);
    }

    #[test]
    fn make_wip_4() {
        test_helper(4);
    }

    #[test]
    fn make_wip_2() {
        test_helper(2);
    }

    #[test]
    fn make_wip_1() {
        test_helper(1);
    }

    #[test]
    fn make_wip_32_fast_verify() {
        test_helper_fast_verify(32);
    }

    #[test]
    fn make_wip_16_fast_verify() {
        test_helper_fast_verify(16);
    }
    #[test]
    fn make_wip_8_fast_verify() {
        test_helper_fast_verify(8);
    }

    #[test]
    fn make_wip_4_fast_verify() {
        test_helper_fast_verify(4);
    }

    #[test]
    fn make_wip_2_fast_verify() {
        test_helper_fast_verify(2);
    }

    #[test]
    fn make_wip_1_fast_verify() {
        test_helper_fast_verify(1);
    }

    #[test]
    fn make_wip_non_power_2() {
        // Create random scalar vectors a, b with size non-power of 2
        let n: usize = 9;
        let mut a: Vec<_> = (0..n)
            .map(|_| {
                let rand: FE = ECScalar::new_random();
                rand.to_big_int()
            })
            .collect();

        let mut b: Vec<_> = (0..n)
            .map(|_| {
                let rand: FE = ECScalar::new_random();
                rand.to_big_int()
            })
            .collect();

        // next power of 2
        let _n: usize = n.next_power_of_two();
        let zero_append_vec = vec![BigInt::zero(); _n - n];

        // zero-appending at the end of a, b
        a.extend_from_slice(&zero_append_vec);
        b.extend_from_slice(&zero_append_vec);

        test_helper_non_power_2(n, _n, &a, &b);
    }
}
