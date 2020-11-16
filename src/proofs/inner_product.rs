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
use curv::arithmetic::traits::Modulo;
use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
use curv::cryptographic_primitives::hashing::traits::*;
use curv::elliptic::curves::traits::*;
use curv::BigInt;
type GE = curv::elliptic::curves::secp256_k1::GE;
type FE = curv::elliptic::curves::secp256_k1::FE;


use Errors::{self, InnerProductError};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InnerProductArg {
    pub(super) L: Vec<GE>,
    pub(super) R: Vec<GE>,
    pub(super) a_tag: BigInt,
    pub(super) b_tag: BigInt,
}

impl InnerProductArg {
    pub fn prove(
        G: &[GE],
        H: &[GE],
        ux: &GE,
        P: &GE,
        a: &[BigInt],
        b: &[BigInt],
        mut L_vec: Vec<GE>,
        mut R_vec: Vec<GE>,
    ) -> InnerProductArg {
        let n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert!(n.is_power_of_two());

        //   let mut L_vec = Vec::with_capacity(n);
        //   let mut R_vec = Vec::with_capacity(n);
        if n != 1 {
            let n = n / 2;
            let (a_L, a_R) = a.split_at(n);
            let (b_L, b_R) = b.split_at(n);
            let (G_L, G_R) = G.split_at(n);
            let (H_L, H_R) = H.split_at(n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            // Note that no element in vectors a_L and b_R can be 0
            // since 0 is an invalid secret key!
            //
            // L = <a_L * G_R> + <b_R * H_L> + c_L * ux
            let c_L_fe: FE = ECScalar::from(&c_L);
            let ux_CL: GE = ux * &c_L_fe;
            let aL_GR = G_R.iter().zip(a_L.clone()).fold(ux_CL, |acc, x| {
                if x.1 != &BigInt::zero() {
                    let aLi: FE = ECScalar::from(&x.1);
                    let aLi_GRi: GE = x.0 * &aLi;
                    acc.add_point(&aLi_GRi.get_element())
                } else {
                    acc
                }
            });
            let L = H_L.iter().zip(b_R.clone()).fold(aL_GR, |acc, x| {
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
            // R = <a_R * G_L> + <b_L * H_R> + c_R * ux
            let c_R_fe: FE = ECScalar::from(&c_R);
            let ux_CR: GE = ux * &c_R_fe;
            let aR_GL = G_L.iter().zip(a_R.clone()).fold(ux_CR, |acc, x| {
                if x.1 != &BigInt::zero() {
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

            let x = HSha256::create_hash_from_ge(&[&L, &R, &ux]);
            let x_bn = x.to_big_int();
            let order = FE::q();
            let x_inv_fe = x.invert();

            let a_new = (0..n)
                .map(|i| {
                    let aLx = BigInt::mod_mul(&a_L[i], &x_bn, &order);
                    let aR_minusx = BigInt::mod_mul(&a_R[i], &x_inv_fe.to_big_int(), &order);
                    BigInt::mod_add(&aLx, &aR_minusx, &order)
                })
                .collect::<Vec<BigInt>>();
            //   a = &mut a_new[..];

            let b_new = (0..n)
                .map(|i| {
                    let bRx = BigInt::mod_mul(&b_R[i], &x_bn, &order);
                    let bL_minusx = BigInt::mod_mul(&b_L[i], &x_inv_fe.to_big_int(), &order);
                    BigInt::mod_add(&bRx, &bL_minusx, &order)
                })
                .collect::<Vec<BigInt>>();
            //    b = &mut b_new[..];

            let G_new = (0..n)
                .map(|i| {
                    let GLx_inv = &G_L[i] * &x_inv_fe;
                    let GRx = &G_R[i] * &x;
                    GRx + GLx_inv
                })
                .collect::<Vec<GE>>();
            //   G = &mut G_new[..];

            let H_new = (0..n)
                .map(|i| {
                    let HLx = &H_L[i] * &x;
                    let HRx_inv = &H_R[i] * &x_inv_fe;
                    HLx + HRx_inv
                })
                .collect::<Vec<GE>>();
            //    H = &mut H_new[..];

            L_vec.push(L);
            R_vec.push(R);
            return InnerProductArg::prove(&G_new, &H_new, &ux, &P, &a_new, &b_new, L_vec, R_vec);
        }

        InnerProductArg {
            L: L_vec,
            R: R_vec,
            a_tag: a[0].clone(),
            b_tag: b[0].clone(),
        }
    }

    pub fn verify(&self, g_vec: &[GE], hi_tag: &[GE], ux: &GE, P: &GE) -> Result<(), Errors> {
        let G = &g_vec[..];
        let H = &hi_tag[..];
        let n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert!(n.is_power_of_two());

        if n != 1 {
            let n = n / 2;
            let (G_L, G_R) = G.split_at(n);
            let (H_L, H_R) = H.split_at(n);

            let x = HSha256::create_hash_from_ge(&[&self.L[0], &self.R[0], &ux]);
            let x_bn = x.to_big_int();
            let order = FE::q();
            let x_inv_fe = x.invert();
            let x_sq_bn = BigInt::mod_mul(&x_bn, &x_bn, &order);
            let x_inv_sq_bn =
                BigInt::mod_mul(&x_inv_fe.to_big_int(), &x_inv_fe.to_big_int(), &order);
            let x_sq_fe: FE = ECScalar::from(&x_sq_bn);
            let x_inv_sq_fe: FE = ECScalar::from(&x_inv_sq_bn);

            let G_new = (0..n)
                .map(|i| {
                    let GLx_inv = &G_L[i] * &x_inv_fe;
                    let GRx = &G_R[i] * &x;
                    GRx + GLx_inv
                })
                .collect::<Vec<GE>>();
            //   G = &mut G_new[..];

            let H_new = (0..n)
                .map(|i| {
                    let HLx = &H_L[i] * &x;
                    let HRx_inv = &H_R[i] * &x_inv_fe;
                    HLx + HRx_inv
                })
                .collect::<Vec<GE>>();
            //    H = &mut H_new[..];
            let Lx_sq = &self.L[0] * &x_sq_fe;
            let Rx_sq_inv = &self.R[0] * &x_inv_sq_fe;
            let P_tag = Lx_sq + Rx_sq_inv + P;
            let ip = InnerProductArg {
                L: (&self.L[1..]).to_vec(),
                R: (&self.R[1..]).to_vec(),
                a_tag: self.a_tag.clone(),
                b_tag: self.b_tag.clone(),
            };
            return ip.verify(&G_new, &H_new, ux, &P_tag);
        }

        let a_fe: FE = ECScalar::from(&self.a_tag);
        let b_fe: FE = ECScalar::from(&self.b_tag);
        let c = a_fe.mul(&b_fe.get_element());
        let Ga = &G[0] * &a_fe;
        let Hb = &H[0] * &b_fe;
        let ux_c = ux * &c;
        let P_calc = Ga + Hb + ux_c;
        if P.clone() == P_calc {
            Ok(())
        } else {
            Err(InnerProductError)
        }
    }

    ///
    /// Returns Ok() if the given inner product satisfies the verification equations,
    /// else returns `InnerProductError`.
    ///
    /// Uses a single multiexponentiation (multiscalar multiplication in additive notation)
    /// check to verify an inner product proof.
    ///
    pub fn fast_verify(&self, g_vec: &[GE], hi_tag: &[GE], ux: &GE, P: &GE) -> Result<(), Errors> {
        let G = &g_vec[..];
        let H = &hi_tag[..];
        let n = G.len();
        let order = FE::q();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert!(n.is_power_of_two());

        let lg_n = self.L.len();
        assert!(
            lg_n <= 64,
            "Not compatible for vector sizes greater than 2^64!"
        );

        let mut x_sq_vec: Vec<BigInt> = Vec::with_capacity(lg_n);
        let mut x_inv_sq_vec: Vec<BigInt> = Vec::with_capacity(lg_n);
        let mut minus_x_sq_vec: Vec<BigInt> = Vec::with_capacity(lg_n);
        let mut minus_x_inv_sq_vec: Vec<BigInt> = Vec::with_capacity(lg_n);
        let mut allinv = BigInt::one();
        for (Li, Ri) in self.L.iter().zip(self.R.iter()) {
            let x = HSha256::create_hash_from_ge::<GE>(&[Li, Ri, ux]);
            let x_bn = x.to_big_int();
            let x_inv_fe = x.invert();
            let x_inv_bn = x_inv_fe.to_big_int();
            let x_sq_bn = BigInt::mod_mul(&x_bn, &x_bn, &order);
            let x_inv_sq_bn =
                BigInt::mod_mul(&x_inv_fe.to_big_int(), &x_inv_fe.to_big_int(), &order);

            x_sq_vec.push(x_sq_bn.clone());
            x_inv_sq_vec.push(x_inv_sq_bn.clone());
            minus_x_sq_vec.push(BigInt::mod_sub(&BigInt::zero(), &x_sq_bn, &order));
            minus_x_inv_sq_vec.push(BigInt::mod_sub(&BigInt::zero(), &x_inv_sq_bn, &order));
            allinv = allinv * x_inv_bn;
        }

        let mut s: Vec<BigInt> = Vec::with_capacity(n);
        s.push(allinv);
        for i in 1..n {
            let lg_i =
                (std::mem::size_of_val(&n) * 8) - 1 - ((i as usize).leading_zeros() as usize);
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [x_k,...,x_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let x_lg_i_sq = x_sq_vec[(lg_n - 1) - lg_i].clone();
            s.push(s[i - k].clone() * x_lg_i_sq);
        }

        let a_times_s: Vec<BigInt> = (0..n)
            .map(|i| BigInt::mod_mul(&s[i], &self.a_tag, &order))
            .collect();

        let b_div_s: Vec<BigInt> = (0..n)
            .map(|i| {
                let s_inv_i = BigInt::mod_inv(&s[i], &order);
                BigInt::mod_mul(&s_inv_i, &self.b_tag, &order)
            })
            .collect();

        let mut scalars: Vec<BigInt> = Vec::with_capacity(2 * n + 2 * lg_n + 1);
        scalars.extend_from_slice(&a_times_s);
        scalars.extend_from_slice(&b_div_s);
        scalars.extend_from_slice(&minus_x_sq_vec);
        scalars.extend_from_slice(&minus_x_inv_sq_vec);

        let mut points: Vec<GE> = Vec::with_capacity(2 * n + 2 * lg_n + 1);
        points.extend_from_slice(g_vec);
        points.extend_from_slice(hi_tag);
        points.extend_from_slice(&self.L);
        points.extend_from_slice(&self.R);

        let c = BigInt::mod_mul(&self.a_tag, &self.b_tag, &order);
        let ux_c = ux * &ECScalar::from(&c);

        let tot_len = points.len();

        let expect_P = (0..tot_len)
            .map(|i| points[i] * &ECScalar::from(&scalars[i]))
            .fold(ux_c, |acc, x| acc + x as GE);

        if *P == expect_P {
            Ok(())
        } else {
            Err(InnerProductError)
        }
    }
}

fn inner_product(a: &[BigInt], b: &[BigInt]) -> BigInt {
    assert_eq!(
        a.len(),
        b.len(),
        "inner_product(a,b): lengths of vectors do not match"
    );
    let out = BigInt::zero();
    let order = FE::q();
    let out = a.iter().zip(b).fold(out, |acc, x| {
        let aibi = BigInt::mod_mul(x.0, x.1, &order);
        BigInt::mod_add(&acc, &aibi, &order)
    });
    return out;
}

#[cfg(test)]
mod tests {
    use curv::arithmetic::traits::{Converter, Modulo};
    use curv::cryptographic_primitives::hashing::hash_sha512::HSha512;
    use curv::cryptographic_primitives::hashing::traits::*;
    use curv::elliptic::curves::traits::*;
    use curv::BigInt;
    use curv::elliptic::curves::secp256_k1::GE;
    use curv::elliptic::curves::secp256_k1::FE;
    use proofs::inner_product::InnerProductArg;
    use proofs::range_proof::generate_random_point;

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

        let label = BigInt::from(1);
        let hash = HSha512::create_hash(&[&label]);
        let Gx = generate_random_point(&Converter::to_vec(&hash));

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
        let c = super::inner_product(&a, &b);

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

        // R = <a * G> + <b_L * H_R> + c * ux
        let c_fe: FE = ECScalar::from(&c);
        let ux_c: GE = &Gx * &c_fe;
        let a_G = (0..n)
            .map(|i| {
                let ai: FE = ECScalar::from(&a[i]);
                &g_vec[i] * &ai
            })
            .fold(ux_c, |acc, x: GE| acc + x as GE);
        let P = (0..n)
            .map(|i| {
                let bi: FE = ECScalar::from(&b[i]);
                &hi_tag[i] * &bi
            })
            .fold(a_G, |acc, x: GE| acc + x as GE);

        let L_vec = Vec::with_capacity(n);
        let R_vec = Vec::with_capacity(n);
        let ipp = InnerProductArg::prove(&g_vec, &hi_tag, &Gx, &P, &a, &b, L_vec, R_vec);
        let verifier = ipp.verify(&g_vec, &hi_tag, &Gx, &P);
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

        let label = BigInt::from(1);
        let hash = HSha512::create_hash(&[&label]);
        let Gx = generate_random_point(&Converter::to_vec(&hash));

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
        let c = super::inner_product(&a, &b);

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

        // R = <a * G> + <b_L * H_R> + c * ux
        let c_fe: FE = ECScalar::from(&c);
        let ux_c: GE = &Gx * &c_fe;
        let a_G = (0..n)
            .map(|i| {
                let ai: FE = ECScalar::from(&a[i]);
                &g_vec[i] * &ai
            })
            .fold(ux_c, |acc, x: GE| acc + x as GE);
        let P = (0..n)
            .map(|i| {
                let bi: FE = ECScalar::from(&b[i]);
                &hi_tag[i] * &bi
            })
            .fold(a_G, |acc, x: GE| acc + x as GE);

        let L_vec = Vec::with_capacity(n);
        let R_vec = Vec::with_capacity(n);
        let ipp = InnerProductArg::prove(&g_vec, &hi_tag, &Gx, &P, &a, &b, L_vec, R_vec);
        let verifier = ipp.fast_verify(&g_vec, &hi_tag, &Gx, &P);
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

        let label = BigInt::from(1);
        let hash = HSha512::create_hash(&[&label]);
        let Gx = generate_random_point(&Converter::to_vec(&hash));

        let c = super::inner_product(&a, &b);

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

        // R = <a * G> + <b_L * H_R> + c * ux
        let c_fe: FE = ECScalar::from(&c);

        let ux_c: GE = &Gx * &c_fe;

        let a_G = (0..m)
            .map(|i| {
                let ai: FE = ECScalar::from(&a[i]);
                &g_vec[i] * &ai
            })
            .fold(ux_c, |acc, x: GE| acc + x as GE);
        let P = (0..m)
            .map(|i| {
                let bi: FE = ECScalar::from(&b[i]);
                &hi_tag[i] * &bi
            })
            .fold(a_G, |acc, x: GE| acc + x as GE);

        let L_vec = Vec::with_capacity(n);
        let R_vec = Vec::with_capacity(n);
        let ipp = InnerProductArg::prove(&g_vec, &hi_tag, &Gx, &P, &a, &b, L_vec, R_vec);
        let verifier = ipp.verify(&g_vec, &hi_tag, &Gx, &P);
        assert!(verifier.is_ok())
    }

    #[test]
    fn make_ipp_32() {
        test_helper(32);
    }

    #[test]
    fn make_ipp_16() {
        test_helper(16);
    }
    #[test]
    fn make_ipp_8() {
        test_helper(8);
    }

    #[test]
    fn make_ipp_4() {
        test_helper(4);
    }

    #[test]
    fn make_ipp_2() {
        test_helper(2);
    }

    #[test]
    fn make_ipp_1() {
        test_helper(1);
    }

    #[test]
    fn make_ipp_32_fast_verify() {
        test_helper_fast_verify(32);
    }

    #[test]
    fn make_ipp_16_fast_verify() {
        test_helper_fast_verify(16);
    }
    #[test]
    fn make_ipp_8_fast_verify() {
        test_helper_fast_verify(8);
    }

    #[test]
    fn make_ipp_4_fast_verify() {
        test_helper_fast_verify(4);
    }

    #[test]
    fn make_ipp_2_fast_verify() {
        test_helper_fast_verify(2);
    }

    #[test]
    fn make_ipp_1_fast_verify() {
        test_helper_fast_verify(1);
    }

    #[test]
    fn make_ipp_non_power_2() {
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
        // let mut padded_a = a.clone();
        a.extend_from_slice(&zero_append_vec);

        // let mut padded_b = b.clone();
        b.extend_from_slice(&zero_append_vec);

        test_helper_non_power_2(n, _n, &a, &b);
    }
}
