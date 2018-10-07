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
use cryptography_utils::elliptic::curves::traits::*;
use cryptography_utils::{FE,GE};
use cryptography_utils::BigInt;
use std::iter;
use cryptography_utils::cryptographic_primitives::hashing::traits::*;
use cryptography_utils::cryptographic_primitives::hashing::hash_sha256::HSha256;
use cryptography_utils::arithmetic::traits::Modulo;
use Errors::{self,InnerProductError};
pub struct InnerProductArg {
    pub L: Vec<GE>,
    pub R: Vec<GE>,
    pub a_tag: BigInt,
    pub b_tag: BigInt,
}

impl InnerProductArg{

    pub fn prove(mut g_vec: Vec<GE>, mut hi_tag: Vec<GE>, ux: GE, P: GE, mut a: Vec<BigInt>, mut b :Vec<BigInt>, mut L_vec: Vec<GE>, mut R_vec: Vec<GE>) -> InnerProductArg {
        let mut G = &mut g_vec[..];
        let mut H = &mut hi_tag[..];
        let mut a = &mut a[..];;
        let mut b = &mut b[..];
        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert!(n.is_power_of_two());

     //   let mut L_vec = Vec::with_capacity(n);
     //   let mut R_vec = Vec::with_capacity(n);
        if n != 1 {
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            // L = <a_L * G_R> + <b_R * H_L> + c_L * ux
            let c_L_fe: FE = ECScalar::from(&c_L);
            let ux_CL: GE = ux.clone() *  c_L_fe;
            let aL_GR = (0..n)
                .map(|i| {
                    let aLi:FE =  ECScalar::from(&a_L[i]);
                    G_R[i].clone() * aLi } )
                .fold(ux_CL, |acc,x| acc + x as GE);
            let L = (0..n)
                .map(|i| {
                    let bRi : FE = ECScalar::from(&b_R[i]);
                    H_L[i].clone() * bRi} )
                .fold(aL_GR, |acc,x| acc + x as GE);

            // R = <a_R * G_L> + <b_L * H_R> + c_R * ux
            let c_R_fe : FE = ECScalar::from(&c_R);
            let ux_CR: GE = ux.clone() * c_R_fe;
            let aR_GL = (0..n)
                .map(|i| {
                    let aRi:FE = ECScalar::from(&a_R[i]);
                    G_L[i].clone() *aRi}  )
                .fold(ux_CR, |acc,x: GE| acc + x as GE);
            let R = (0..n)
                .map(|i| {
                    let bLi :FE= ECScalar::from(&b_L[i]);
                    H_R[i].clone() *bLi} )
                .fold(aR_GL, |acc,x:GE| acc + x as GE);


            L_vec.push(L.clone());
            R_vec.push(R.clone());

            let x = HSha256::create_hash_from_ge(&[&L,&R, &ux]);
            let x_bn = x.to_big_int();
            let order = x.q();
            let x_inv = x_bn.invert(&order).unwrap();
            let x_inv_fe = ECScalar::from(&x_inv);

            let mut a_new = (0..n).map(|i| {
                let aLx = BigInt::mod_mul(&a_L[i], &x_bn, &order);
                let aR_minusx = BigInt::mod_mul(&a_R[i], &x_inv, &order);
                BigInt::mod_add(&aLx, &aR_minusx, &order)
            }).collect::<Vec<BigInt>>();
         //   a = &mut a_new[..];

            let mut b_new = (0..n).map(|i| {
                let bRx = BigInt::mod_mul(&b_R[i], &x_bn, &order);
                let bL_minusx = BigInt::mod_mul(&b_L[i], &x_inv, &order);
                BigInt::mod_add(&bRx, &bL_minusx, &order)
            }).collect::<Vec<BigInt>>();
        //    b = &mut b_new[..];

            let mut G_new = (0..n).map(|i| {
                let GLx_inv = G_L[i].clone() * &x_inv_fe;
                let GRx = G_R[i].clone() * &x;
                GRx + GLx_inv
            }).collect::<Vec<GE>>();
         //   G = &mut G_new[..];

            let mut H_new = (0..n).map(|i| {
                let HLx = H_L[i].clone() * &x;
                let HRx_inv = H_R[i].clone() * &x_inv_fe;
                HLx + HRx_inv
            }).collect::<Vec<GE>>();
        //    H = &mut H_new[..];

            return InnerProductArg::prove(G_new,H_new,ux,P,a_new,b_new,L_vec, R_vec);

        }

        InnerProductArg{
            L: L_vec,
            R: R_vec,
            a_tag: a[0].clone(),
            b_tag: b[0].clone(),
        }
    }

    pub fn verify(&self, mut g_vec: Vec<GE>, mut hi_tag: Vec<GE>, ux: GE, P: GE) -> Result<bool,Errors>{

        let mut G = &mut g_vec[..];
        let mut H = &mut hi_tag[..];
        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert!(n.is_power_of_two());

        if n != 1 {
            n = n / 2;
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);


            let x = HSha256::create_hash_from_ge(&[&self.L[0],&self.R[0], &ux]);
            let x_bn = x.to_big_int();
            let order = x.q();
            let x_inv = x_bn.invert(&order).unwrap();
            let x_inv_fe = ECScalar::from(&x_inv);
            let x_sq_bn = BigInt::mod_mul(&x_bn, &x_bn, &order);
            let x_inv_sq_bn = BigInt::mod_mul(&x_inv, &x_inv, &order);
            let x_sq_fe: FE = ECScalar::from(&x_sq_bn);
            let x_inv_sq_fe: FE = ECScalar::from(&x_inv_sq_bn);


            let mut G_new = (0..n).map(|i| {
                let GLx_inv = G_L[i].clone() * &x_inv_fe;
                let GRx = G_R[i].clone() * &x;
                GRx + GLx_inv
            }).collect::<Vec<GE>>();
            //   G = &mut G_new[..];

            let mut H_new = (0..n).map(|i| {
                let HLx = H_L[i].clone() * &x;
                let HRx_inv = H_R[i].clone() * &x_inv_fe;
                HLx + HRx_inv
            }).collect::<Vec<GE>>();
            //    H = &mut H_new[..];
            let Lx_sq = self.L[0].clone() * &x_sq_fe;
            let Rx_sq_inv = self.R[0].clone() * &x_inv_sq_fe;
            let P_tag = Lx_sq + Rx_sq_inv + P;
            let ip = InnerProductArg{
                L: (&self.L[1..]).to_vec(),
                R: (&self.R[1..]).to_vec(),
                a_tag: self.a_tag.clone(),
                b_tag: self.b_tag.clone(),
            };
            return ip.verify( G_new,H_new,ux,P_tag);

        }

        let a_fe: FE = ECScalar::from(&self.a_tag);
        let b_fe: FE = ECScalar::from(&self.b_tag);
        let c = a_fe.mul(&b_fe.get_element());
        let Ga = G[0].clone() * a_fe;
        let Hb = H[0].clone() * b_fe;
        let ux_c = ux * c;
        let P_calc = Ga+ Hb+ ux_c;
        if P.get_element() == P_calc.get_element(){
            Ok(true)
        }
        else{
            Err(InnerProductError)
        }


    }
}


pub fn inner_product(a: &[BigInt], b: &[BigInt]) -> BigInt {
    let mut out = BigInt::zero();
    let temp: FE = ECScalar::new_random();
    let order = temp.q();
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    let out = a.iter().zip(b).fold(out,|acc,x| {
        let aibi = BigInt::mod_mul(x.0, x.1, &order) ;
        BigInt::mod_add(&acc, &aibi, &order)
    });
    return out;

}

#[cfg(test)]
mod tests {
    use cryptography_utils::BigInt;
    use cryptography_utils::arithmetic::traits::{Converter,Modulo};
    use cryptography_utils::{GE,FE};
    use cryptography_utils::elliptic::curves::traits::*;
    use cryptography_utils::cryptographic_primitives::hashing::traits::*;
    use cryptography_utils::cryptographic_primitives::hashing::hash_sha512::HSha512;
    use std::ops::Shr;
    use itertools::Itertools;
    use proofs::inner_product::InnerProductArg;
    use proofs::range_proof::generate_random_point;

    fn test_helper(n: usize) {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from(KZen);

                let mut g_vec = (0..n).map(|i| {
                    let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                    let hash_i = HSha512::create_hash(&[&kzen_label_i]);
                    generate_random_point(&Converter::to_vec(&hash_i))
                }).collect::<Vec<GE>>();


                // can run in parallel to g_vec:
                let mut h_vec = (0..n).map(|i| {
                    let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                    let hash_j = HSha512::create_hash(&[&kzen_label_j]);
                    generate_random_point(&Converter::to_vec(&hash_j))
                }).collect::<Vec<GE>>();

                let label = BigInt::from(1);
                let hash = HSha512::create_hash(&[&label]);
                let Gx = generate_random_point(&Converter::to_vec(&hash));


                let mut a: Vec<_> = (0..n).map(|_| {
                    let rand: FE = ECScalar::new_random();
                    rand.to_big_int()
                }).collect();

                let mut b: Vec<_> = (0..n).map(|_| {
                    let rand: FE = ECScalar::new_random();
                    rand.to_big_int()
                }).collect();
                let c = super::inner_product(&a, &b);

                let y : FE  = ECScalar::new_random();
                let order = y.q();
                let yi = (0..n).map(|i| BigInt::mod_pow(&y.to_big_int(), &BigInt::from(i as u32), &order))
                    .collect::<Vec<BigInt>>();


                let yi_inv = (0..n).map(|i| {
                    yi[i].invert(&order).expect(&"error invert")
                }).collect::<Vec<BigInt>>();

                let hi_tag = (0..n).map(|i| {
                    h_vec[i].clone() * &ECScalar::from(&yi_inv[i])
                }).collect::<Vec<GE>>();

                // R = <a * G> + <b_L * H_R> + c * ux
                let c_fe: FE = ECScalar::from(&c);
                let ux_c: GE = Gx.clone() * c_fe;
                let a_G = (0..n)
                    .map(|i| {
                        let ai: FE = ECScalar::from(&a[i]);
                        g_vec[i].clone() * ai
                    })
                    .fold(ux_c, |acc, x: GE| acc + x as GE);
                let P = (0..n)
                    .map(|i| {
                        let bi: FE = ECScalar::from(&b[i]);
                        hi_tag[i].clone() * bi
                    })
                    .fold(a_G, |acc, x: GE| acc + x as GE);

                let mut L_vec = Vec::with_capacity(n);
                let mut R_vec = Vec::with_capacity(n);
                let ipp = InnerProductArg::prove(g_vec.clone(), hi_tag.clone(),Gx.clone(), P.clone(),a,b,L_vec,R_vec);
                let verifier = ipp.verify(g_vec,hi_tag,Gx,P);
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

}