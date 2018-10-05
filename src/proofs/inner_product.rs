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

pub struct InnerProductArg {
    L: Vec<GE>,
    R: Vec<GE>,
    a_tag: BigInt,
    b_tag: BigInt,
}

impl InnerProductArg{

    pub fn prove(mut g_vec: Vec<GE>, mut hi_tag: Vec<GE>, ux: GE, P: GE, mut a: Vec<BigInt>, mut b :Vec<BigInt>, mut L_vec: Vec<GE>, mut R_vec: Vec<GE>) ->InnerProductArg {
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
            let x_inv = BigInt::mod_pow(&x_bn, &BigInt::from(-1), &order);
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
}

// let L_fe : Vec<FE> = a_L.iter().chain(b_R.iter()).chain(iter::once(&c_L));
//  let L_ge: Vec<GE> = G_R.iter().chain(H_L.iter()).chain(iter::once(G));
//  let L = (0..n).map(|i|{
//      L_ge[i].clone() * &L_fe[i]
//   }).collect::<Vec<GE>>();

pub fn inner_product(a: &[BigInt], b: &[BigInt]) -> BigInt {
    let mut out = BigInt::zero();
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    let out = a.iter().zip(b).fold(out,|acc,x| {
        let aibi = x.0 * x.1;
        acc + aibi
    });
    return out;
}
