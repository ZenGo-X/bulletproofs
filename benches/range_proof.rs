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

#[macro_use]
extern crate criterion;

extern crate bulletproof;
extern crate curv;

mod bench {

    use bulletproof::proofs::range_proof::*;
    use criterion::Criterion;
    use curv::arithmetic::traits::{Converter, Samplable};
    use curv::cryptographic_primitives::hashing::hash_sha512::HSha512;
    use curv::cryptographic_primitives::hashing::traits::*;
    use curv::elliptic::curves::traits::*;
    use curv::{BigInt, FE, GE};

    pub fn bench_range_proof_8(c: &mut Criterion) {
        c.bench_function("range proof", move |b| {
            let n = 16;
            // num of proofs
            let m = 2;
            let nm = n * m;
            let kzen: &[u8] = &[75, 90, 101, 110];
            let kzen_label = BigInt::from(kzen);

            let g: GE = ECPoint::generator();
            let label = BigInt::from(1);
            let hash = HSha512::create_hash(&[&label]);
            let h = generate_random_point(&Converter::to_vec(&hash));

            let g_vec = (0..nm)
                .map(|i| {
                    let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                    let hash_i = HSha512::create_hash(&[&kzen_label_i]);
                    generate_random_point(&Converter::to_vec(&hash_i))
                })
                .collect::<Vec<GE>>();

            // can run in parallel to g_vec:
            let h_vec = (0..nm)
                .map(|i| {
                    let kzen_label_j =
                        BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                    let hash_j = HSha512::create_hash(&[&kzen_label_j]);
                    generate_random_point(&Converter::to_vec(&hash_j))
                })
                .collect::<Vec<GE>>();

            let range = BigInt::from(2).pow(n as u32);
            let v_vec = (0..m)
                .map(|_i| {
                    let v = BigInt::sample_below(&range);
                    let v_fe: FE = ECScalar::from(&v);
                    v_fe
                })
                .collect::<Vec<FE>>();

            let r_vec = (0..m).map(|_i| ECScalar::new_random()).collect::<Vec<FE>>();

            let ped_com_vec = (0..m)
                .map(|i| {
                    let ped_com = g.scalar_mul(&v_vec[i].get_element())
                        + h.scalar_mul(&r_vec[i].get_element());
                    ped_com
                })
                .collect::<Vec<GE>>();

            b.iter(|| {
                let range_proof =
                    RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n);
                let result =
                    RangeProof::verify(&range_proof, &g_vec, &h_vec, &g, &h, &ped_com_vec, n);
                assert!(result.is_ok());
            })
        });
    }

    criterion_group! {
    name = range_proof;
    config = Criterion::default().sample_size(10);
    targets =bench_range_proof_8}

}
//fn main() {}
criterion_main!(bench::range_proof);
