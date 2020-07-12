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

#[macro_use]
extern crate criterion;

extern crate bulletproof;
extern crate curv;

mod bench_range_proof {

    use bulletproof::proofs::range_proof::*;
    use criterion::Criterion;
    use curv::arithmetic::traits::{Converter, Samplable};
    use curv::cryptographic_primitives::hashing::hash_sha512::HSha512;
    use curv::cryptographic_primitives::hashing::traits::*;
    use curv::elliptic::curves::traits::*;
    use curv::{BigInt, FE, GE};

    pub fn bench_range_proof_16_2(c: &mut Criterion) {
        c.bench_function("range proof, n=16, m=2", move |b| {
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

    pub fn create_range_proof_16_2(c: &mut Criterion) {
        c.bench_function("create range proof, n=16, m=2", move |b| {
            let n = 16;
            // num of proofs (aggregation factor)
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

            b.iter(|| {
                RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n)
            })
        });
    }

    pub fn verify_range_proof_16_2(c: &mut Criterion) {
        c.bench_function("verify range proof, n=16, m=2", move |b| {
            let n = 16;
            // num of proofs (aggregation factor)
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

            let range_proof = RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n);

            b.iter(|| {
                let result =
                    RangeProof::verify(&range_proof, &g_vec, &h_vec, &g, &h, &ped_com_vec, n);
                assert!(result.is_ok());
            })
        });
    }

    pub fn fast_verify_range_proof_16_2(c: &mut Criterion) {
        c.bench_function("multiexp-based verify range proof, n=16, m=2", move |b| {
            let n = 16;
            // num of proofs (aggregation factor)
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

            let range_proof = RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n);

            b.iter(|| {
                let result =
                    RangeProof::fast_verify(&range_proof, &g_vec, &h_vec, &g, &h, &ped_com_vec, n);
                assert!(result.is_ok());
            })
        });
    }

    pub fn create_range_proof_64_1(c: &mut Criterion) {
        c.bench_function("create range proof, n=64, m=1", move |b| {
            let n = 64;
            // num of proofs (aggregation factor)
            let m = 1;
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

            b.iter(|| {
                RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n)
            })
        });
    }

    pub fn fast_verify_range_proof_64_1(c: &mut Criterion) {
        c.bench_function("fast verify range proof, n=64, m=1", move |b| {
            let n = 64;
            // num of proofs (aggregation factor)
            let m = 1;
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

            let range_proof = RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n);

            b.iter(|| {
                let result =
                    RangeProof::fast_verify(&range_proof, &g_vec, &h_vec, &g, &h, &ped_com_vec, n);
                assert!(result.is_ok());
            })
        });
    }

    pub fn create_range_proof_64_4(c: &mut Criterion) {
        c.bench_function("create range proof, n=64, m=4", move |b| {
            let n = 64;
            // num of proofs (aggregation factor)
            let m = 4;
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

            b.iter(|| {
                RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n)
            })
        });
    }

    pub fn fast_verify_range_proof_64_4(c: &mut Criterion) {
        c.bench_function("fast verify range proof, n=64, m=4", move |b| {
            let n = 64;
            // num of proofs (aggregation factor)
            let m = 4;
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

            let range_proof = RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n);

            b.iter(|| {
                let result =
                    RangeProof::fast_verify(&range_proof, &g_vec, &h_vec, &g, &h, &ped_com_vec, n);
                assert!(result.is_ok());
            })
        });
    }

    pub fn create_range_proof_64_8(c: &mut Criterion) {
        c.bench_function("create range proof, n=64, m=8", move |b| {
            let n = 64;
            // num of proofs (aggregation factor)
            let m = 8;
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

            b.iter(|| {
                RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n)
            })
        });
    }

    pub fn fast_verify_range_proof_64_8(c: &mut Criterion) {
        c.bench_function("fast verify range proof, n=64, m=8", move |b| {
            let n = 64;
            // num of proofs (aggregation factor)
            let m = 8;
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

            let range_proof = RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n);

            b.iter(|| {
                let result =
                    RangeProof::fast_verify(&range_proof, &g_vec, &h_vec, &g, &h, &ped_com_vec, n);
                assert!(result.is_ok());
            })
        });
    }

    pub fn create_range_proof_64_16(c: &mut Criterion) {
        c.bench_function("create range proof, n=64, m=16", move |b| {
            let n = 64;
            // num of proofs (aggregation factor)
            let m = 16;
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

            b.iter(|| {
                RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n)
            })
        });
    }

    pub fn fast_verify_range_proof_64_16(c: &mut Criterion) {
        c.bench_function("fast verify range proof, n=64, m=16", move |b| {
            let n = 64;
            // num of proofs (aggregation factor)
            let m = 16;
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

            let range_proof = RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n);

            b.iter(|| {
                let result =
                    RangeProof::fast_verify(&range_proof, &g_vec, &h_vec, &g, &h, &ped_com_vec, n);
                assert!(result.is_ok());
            })
        });
    }

    pub fn create_range_proof_64_32(c: &mut Criterion) {
        c.bench_function("create range proof, n=64, m=32", move |b| {
            let n = 64;
            // num of proofs (aggregation factor)
            let m = 32;
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

            b.iter(|| {
                RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n)
            })
        });
    }

    pub fn fast_verify_range_proof_64_32(c: &mut Criterion) {
        c.bench_function("fast verify range proof, n=64, m=32", move |b| {
            let n = 64;
            // num of proofs (aggregation factor)
            let m = 32;
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

            let range_proof = RangeProof::prove(&g_vec, &h_vec, &g, &h, v_vec.clone(), &r_vec, n);

            b.iter(|| {
                let result =
                    RangeProof::fast_verify(&range_proof, &g_vec, &h_vec, &g, &h, &ped_com_vec, n);
                assert!(result.is_ok());
            })
        });
    }

    criterion_group! {
    name = range_proof;
    config = Criterion::default().sample_size(10);
    targets =
    bench_range_proof_16_2,
    create_range_proof_16_2,
    verify_range_proof_16_2,
    fast_verify_range_proof_16_2,
    create_range_proof_64_1,
    fast_verify_range_proof_64_1,
    create_range_proof_64_4,
    fast_verify_range_proof_64_4,
    create_range_proof_64_8,
    fast_verify_range_proof_64_8,
    create_range_proof_64_16,
    fast_verify_range_proof_64_16,
    create_range_proof_64_32,
    fast_verify_range_proof_64_32,
    }
}

mod bench_wip_range_proof {
    use bulletproof::proofs::range_proof_wip::*;
    use criterion::Criterion;
    use curv::arithmetic::traits::{Samplable};
    use curv::elliptic::curves::traits::*;
    use curv::{BigInt, FE, GE};

    pub fn wip_range_proof_16_2(c: &mut Criterion) {
        c.bench_function("wip range proof, n=16, m=2", move |b| {
            let n = 16;
            // num of proofs
            let m = 2;
            
            // generate stmt
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
            
            b.iter(|| {
                let range_proof_wip = 
                    RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);
                let result = 
                    RangeProofWIP::verify(&range_proof_wip, stmt.clone(), &ped_com_vec);
                assert!(result.is_ok());
            })
        });
    }

    pub fn create_wip_range_proof_16_2(c: &mut Criterion) {
        c.bench_function("create wip range proof, n=16, m=2", move |b| {
            let n = 16;
            // num of proofs
            let m = 2;
            
            // generate stmt
            let KZen: &[u8] = &[75, 90, 101, 110];
            let kzen_label = BigInt::from(KZen);
            let stmt = StatementRP::generate_bases(&kzen_label, m, n);
    
            // generate witness
            let range = BigInt::from(2).pow(n as u32);
            let v_vec = (0..m)
                .map(|_| ECScalar::from(&BigInt::sample_below(&range)))
                .collect::<Vec<FE>>();
    
            let r_vec = (0..m).map(|_| ECScalar::new_random()).collect::<Vec<FE>>();
            
            b.iter(|| {
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);
            })
        });
    }

    pub fn verify_wip_range_proof_16_2(c: &mut Criterion) {
        c.bench_function("verify wip range proof using multi-exp, n=16, m=2", move |b| {
            let n = 16;
            // num of proofs
            let m = 2;
            
            // generate stmt
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
            
            let range_proof_wip = 
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);

            b.iter(|| {
                let result = 
                    RangeProofWIP::verify(&range_proof_wip, stmt.clone(), &ped_com_vec);
                assert!(result.is_ok());
            })
        });
    }

    pub fn create_wip_range_proof_64_1(c: &mut Criterion) {
        c.bench_function("create wip range proof, n=64, m=1", move |b| {
            let n = 64;
            // num of proofs
            let m = 1;
            
            // generate stmt
            let KZen: &[u8] = &[75, 90, 101, 110];
            let kzen_label = BigInt::from(KZen);
            let stmt = StatementRP::generate_bases(&kzen_label, m, n);
    
            // generate witness
            let range = BigInt::from(2).pow(n as u32);
            let v_vec = (0..m)
                .map(|_| ECScalar::from(&BigInt::sample_below(&range)))
                .collect::<Vec<FE>>();
    
            let r_vec = (0..m).map(|_| ECScalar::new_random()).collect::<Vec<FE>>();
            
            b.iter(|| {
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);
            })
        });
    }

    pub fn verify_wip_range_proof_64_1(c: &mut Criterion) {
        c.bench_function("fast verify wip range proof, n=64, m=1", move |b| {
            let n = 64;
            // num of proofs
            let m = 1;
            
            // generate stmt
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
            
            let range_proof_wip = 
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);

            b.iter(|| {
                let result = 
                    RangeProofWIP::verify(&range_proof_wip, stmt.clone(), &ped_com_vec);
                assert!(result.is_ok());
            })
        });
    }

    pub fn create_wip_range_proof_64_4(c: &mut Criterion) {
        c.bench_function("create wip range proof, n=64, m=4", move |b| {
            let n = 64;
            // num of proofs
            let m = 4;
            
            // generate stmt
            let KZen: &[u8] = &[75, 90, 101, 110];
            let kzen_label = BigInt::from(KZen);
            let stmt = StatementRP::generate_bases(&kzen_label, m, n);
    
            // generate witness
            let range = BigInt::from(2).pow(n as u32);
            let v_vec = (0..m)
                .map(|_| ECScalar::from(&BigInt::sample_below(&range)))
                .collect::<Vec<FE>>();
    
            let r_vec = (0..m).map(|_| ECScalar::new_random()).collect::<Vec<FE>>();
            
            b.iter(|| {
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);
            })
        });
    }

    pub fn verify_wip_range_proof_64_4(c: &mut Criterion) {
        c.bench_function("fast verify wip range proof, n=64, m=4", move |b| {
            let n = 64;
            // num of proofs
            let m = 4;
            
            // generate stmt
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
            
            let range_proof_wip = 
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);

            b.iter(|| {
                let result = 
                    RangeProofWIP::verify(&range_proof_wip, stmt.clone(), &ped_com_vec);
                assert!(result.is_ok());
            })
        });
    }

    pub fn create_wip_range_proof_64_8(c: &mut Criterion) {
        c.bench_function("create wip range proof, n=64, m=8", move |b| {
            let n = 64;
            // num of proofs
            let m = 8;
            
            // generate stmt
            let KZen: &[u8] = &[75, 90, 101, 110];
            let kzen_label = BigInt::from(KZen);
            let stmt = StatementRP::generate_bases(&kzen_label, m, n);
    
            // generate witness
            let range = BigInt::from(2).pow(n as u32);
            let v_vec = (0..m)
                .map(|_| ECScalar::from(&BigInt::sample_below(&range)))
                .collect::<Vec<FE>>();
    
            let r_vec = (0..m).map(|_| ECScalar::new_random()).collect::<Vec<FE>>();
            
            b.iter(|| {
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);
            })
        });
    }

    pub fn verify_wip_range_proof_64_8(c: &mut Criterion) {
        c.bench_function("fast verify wip range proof, n=64, m=8", move |b| {
            let n = 64;
            // num of proofs
            let m = 8;
            
            // generate stmt
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
            
            let range_proof_wip = 
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);

            b.iter(|| {
                let result = 
                    RangeProofWIP::verify(&range_proof_wip, stmt.clone(), &ped_com_vec);
                assert!(result.is_ok());
            })
        });
    }

    pub fn create_wip_range_proof_64_16(c: &mut Criterion) {
        c.bench_function("create wip range proof, n=64, m=16", move |b| {
            let n = 64;
            // num of proofs
            let m = 16;
            
            // generate stmt
            let KZen: &[u8] = &[75, 90, 101, 110];
            let kzen_label = BigInt::from(KZen);
            let stmt = StatementRP::generate_bases(&kzen_label, m, n);
    
            // generate witness
            let range = BigInt::from(2).pow(n as u32);
            let v_vec = (0..m)
                .map(|_| ECScalar::from(&BigInt::sample_below(&range)))
                .collect::<Vec<FE>>();
    
            let r_vec = (0..m).map(|_| ECScalar::new_random()).collect::<Vec<FE>>();
            
            b.iter(|| {
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);
            })
        });
    }

    pub fn verify_wip_range_proof_64_16(c: &mut Criterion) {
        c.bench_function("fast verify wip range proof, n=64, m=16", move |b| {
            let n = 64;
            // num of proofs
            let m = 16;
            
            // generate stmt
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
            
            let range_proof_wip = 
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);

            b.iter(|| {
                let result = 
                    RangeProofWIP::verify(&range_proof_wip, stmt.clone(), &ped_com_vec);
                assert!(result.is_ok());
            })
        });
    }

    pub fn create_wip_range_proof_64_32(c: &mut Criterion) {
        c.bench_function("create wip range proof, n=64, m=32", move |b| {
            let n = 64;
            // num of proofs
            let m = 32;
            
            // generate stmt
            let KZen: &[u8] = &[75, 90, 101, 110];
            let kzen_label = BigInt::from(KZen);
            let stmt = StatementRP::generate_bases(&kzen_label, m, n);
    
            // generate witness
            let range = BigInt::from(2).pow(n as u32);
            let v_vec = (0..m)
                .map(|_| ECScalar::from(&BigInt::sample_below(&range)))
                .collect::<Vec<FE>>();
    
            let r_vec = (0..m).map(|_| ECScalar::new_random()).collect::<Vec<FE>>();
            
            b.iter(|| {
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);
            })
        });
    }

    pub fn verify_wip_range_proof_64_32(c: &mut Criterion) {
        c.bench_function("fast verify wip range proof, n=64, m=32", move |b| {
            let n = 64;
            // num of proofs
            let m = 32;
            
            // generate stmt
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
            
            let range_proof_wip = 
                RangeProofWIP::prove(stmt.clone(), v_vec.clone(), &r_vec);

            b.iter(|| {
                let result = 
                    RangeProofWIP::verify(&range_proof_wip, stmt.clone(), &ped_com_vec);
                assert!(result.is_ok());
            })
        });
    }

    criterion_group! {
    name = wip_range_proof;
    config = Criterion::default().sample_size(10);
    targets = 
        wip_range_proof_16_2,
        create_wip_range_proof_16_2,
        verify_wip_range_proof_16_2,
        create_wip_range_proof_64_1,
        verify_wip_range_proof_64_1,
        create_wip_range_proof_64_4,
        verify_wip_range_proof_64_4,
        create_wip_range_proof_64_8,
        verify_wip_range_proof_64_8,
        create_wip_range_proof_64_16,
        verify_wip_range_proof_64_16,
        create_wip_range_proof_64_32,
        verify_wip_range_proof_64_32,
    }
}

//fn main() {}
criterion_main!(
    bench_range_proof::range_proof,
    bench_wip_range_proof::wip_range_proof,
);
