#[macro_use]
extern crate criterion;

extern crate bulletproof;
extern crate cryptography_utils;

mod bench {

    use bulletproof::proofs::range_proof::*;
    use criterion::Criterion;
    use cryptography_utils::arithmetic::traits::{Converter, Modulo, Samplable};
    use cryptography_utils::cryptographic_primitives::hashing::hash_sha256::HSha256;
    use cryptography_utils::cryptographic_primitives::hashing::hash_sha512::HSha512;
    use cryptography_utils::cryptographic_primitives::hashing::traits::*;
    use cryptography_utils::elliptic::curves::traits::*;
    use cryptography_utils::{BigInt, FE, GE};

    pub fn bench_range_proof_8(c: &mut Criterion) {
        c.bench_function("range proof", move |b| {

            let n = 8;
            // num of proofs
            let m = 4;
            let nm = n*m;
            let KZen: &[u8] = &[75, 90, 101, 110];
            let kzen_label = BigInt::from(KZen);

            let G: GE = ECPoint::generator();
            let label = BigInt::from(1);
            let hash = HSha512::create_hash(&[&label]);
            let H = generate_random_point(&Converter::to_vec(&hash));

            let g_vec = (0..nm)
                .map(|i| {
                    let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                    let hash_i = HSha512::create_hash(&[&kzen_label_i]);
                    generate_random_point(&Converter::to_vec(&hash_i))
                }).collect::<Vec<GE>>();

            // can run in parallel to g_vec:
            let h_vec = (0..nm)
                .map(|i| {
                    let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                    let hash_j = HSha512::create_hash(&[&kzen_label_j]);
                    generate_random_point(&Converter::to_vec(&hash_j))
                }).collect::<Vec<GE>>();

            let range = BigInt::from(2).pow(n as u32);
            let v_vec = (0..m).map(|i|{
                let v = BigInt::sample_below(&range);
                let v_fe : FE = ECScalar::from(&v);
                v_fe
            }).collect::<Vec<FE>>();

            let r_vec = (0..m).map(|i|{
                ECScalar::new_random()
            }).collect::<Vec<FE>>();

            let ped_com_vec = (0..m).map(|i|{
                let ped_com = G.clone() * &v_vec[i] + H.clone() * &r_vec[i];
                ped_com
            }).collect::<Vec<GE>>();

            b.iter(|| {
                let range_proof = RangeProof::prove(&g_vec, &h_vec, &G, &H, v_vec.clone(), r_vec.clone(), n);
                let result = RangeProof::verify(&range_proof, &g_vec, &h_vec, &G, &H, ped_com_vec.clone(), n);
                assert!(result.is_ok());
            })
        });
    }

    criterion_group!{
    name = range_proof;
    config = Criterion::default().sample_size(10);
    targets =bench_range_proof_8}

}
//fn main() {}
criterion_main!(bench::range_proof);
