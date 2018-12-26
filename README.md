# Bulletproofs
Bulletproof Rust implementation for aggregated range proofs: 
https://eprint.iacr.org/2017/1066.pdf
* Works for *multiple elliptic curves*. Currently supports:
  * _secp256k1_ [1] 
  * _ristretto_ [2]
  * _ed25519_ [3]
* The implementation is based on some design ideas presented in dalek's implementation [4] and in ElementsProject implementation [5]. This project required abstraction of elliptic curve. We rely on [6] for the abstraction. Both mentioned implementations cannot be generelized to other curves since they the code is tailored to a specific elliptic curve library. 

## Benchemarks
Control range and batch size using `n,m` variables. Run `cargo bench`. For _curve25519_ the current implementation is 6x  slower than [4]. 

## Usage
```Rust
    use curv::arithmetic::traits::{Converter, Samplable};
    use curv::cryptographic_primitives::hashing::hash_sha512::HSha512;
    use curv::cryptographic_primitives::hashing::traits::*;
    use curv::elliptic::curves::traits::*;
    use curv::BigInt;
    use curv::{FE, GE};
    use proofs::range_proof::generate_random_point;
    use proofs::range_proof::RangeProof;
    
        bit range
        let n = 8;
        // num of agg proofs
        let m = 4;
        let nm = n * m;
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
        let v_vec = (0..m)
            .map(|_| ECScalar::from(&BigInt::sample_below(&range)))
            .collect::<Vec<FE>>();

        let r_vec = (0..m).map(|_| ECScalar::new_random()).collect::<Vec<FE>>();

        let ped_com_vec = (0..m)
            .map(|i| {
                let ped_com = G.clone() * &v_vec[i] + H.clone() * &r_vec[i];
                ped_com
            }).collect::<Vec<GE>>();

        let range_proof = RangeProof::prove(&g_vec, &h_vec, &G, &H, v_vec, &r_vec, n);
        let result = RangeProof::verify(&range_proof, &g_vec, &h_vec, &G, &H, &ped_com_vec, n);
        assert!(result.is_ok());
```

## References
[1] https://github.com/rust-bitcoin/rust-secp256k1/ 

[2] https://github.com/dalek-cryptography/curve25519-dalek

[3] https://github.com/typed-io/cryptoxide/blob/master/src/curve25519.rs

[4] https://github.com/dalek-cryptography/bulletproofs

[5] https://github.com/ElementsProject/secp256k1-zkp/pull/23

[6] https://github.com/KZen-networks/cryptography-utils/blob/master/src/elliptic/curves/traits.rs
