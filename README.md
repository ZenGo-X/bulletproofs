# Bulletproofs
This library implements [Bulletproofs+](https://eprint.iacr.org/2020/735.pdf) and [Bulletproofs](https://eprint.iacr.org/2017/1066.pdf) aggregated range proofs with multi-exponent verification. The library supports multiple elliptic curves: _secp256k1_ , _ristretto_ , _ed25519_


## Usage
Control range and batch size using `n,m` variables. Supported range is any number `0<n<2^64`. 
The library contains multiple test examples that can be followed (run them with `Cargo test`). To change an elliptic curve, change `feature` for [Curv](https://github.com/KZen-networks/curv/blob/master/Cargo.toml) dependency inside `Cargo.toml`. 

## Benchmarks
 Run `cargo bench`. For _ristretto_ the current implementation is ~4x slower than [dalek-cryptography](https://github.com/dalek-cryptography/curve25519-dalek). 

## Contact
Feel free to [reach out](mailto:github@kzencorp.com) or join the ZenGo X [Telegram](https://t.me/joinchat/ET1mddGXRoyCxZ-7) for discussions on code and research.
