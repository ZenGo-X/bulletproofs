use curv::arithmetic::big_gmp::BigInt;
use curv::elliptic::curves::traits::*;

// TODO: this function needs to be reviewed. consider applying KDF
//  to given bytes before converting them to ec scalar
pub fn derive_point<P: ECPoint>(source: &[u8]) -> P {
    let bn = BigInt::from(source);
    let scalar = <P::Scalar as ECScalar>::from(&bn);
    P::generator() * scalar
}
