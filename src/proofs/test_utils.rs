use curv::elliptic::curves::traits::*;
use curv::arithmetic::big_gmp::*;

pub fn generate_random_point<P: ECPoint>(random_source: &[u8]) -> P {
    let bn = BigInt::from(random_source);
    let scalar = <P::Scalar as ECScalar>::from(&bn);
    P::generator() * scalar
}
