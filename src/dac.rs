use mcore::bn254::*;
use mcore::{
    bn254::ecp2::*,
    bn254::{big::*, bls::bls_hash_to_point, ecp::*},
    rand::RAND_impl,
};

use crate::mss::prepare_rng;

//#[test]
fn test() {
    let mut rng = prepare_rng();
    let bi = BIG::random(&mut rng);

    let mut b = [0u8; 32];
    bi.tobytes(&mut b);

    let e = ECP::frombytes(&b);

    //println!("{:?}", b);
}

#[test]
fn test_hash_to_curve() {
    let m = b"this is a message";

    let hashed = bls_hash_to_point(m);

    println!("{:?}", &hashed);
}
