use std::marker::PhantomData;

use mcore::{bn254::{big::{self, BIG}, bls::bls_hash_to_point, dbig::DBIG, ecp::{self, ECP}, ecp2::{self, ECP2}, fp::FP, fp2::FP2, pair, rom}, hmac, rand::{self, RAND}};

pub struct MercurialScheme {
    ell: usize, // length of keys & messages
    P: ECP,     // generator for the first group
    Phat: ECP2, // generator for the paired group
    r: BIG,     // order of the isomorphic paired groups
}

#[derive(Debug, Clone)]
pub struct Signature<T, U> {
    // a mercurial signature
    Z: T,
    Y: T,
    Yhat: U,
}

impl MercurialScheme {
    pub fn new(el: usize) -> MercurialScheme {
        MercurialScheme {
            ell: el,
            P: ecp::ECP::generator(),
            Phat: ecp2::ECP2::generator(),
            r: big::BIG::new_ints(&rom::CURVE_ORDER),
        }
    }

    pub fn randomZp(&self, rng: &mut rand::RAND_impl) -> big::BIG {
        let rho = big::BIG::randomnum(&self.r, rng);
        return rho;
    }

    pub fn odd_signer(&self) -> &dyn Signer<ECP2, ECP> {
        self
    }

    pub fn even_signer(&self) -> &dyn Signer<ECP, ECP2> {
        self
    }
}

pub trait Signer<T, U> {
    fn KeyGen(&self, rng: &mut rand::RAND_impl) -> (Vec<big::BIG>, Vec<T>);
    fn Sign(&self, sk: &Vec<big::BIG>, M: &Vec<U>, rng: &mut rand::RAND_impl) -> Signature<U, T>;
    fn Verify(&self, pk: &Vec<T>, M: &Vec<U>, sigma: &Signature<U, T>) -> bool;
    fn HashMessage(&self, M: &[u8]) -> U;
}

impl Signer<ECP2, ECP> for MercurialScheme {
    fn KeyGen(&self, rng: &mut rand::RAND_impl) -> (Vec<big::BIG>, Vec<ecp2::ECP2>) {
        // generates secret key sk, public key pk pair
        let mut sk: Vec<big::BIG> = Vec::with_capacity(self.ell);
        let mut pk: Vec<ecp2::ECP2> = Vec::with_capacity(self.ell);
        for _ in 0..(self.ell as u64) {
            let x = big::BIG::randomnum(&self.r, rng);
            let mut w = ecp2::ECP2::new();
            w.copy(&self.Phat);
            sk.push(x);
            pk.push(ecp2::ECP2::mul(&w, &x));
        }
        return (sk, pk);
    }

    fn Sign(&self, sk: &Vec<big::BIG>, M: &Vec<ecp::ECP>, rng: &mut rand::RAND_impl) -> Signature<ECP, ECP2> {
        // signs a message M using secret key sk
        let y = big::BIG::randomnum(&self.r, rng);
        let mut y_inv = big::BIG::new_copy(&y);
        big::BIG::invmodp(&mut y_inv, &self.r);
        let mut Z = M[0].mul(&sk[0]);
        for i in 1..self.ell {
            Z.add(&(M[i].mul(&sk[i])));
        }
        Z = Z.mul(&y);
        let Y = (&self.P).mul(&y_inv);
        let Yhat = (&self.Phat).mul(&y_inv);
        let sigma = Signature { Z: Z, Y: Y, Yhat: Yhat };
        return sigma;
    }

    fn Verify(&self, pk: &Vec<ecp2::ECP2>, M: &Vec<ecp::ECP>, sigma: &Signature<ECP, ECP2>) -> bool {
        // verfies that the signature sigma corresponds to public key pk
        // and message M
        let Z = &sigma.Z;
        let Y = &sigma.Y;
        let Yhat = &sigma.Yhat;
        let mut q1 = pair::fexp(&pair::ate(&pk[0], &M[0]));
        for i in 1..self.ell {
            q1.mul(&pair::fexp(&pair::ate(&pk[i], &M[i])));
        }
        let q2 = pair::fexp(&pair::ate(&Yhat, &Z));
        let q3 = pair::fexp(&pair::ate(&self.Phat, &Y));
        let q4 = pair::fexp(&pair::ate(&Yhat, &self.P));
        return q1.equals(&q2) && q3.equals(&q4);
    }

    fn HashMessage(&self, M: &[u8]) -> ECP {
        bls_hash_to_point(M)
    }
}

impl Signer<ECP, ECP2> for MercurialScheme {
    fn KeyGen(&self, rng: &mut rand::RAND_impl) -> (Vec<big::BIG>, Vec<ECP>) {
        // generates secret key sk, public key pk pair
        let mut sk: Vec<big::BIG> = Vec::with_capacity(self.ell);
        let mut pk: Vec<ecp::ECP> = Vec::with_capacity(self.ell);
        for _ in 0..(self.ell as u64) {
            let x = big::BIG::randomnum(&self.r, rng);
            let mut w = ecp::ECP::new();
            w.copy(&self.P);
            sk.push(x);
            pk.push(ecp::ECP::mul(&w, &x));
        }
        return (sk, pk);
    }

    fn Sign(&self, sk: &Vec<big::BIG>, M: &Vec<ECP2>, rng: &mut rand::RAND_impl) -> Signature<ECP2, ECP> {
        // signs a message M using secret key sk
        let y = big::BIG::randomnum(&self.r, rng);
        let mut y_inv = big::BIG::new_copy(&y);
        big::BIG::invmodp(&mut y_inv, &self.r);
        let mut Z = M[0].mul(&sk[0]);
        for i in 1..self.ell {
            Z.add(&(M[i].mul(&sk[i])));
        }
        Z = Z.mul(&y);
        let Y = (&self.Phat).mul(&y_inv);
        let Yhat = (&self.P).mul(&y_inv);
        let sigma = Signature { Z: Z, Y: Y, Yhat: Yhat };
        return sigma;
    }

    fn Verify(&self, pk: &Vec<ECP>, M: &Vec<ECP2>, sigma: &Signature<ECP2, ECP>) -> bool {
        // verfies that the signature sigma corresponds to public key pk
        // and message M
        let Z = &sigma.Z;
        let Y = &sigma.Y;
        let Yhat = &sigma.Yhat;
        let mut q1 = pair::fexp(&pair::ate(&M[0], &pk[0]));
        for i in 1..self.ell {
            q1.mul(&pair::fexp(&pair::ate(&M[i], &pk[i])));
        }
        let q2 = pair::fexp(&pair::ate(&Z, &Yhat));
        let q3 = pair::fexp(&pair::ate(&Y, &self.P));
        let q4 = pair::fexp(&pair::ate(&self.Phat, &Yhat));
        return q1.equals(&q2) && q3.equals(&q4);
    }

    fn HashMessage(&self, M: &[u8]) -> ECP2 {
        let dst = "BLS_SIG_BN254G2_XMD:SHA-256_SVDW_RO_NUL_";

        let mut u: [FP2; 2] = [FP2::new(), FP2::new()];
        hash_to_field(hmac::MC_SHA2, ecp::HASH_TYPE, &mut u, dst.as_bytes(), M, 2);

        let mut P = ECP2::map2point(&u[0]);
        let P1 = ECP2::map2point(&u[1]);

        P.add(&P1);
        P.cfp();
        P.affine();
        P
    }
}

fn hash_to_field(hash: usize,hlen: usize ,u: &mut [FP2], dst: &[u8],m: &[u8],ctr: usize) {
    let q = BIG::new_ints(&rom::MODULUS);
    let nbq=q.nbits();
    let el = ceil(nbq+ecp::AESKEY*8,8);

    let mut okm: [u8;256]=[0;256];
    let mut fd: [u8;128]=[0;128];

    hmac::xmd_expand(hash,hlen,&mut okm,el*ctr,&dst,&m);
    for i in 0..ctr {
        for j in 0..el {
            fd[j]=okm[el*i+j];
        }
        u[i]=FP2::new_big(&DBIG::frombytes(&fd[0 .. el]).ctdmod(&q,8*el-nbq));
    }
}

fn ceil(a: usize,b: usize) -> usize {
    (a-1)/b+1
}

pub fn prepare_rng() -> rand::RAND_impl {
    // sets up a random number generator
    let mut raw: [u8; 100] = [0; 100];
    let mut rng = rand::RAND_impl::new();
    rng.clean();
    for i in 0..100 {
        raw[i] = i as u8
    }
    rng.seed(100, &raw);
    return rng;
}

#[cfg(test)]
mod test {
    use mcore::bn254::{big::BIG, ecp::ECP, ecp2::ECP2};

    use super::{MercurialScheme, Signer, prepare_rng};

    #[test]
    fn test_sign_verify_odd() {
        let scheme = MercurialScheme::new(2);
        let mut rng = prepare_rng();
        let (sk, pk) = scheme.odd_signer().KeyGen(&mut rng);

        let M = vec![
            scheme.odd_signer().HashMessage(b"hello"),
            scheme.odd_signer().HashMessage(b"world")
        ];

        let sigma = scheme.Sign(&sk, &M, &mut rng);

        println!("{:?}", &sigma);

        let verify = scheme.Verify(&pk, &M, &sigma);

        println!("valid: {}", verify);
    }

    #[test]
    fn test_sign_verify_even() {
        let scheme = MercurialScheme::new(2);
        let signer = scheme.even_signer();

        let mut rng = prepare_rng();
        let (sk, pk) = signer.KeyGen(&mut rng);

        let M = vec![
            signer.HashMessage(b"hello"),
            signer.HashMessage(b"world")
        ];

        let sigma = signer.Sign(&sk, &M, &mut rng);

        println!("{:?}", &sigma);

        let verify = signer.Verify(&pk, &M, &sigma);

        println!("valid: {}", verify);
    }
}