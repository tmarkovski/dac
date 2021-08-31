use core::panic;

use mcore::{
    bn254::ecp2::*,
    bn254::{big::*, ecp::*},
};

use crate::mss::{prepare_rng, MercurialScheme, Signature, Signer};

pub struct DelegatableAnonCredScheme {
    pub ell: usize,
    pub mss: MercurialScheme,
    pub pk0: Vec<ECP>,
    pub sk0: Vec<BIG>,
    pub nym0: (Vec<ECP>, Option<Vec<BIG>>),
}

impl DelegatableAnonCredScheme {
    pub fn new(ell: usize) -> Self {
        let scheme = MercurialScheme::new(ell);
        let mut rng = prepare_rng();

        let (sk0, pk0) = scheme.as_g1().KeyGen(&mut rng);

        DelegatableAnonCredScheme {
            ell: ell,
            mss: scheme,
            pk0: pk0.clone(),
            sk0: sk0,
            nym0: (pk0, None),
        }
    }

    pub fn KeyGen(&self) -> (KeyPairG1, KeyPairG2) {
        let mut rng = prepare_rng();
        let (sk_even, pk_even) = self.mss.as_g1().KeyGen(&mut rng);
        let (sk_odd, pk_odd) = self.mss.as_g2().KeyGen(&mut rng);
        return ((sk_even, pk_even), (sk_odd, pk_odd));
    }

    pub fn NymGen(&self, even: KeyPairG1, odd: KeyPairG2) -> (KeyPairG1, KeyPairG2) {
        let mut rng = prepare_rng();

        let rho_even = self.mss.randomZp(&mut rng);
        let sk_even = self.mss.ConvertSK(even.0, &rho_even);
        let nym_even = self.mss.as_g1().ConvertPK(even.1, &rho_even);

        let rho_odd = self.mss.randomZp(&mut rng);
        let sk_odd = self.mss.ConvertSK(odd.0, &rho_odd);
        let nym_odd = self.mss.as_g2().ConvertPK(odd.1, &rho_odd);

        return ((sk_even, nym_even), (sk_odd, nym_odd));
    }

    pub fn IssueFirst(&self, nym1: PublicKeyG2) -> ChainEntry {
        let mut rng = prepare_rng();

        let sig1 = self.mss.as_g1().Sign(&self.sk0, &nym1, &mut rng);
        return ChainEntry::G1(nym1, sig1);
    }

    pub fn IssueNext(&self, cred_chain: &mut Vec<ChainEntry>, new_nym: PublicKey, sk: SecretKey) {
        let mut rng = prepare_rng();

        let mut rho = self.mss.randomZp(&mut rng);
        let entry_0 = cred_chain[0].as_g2();

        let (nym_list_0, sig_list_0) = self
            .mss
            .as_g1()
            .ChangeRepresentation(entry_0.0, entry_0.1, &rho, &mut rng);

        // assert!(self.mss.as_even().Verify(&self.pk0, &nym_list_0, &sig_list_0));
        cred_chain[0] = ChainEntry::G1(nym_list_0, sig_list_0);

        for i in 0..(cred_chain.len() - 1) {
            if i % 2 == 0 {
                let sig_tilde = self
                    .mss
                    .as_g2()
                    .ConvertSignature(cred_chain[i + 1].as_g1().1, &rho, &mut rng);
                rho = self.mss.randomZp(&mut rng);
                let new_entry =
                    self.mss
                        .as_g2()
                        .ChangeRepresentation(cred_chain[i + 1].as_g1().0, sig_tilde, &rho, &mut rng);
                cred_chain[i + 1] = ChainEntry::G2(new_entry.0, new_entry.1);
                self.mss.as_g2().Verify(
                    &cred_chain[i].as_g2().0,
                    &cred_chain[i + 1].as_g1().0,
                    &cred_chain[i + 1].as_g1().1,
                );
            } else {
                let sig_tilde = self
                    .mss
                    .as_g1()
                    .ConvertSignature(cred_chain[i + 1].as_g2().1, &rho, &mut rng);
                rho = self.mss.randomZp(&mut rng);
                let new_entry =
                    self.mss
                        .as_g1()
                        .ChangeRepresentation(cred_chain[i + 1].as_g2().0, sig_tilde, &rho, &mut rng);
                cred_chain[i + 1] = ChainEntry::G1(new_entry.0, new_entry.1);
                self.mss.as_g1().Verify(
                    &cred_chain[i].as_g1().0,
                    &cred_chain[i + 1].as_g2().0,
                    &cred_chain[i + 1].as_g2().1,
                );
            }
        }

        let sk_ = self.mss.ConvertSK(sk, &rho);

        if cred_chain.len() % 2 == 0 {
            cred_chain.push(ChainEntry::G1(
                new_nym.as_g2(),
                self.mss.as_g1().Sign(&sk_, &new_nym.as_g2(), &mut rng),
            ))
        } else {
            cred_chain.push(ChainEntry::G2(
                new_nym.as_g1(),
                self.mss.as_g2().Sign(&sk_, &new_nym.as_g1(), &mut rng),
            ))
        }
    }

    pub fn VerifyChain(&self, cred_chain: &Vec<ChainEntry>) -> bool {
        if !self
            .mss
            .as_g1()
            .Verify(&self.pk0, &cred_chain[0].as_g2().0, &cred_chain[0].as_g2().1)
        {
            return false;
        }

        for i in 0..(cred_chain.len() - 1) {
            if i % 2 == 0 {
                if !self.mss.as_g2().Verify(
                    &cred_chain[i].as_g2().0,
                    &cred_chain[i + 1].as_g1().0,
                    &cred_chain[i + 1].as_g1().1,
                ) {
                    return false;
                }
            } else {
                if !self.mss.as_g1().Verify(
                    &cred_chain[i].as_g1().0,
                    &cred_chain[i + 1].as_g2().0,
                    &cred_chain[i + 1].as_g2().1,
                ) {
                    return false;
                }
            }
        }
        return true;
    }
}

type SecretKey = Vec<BIG>;
type PublicKeyG2 = Vec<ECP2>;
type PublicKeyG1 = Vec<ECP>;

type KeyPairG1 = (SecretKey, PublicKeyG1);
type KeyPairG2 = (SecretKey, PublicKeyG2);

type SignatureG2 = Signature<ECP, ECP2>;
type SignatureG1 = Signature<ECP2, ECP>;

pub enum ChainEntry {
    G1(PublicKeyG2, SignatureG1),
    G2(PublicKeyG1, SignatureG2),
}

pub enum PublicKey {
    G2(PublicKeyG2),
    G1(PublicKeyG1),
}

impl PublicKey {
    pub fn as_g2(&self) -> PublicKeyG2 {
        match self {
            PublicKey::G2(x) => x.clone(),
            PublicKey::G1(_) => panic!("not g2"),
        }
    }
    pub fn as_g1(&self) -> PublicKeyG1 {
        match self {
            PublicKey::G2(_) => panic!("not g1"),
            PublicKey::G1(x) => x.clone(),
        }
    }
}

impl ChainEntry {
    pub fn as_g2(&self) -> (PublicKeyG2, SignatureG1) {
        match self {
            ChainEntry::G1(x, y) => (x.to_owned(), y.to_owned()),
            ChainEntry::G2(_, _) => panic!("not odd"),
        }
    }
    pub fn as_g1(&self) -> (PublicKeyG1, SignatureG2) {
        match self {
            ChainEntry::G2(x, y) => (x.to_owned(), y.to_owned()),
            ChainEntry::G1(_, _) => panic!("not even"),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_dac() {
        let dac = DelegatableAnonCredScheme::new(3);
        let mut cred_chain: Vec<ChainEntry> = vec![];

        // user 1 generates keys, nyms, & gets on the credential chain
        let (even_keys1, odd_keys1) = dac.KeyGen();
        let (_, (sk_odd1, nym_odd1)) = dac.NymGen(even_keys1, odd_keys1);
        let entry = dac.IssueFirst(nym_odd1);
        cred_chain.push(entry);

        assert!(dac.VerifyChain(&cred_chain));

        // user 2 generates keys, nyms, & gets on the credential chain
        let (even_keys2, odd_keys2) = dac.KeyGen();
        let ((sk_even2, nym_even2), _) = dac.NymGen(even_keys2, odd_keys2);
        dac.IssueNext(&mut cred_chain, PublicKey::G1(nym_even2), sk_odd1);

        assert!(dac.VerifyChain(&cred_chain));

        // user 3 generates keys, nyms, & gets on the credential chain
        let (even_keys3, odd_keys3) = dac.KeyGen();
        let (_, (sk_odd3, nym_odd3)) = dac.NymGen(even_keys3, odd_keys3);
        dac.IssueNext(&mut cred_chain, PublicKey::G2(nym_odd3), sk_even2);

        assert!(dac.VerifyChain(&cred_chain));
    }
}
