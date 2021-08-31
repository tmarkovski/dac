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

        let (sk0, pk0) = scheme.as_even().KeyGen(&mut rng);

        DelegatableAnonCredScheme {
            ell: ell,
            mss: scheme,
            pk0: pk0.clone(),
            sk0: sk0,
            nym0: (pk0, None),
        }
    }

    pub fn KeyGen(&self) -> (EvenKeyPair, OddKeyPair) {
        let mut rng = prepare_rng();
        let (sk_even, pk_even) = self.mss.as_even().KeyGen(&mut rng);
        let (sk_odd, pk_odd) = self.mss.as_odd().KeyGen(&mut rng);
        return ((sk_even, pk_even), (sk_odd, pk_odd));
    }

    pub fn NymGen(&self, even: EvenKeyPair, odd: OddKeyPair) -> (EvenKeyPair, OddKeyPair) {
        let mut rng = prepare_rng();

        let rho_even = self.mss.randomZp(&mut rng);
        let sk_even = self.mss.ConvertSK(even.0, &rho_even);
        let nym_even = self.mss.as_even().ConvertPK(even.1, &rho_even);

        let rho_odd = self.mss.randomZp(&mut rng);
        let sk_odd = self.mss.ConvertSK(odd.0, &rho_odd);
        let nym_odd = self.mss.as_odd().ConvertPK(odd.1, &rho_odd);

        return ((sk_even, nym_even), (sk_odd, nym_odd));
    }

    pub fn IssueFirst(&self, nym1: OddPublicKey) -> ChainEntry {
        let mut rng = prepare_rng();

        let sig1 = self.mss.as_even().Sign(&self.sk0, &nym1, &mut rng);
        return ChainEntry::Odd(nym1, sig1);
    }

    pub fn IssueNext(&self, cred_chain: &mut Vec<ChainEntry>, new_nym: PublicKey, sk: SecretKey) {
        let mut rng = prepare_rng();

        let mut rho = self.mss.randomZp(&mut rng);
        let entry_0 = cred_chain[0].as_odd();

        let (nym_list_0, sig_list_0) = self
            .mss
            .as_even()
            .ChangeRepresentation(entry_0.0, entry_0.1, &rho, &mut rng);

        // assert!(self.mss.as_even().Verify(&self.pk0, &nym_list_0, &sig_list_0));
        cred_chain[0] = ChainEntry::Odd(nym_list_0, sig_list_0);

        for i in 0..(cred_chain.len() - 1) {
            if i % 2 == 0 {
                let sig_tilde = self
                    .mss
                    .as_odd()
                    .ConvertSignature(cred_chain[i + 1].as_even().1, &rho, &mut rng);
                rho = self.mss.randomZp(&mut rng);
                let new_entry =
                    self.mss
                        .as_odd()
                        .ChangeRepresentation(cred_chain[i + 1].as_even().0, sig_tilde, &rho, &mut rng);
                cred_chain[i + 1] = ChainEntry::Even(new_entry.0, new_entry.1);
                self.mss.as_odd().Verify(
                    &cred_chain[i].as_odd().0,
                    &cred_chain[i + 1].as_even().0,
                    &cred_chain[i + 1].as_even().1,
                );
            } else {
                let sig_tilde = self
                    .mss
                    .as_even()
                    .ConvertSignature(cred_chain[i + 1].as_odd().1, &rho, &mut rng);
                rho = self.mss.randomZp(&mut rng);
                let new_entry =
                    self.mss
                        .as_even()
                        .ChangeRepresentation(cred_chain[i + 1].as_odd().0, sig_tilde, &rho, &mut rng);
                cred_chain[i + 1] = ChainEntry::Odd(new_entry.0, new_entry.1);
                self.mss.as_even().Verify(
                    &cred_chain[i].as_even().0,
                    &cred_chain[i + 1].as_odd().0,
                    &cred_chain[i + 1].as_odd().1,
                );
            }
        }

        let sk_ = self.mss.ConvertSK(sk, &rho);

        if cred_chain.len() % 2 == 0 {
            cred_chain.push(ChainEntry::Odd(
                new_nym.as_odd(),
                self.mss.as_even().Sign(&sk_, &new_nym.as_odd(), &mut rng),
            ))
        } else {
            cred_chain.push(ChainEntry::Even(
                new_nym.as_even(),
                self.mss.as_odd().Sign(&sk_, &new_nym.as_even(), &mut rng),
            ))
        }
    }

    pub fn VerifyChain(&self, cred_chain: &Vec<ChainEntry>) -> bool {
        if !self
            .mss
            .as_even()
            .Verify(&self.pk0, &cred_chain[0].as_odd().0, &cred_chain[0].as_odd().1)
        {
            return false;
        }

        for i in 0..(cred_chain.len() - 1) {
            if i % 2 == 0 {
                if !self.mss.as_odd().Verify(
                    &cred_chain[i].as_odd().0,
                    &cred_chain[i + 1].as_even().0,
                    &cred_chain[i + 1].as_even().1,
                ) {
                    return false;
                }
            } else {
                if !self.mss.as_even().Verify(
                    &cred_chain[i].as_even().0,
                    &cred_chain[i + 1].as_odd().0,
                    &cred_chain[i + 1].as_odd().1,
                ) {
                    return false;
                }
            }
        }
        return true;
    }
}

type SecretKey = Vec<BIG>;
type OddPublicKey = Vec<ECP2>;
type EvenPublicKey = Vec<ECP>;

type EvenKeyPair = (SecretKey, EvenPublicKey);
type OddKeyPair = (SecretKey, OddPublicKey);

type OddSignature = Signature<ECP, ECP2>;
type EvenSignature = Signature<ECP2, ECP>;

pub enum ChainEntry {
    Odd(OddPublicKey, EvenSignature),
    Even(EvenPublicKey, OddSignature),
}

pub enum PublicKey {
    Odd(OddPublicKey),
    Even(EvenPublicKey),
}

impl PublicKey {
    pub fn as_odd(&self) -> OddPublicKey {
        match self {
            PublicKey::Odd(x) => x.clone(),
            PublicKey::Even(_) => panic!("not odd"),
        }
    }
    pub fn as_even(&self) -> EvenPublicKey {
        match self {
            PublicKey::Odd(_) => panic!("not even"),
            PublicKey::Even(x) => x.clone(),
        }
    }
}

impl ChainEntry {
    pub fn as_odd(&self) -> (OddPublicKey, EvenSignature) {
        match self {
            ChainEntry::Odd(x, y) => (x.to_owned(), y.to_owned()),
            ChainEntry::Even(_, _) => panic!("not odd"),
        }
    }
    pub fn as_even(&self) -> (EvenPublicKey, OddSignature) {
        match self {
            ChainEntry::Even(x, y) => (x.to_owned(), y.to_owned()),
            ChainEntry::Odd(_, _) => panic!("not even"),
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
        dac.IssueNext(&mut cred_chain, PublicKey::Even(nym_even2), sk_odd1);

        assert!(dac.VerifyChain(&cred_chain));

        // user 3 generates keys, nyms, & gets on the credential chain
        let (even_keys3, odd_keys3) = dac.KeyGen();
        let (_, (sk_odd3, nym_odd3)) = dac.NymGen(even_keys3, odd_keys3);
        dac.IssueNext(&mut cred_chain, PublicKey::Odd(nym_odd3), sk_even2);

        assert!(dac.VerifyChain(&cred_chain));
    }
}
