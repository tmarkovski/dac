use core::panic;

use mcore::bn254::*;
use mcore::{
    bn254::ecp2::*,
    bn254::{big::*, bls::bls_hash_to_point, ecp::*},
    rand::RAND_impl,
};

use crate::mss::{prepare_rng, MercurialScheme, Signature, Signer};

struct DelegatableAnonCredScheme {
    ell: usize,
    mss: MercurialScheme,
    pk0: Vec<ECP>,
    sk0: Vec<BIG>,
    nym0: (Vec<ECP>, Option<Vec<BIG>>),
}

impl DelegatableAnonCredScheme {
    fn new(ell: usize) -> Self {
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

    fn KeyGen(&self) -> (EvenKeyPair, OddKeyPair) {
        let mut rng = prepare_rng();
        let (sk_even, pk_even) = self.mss.as_even().KeyGen(&mut rng);
        let (sk_odd, pk_odd) = self.mss.as_odd().KeyGen(&mut rng);
        return ((sk_even, pk_even), (sk_odd, pk_odd));
    }

    fn NymGen(&self, even: EvenKeyPair, odd: OddKeyPair) -> (EvenKeyPair, OddKeyPair) {
        let mut rng = prepare_rng();

        let rho_even = self.mss.randomZp(&mut rng);
        let sk_even = self.mss.ConvertSK(even.0, &rho_even);
        let nym_even = self.mss.as_even().ConvertPK(even.1, &rho_even);

        let rho_odd = self.mss.randomZp(&mut rng);
        let sk_odd = self.mss.ConvertSK(odd.0, &rho_odd);
        let nym_odd = self.mss.as_odd().ConvertPK(odd.1, &rho_odd);

        return ((sk_even, nym_even), (sk_odd, nym_odd));
    }

    fn IssueFirst(&self, nym1: OddPublicKey) -> ChainEntry {
        let mut rng = prepare_rng();

        let sig1 = self.mss.as_even().Sign(&self.sk0, &nym1, &mut rng);
        return ChainEntry::Odd(nym1, sig1);
    }

    fn IssueNext(&self, cred_chain: &mut Vec<ChainEntry>, new_nym: PublicKey, sk: SecretKey) {
        // nym_list, sig_list = cred_chain
        // assert len(nym_list) == len(sig_list)

        let mut rng = prepare_rng();

        let rho = self.mss.randomZp(&mut rng);
        let entry_0 = cred_chain[0].as_odd();

        let (nym_list_0, sig_list_0) = self
            .mss
            .as_even()
            .ChangeRepresentation(entry_0.0, entry_0.1, &rho, &mut rng);

        assert!(self.mss.as_even().Verify(&self.pk0, &nym_list_0, &sig_list_0));
        cred_chain[0] = ChainEntry::Odd(nym_list_0, sig_list_0);

        for i in 0..(cred_chain.len() - 1) {
            if i % 2 == 0 {
                let sig_tilde = self
                    .mss
                    .as_odd()
                    .ConvertSignature(cred_chain[i + 1].as_even().1, &rho, &mut rng);
                let rho = self.mss.randomZp(&mut rng);
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
                let rho = self.mss.randomZp(&mut rng);
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
            //     # Note: MSS1 & MSS2 share the same functions RandomZp, ChangeRep, & ConvertSig
            //     MSS = self.MSS1 if i % 2 == 0 else self.MSS2
            //     sig_tilde = MSS.ConvertSig(
            //         nym_list[i], nym_list[i + 1], sig_list[i + 1], rho
            //     )
            //     rho = MSS.RandomZp()
            //     nym_list[i + 1], sig_list[i + 1] = MSS.ChangeRep(
            //         nym_list[i], nym_list[i + 1], sig_tilde, rho
            //     )
            //     assert MSS.Verify(nym_list[i], nym_list[i + 1], sig_list[i + 1])
        }

        let sk_ = self.mss.ConvertSK(sk, &rho);
        // nym_list.append(new_nym)
        // MSS = self.MSS1 if len(nym_list) % 2 == 0 else self.MSS2
        // sk = MSS.ConvertSK(sk, rho)
        // sig_list.append(MSS.Sign(sk, new_nym))
        // assert MSS.Verify(nym_list[-2], nym_list[-1], sig_list[-1])
        // return nym_list, sig_list
    }

    fn VerifyChain(&self, cred_chain: &Vec<ChainEntry>) -> bool {
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

enum ChainEntry {
    Odd(OddPublicKey, EvenSignature),
    Even(EvenPublicKey, OddSignature),
}

enum PublicKey {
    Odd(OddPublicKey),
    Even(EvenPublicKey),
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

mod test {
    use mcore::bn254::ecp::ECP;

    use super::{ChainEntry, DelegatableAnonCredScheme};

    #[test]
    fn test_keygen() {
        // user 1 generates keys, nyms, & gets on the credential chain
        let dac = DelegatableAnonCredScheme::new(2);
        let (even_keys1, odd_keys1) = dac.KeyGen();
        let ((sk_even1, nym_even1), (sk_odd1, nym_odd1)) = dac.NymGen(even_keys1, odd_keys1);

        let mut cred_chain: Vec<ChainEntry> = vec![];
        let entry = dac.IssueFirst(nym_odd1);
        cred_chain.insert(0, entry);

        dac.VerifyChain(&cred_chain);
    }
}
