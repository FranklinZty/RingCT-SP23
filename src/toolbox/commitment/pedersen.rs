use ark_ec::CurveGroup;
use ark_std::{end_timer, marker::PhantomData, rand::Rng, start_timer, UniformRand};

use std::fmt::Debug;
use crate::toolbox::errors::CommitmentErrors;
use crate::toolbox::commitment::{PedersenOpening, PedersenParams};

/// Pedersen (Vector) Commitment with form
/// com(vec_m, r) = vec_g^vec_m + h^r (perfectly hiding)
#[derive(Clone, Debug)]
pub struct PedersenCommitmentScheme<C: CurveGroup> {
    phantom: PhantomData<C>,
}

impl<C: CurveGroup> PedersenCommitmentScheme<C> {
    /// Setup algorithm generates public parameters for Pedersen Commitment includes
    /// - h: a generator
    /// - vec_g: a vector of generators in length of supported_size
    pub fn setup<R: Rng>(
        rng: &mut R,
        supported_size: usize,
    ) -> Result<PedersenParams<C>, CommitmentErrors> {
        // h_scalar should be dropped
        let h_scalar = C::ScalarField::rand(rng);
        let g = C::generator();
        // generator vector with unknown DL relation
        let generators = vec![C::Affine::rand(rng); supported_size];
        let pp = PedersenParams {
            generator: g.mul(h_scalar),
            vec_gen: generators,
        };
        Ok(pp)
    }

    /// Commit algorithm takes inputs as
    /// - PublicParams
    /// - m: message vector
    /// - r: random element for hiding
    /// then outputs
    /// - cm: a pedersen vector commitment
    pub fn commit(
        params: &PedersenParams<C>,
        m: &Vec<C::ScalarField>,
        r: &C::ScalarField,
        info: &str,
    ) -> Result<C, CommitmentErrors> {
        let log_info = "generating pedersen commitment ".to_owned() + info;
        let start = start_timer!(|| log_info);
        let params = params;
        if m.len() != params.vec_gen.len() {
            return Err(CommitmentErrors::InvalidParameters(
                "message length should equal to the generator length".to_string(),
            ));
        }
        let msm = C::msm(&params.vec_gen, m).unwrap();
        let cm: C = params.generator.mul(r) + msm;
        end_timer!(start);
        Ok(cm)
    }

    /// Open algorithm outputs the following as the opening of commitment
    /// - m: message vector
    /// - r: random element for hiding
    pub fn open(
        m: &Vec<C::ScalarField>,
        r: &C::ScalarField,
    ) -> Result<PedersenOpening<C>, CommitmentErrors> {
        Ok(PedersenOpening {
            message: m.clone(),
            random: r.clone(),
        })
    }

    /// Verify algorithm takes inputs as
    /// - PublicParams
    /// - cm: commitment
    /// - open: opening includes m and r
    /// then outputs
    /// - cm: a pedersen vector commitment
    pub fn verify(
        params: &PedersenParams<C>,
        cm: &C,
        open: &PedersenOpening<C>,
    ) -> Result<bool, CommitmentErrors> {
        let start = start_timer!(|| "checking pedersen commitment...");
        let params = params;
        let msm = C::msm(&params.vec_gen, &open.message).unwrap();
        let cm_prime = params.generator.mul(open.random) + msm;
        end_timer!(start);
        Ok(&cm_prime == cm)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::toolbox::vec::vec_u64_to_F;
    use ark_bls12_381::{Fr as G1Fr, G1Projective};
    use ark_secp256k1::{Fr, Projective};
    use test::Bencher;

    #[test]
    fn test_pedersen() {
        let mut rng = ark_std::test_rng();
        let supported_size = 10;
        let params =
            PedersenCommitmentScheme::<Projective>::setup(&mut rng, supported_size).unwrap();
        let m: [u64; 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
        let field_m: Vec<Fr> = vec_u64_to_F(&m);
        let r = Fr::rand(&mut rng);
        let cm = PedersenCommitmentScheme::<Projective>::commit(&params, &field_m, &r, "cm").unwrap();
        let opening = PedersenCommitmentScheme::<Projective>::open(&field_m, &r).unwrap();
        assert_eq!(
            PedersenCommitmentScheme::<Projective>::verify(&params, &cm, &opening).unwrap(),
            true
        );
    }

    #[bench]
    fn bench_group(b: &mut Bencher) {
        let mut rng = ark_std::test_rng();
        let supported_size = 4096;
        let params =
            PedersenCommitmentScheme::<G1Projective>::setup(&mut rng, supported_size).unwrap();

        let m: Vec<G1Fr> = vec![G1Fr::rand(&mut rng); supported_size];
        let r = G1Fr::rand(&mut rng);

        b.iter(|| PedersenCommitmentScheme::<G1Projective>::commit(&params, &m, &r, "cm").unwrap());
    }
}
