use std::marker::PhantomData;
use ark_ec::CurveGroup;
use ark_std::{end_timer, rand::Rng, start_timer, UniformRand, Zero, One};
use crate::toolbox::commitment::pedersen::PedersenCommitmentScheme;
use crate::rangeproof::structs::{RangeProof, RangeProofParams, Openings};
use crate::toolbox::sigma::{transcript::ProofTranscript, SigmaProtocol};
use crate::toolbox::errors::SigmaErrors;
use crate::toolbox::vec::*;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RangeProofScheme<C>
where
    C: CurveGroup,
{
    phantom: PhantomData<C>,
}

/// Implement a sigma protocol as a ring signature scheme (without compression), including 5-move:
/// Relation: P knows a sk to a pk among the vector vec_pk
/// Formalized Relation: P knows a sk satisfying <vec_pk, vec_b> = com(sk)
impl<C> SigmaProtocol<C> for RangeProofScheme<C>
where
    C: CurveGroup,
{
    /// public parameters
    type PublicParams = RangeProofParams<C>;
    /// witness
    type Witness = (Vec<u128>, Vec<C::ScalarField>);
    /// witness commitments
    type Commitments = Vec<C::Affine>;
    // challenge
    type Challenge = Vec<C::ScalarField>;
    /// proof
    type Proof = RangeProof<C>;

    fn setup<R: Rng>(
        rng: &mut R,
        wit: &mut Self::Witness, // secret values
        _msg: Option<&String>,
        supported_size: usize, // value size (maximum bits)
    ) -> Result<Self::PublicParams, SigmaErrors> {
        let value_num = wit.0.len();
        let mut com_parameters = Vec::with_capacity(value_num*2);
        let mut val_com_parameters = Vec::with_capacity(value_num);
        let mut com_value = Vec::with_capacity(value_num);
        for i in 0..value_num {
            // sample generators for binary commitments
            let com_params_temp = PedersenCommitmentScheme::<C>::setup(rng, supported_size)?;
            com_parameters.push(com_params_temp);
            let com_params_temp = PedersenCommitmentScheme::<C>::setup(rng, supported_size)?;
            com_parameters.push(com_params_temp);

            // sample generators for value commitments
            let val_params_temp = PedersenCommitmentScheme::<C>::setup(rng, 1)?;
            // compute the value commitment
            let random = C::ScalarField::rand(rng);
            let value_num_term = PedersenCommitmentScheme::<C>::commit(&val_params_temp, &vec![C::ScalarField::from(wit.0[i])], &random, "value")?;

            wit.1.push(random);
            com_value.push(value_num_term.into_affine());
            val_com_parameters.push(val_params_temp);

        }

        com_parameters.extend(val_com_parameters);

        Ok(RangeProofParams {
            num_witness: wit.0.len(),
            num_pub_inputs: supported_size,
            com_parameters,
            com_value,
        })
    }

    fn prove<R: Rng>(
        rng: &mut R,
        params: &Self::PublicParams,
        wit: &Self::Witness,
    ) -> Result<Self::Proof, SigmaErrors> {
        // initialization
        let start = start_timer!(|| "running sigma protocol prove algorithm...");
        let mut transcript = ProofTranscript::<C::ScalarField>::new(b"RingSignature");
        transcript.append_serializable_element(b"public list", &params.com_value)?;
        let val_num = wit.0.len();

        // parse commitment parameters
        let bin_com_g_param = &params.com_parameters[0..val_num].to_vec();
        let bin_com_h_param = &params.com_parameters[val_num..2*val_num].to_vec();
        let val_com_param = &params.com_parameters[2*val_num..].to_vec();

        // parse wit as vec_sk and vec_b
        let vec_val = wit.0.clone();
        let vec_rand = wit.1.clone();

        // convert values to binary vectors in F^n
        let mut vec_b0 = Vec::<Vec<C::ScalarField>>::with_capacity(val_num);
        let mut vec_b1 = Vec::<Vec<C::ScalarField>>::with_capacity(val_num);
        for val in vec_val {
            let temp = u128_to_bin(val);
            vec_b0.push(temp.clone());
            let temp_inverse: Vec<C::ScalarField> = temp.iter()
                .map(|&b_i| C::ScalarField::one() - b_i)
                .collect();
            vec_b1.push(temp_inverse.clone());
        }

        // sanity check
        // b_0 + b_1 = 1^n
        // b_0 \circ b_1 = 0^n
        for i in 0..val_num {
            let constraint_1 = vec_b0[i].iter()
                .zip(vec_b1[i].iter())
                .all(|(&b0_i, &b1_i)| b0_i + b1_i == C::ScalarField::one());
            let constraint_2 = vec_b0[i].iter()
                .zip(vec_b1[i].iter())
                .all(|(&b0_i, &b1_i)| b0_i * b1_i == C::ScalarField::zero());
            assert!(constraint_1 && constraint_2);
        }

        // computes batch commitment A, B for all vec_b0, vec_b1
        let alpha = C::ScalarField::rand(rng);
        let beta = C::ScalarField::rand(rng);
        let vec_r0 = vec![vec![C::ScalarField::rand(rng); vec_b0[0].len()]; val_num];
        let vec_r1 = vec![vec![C::ScalarField::rand(rng); vec_b1[0].len()]; val_num];

        let com_A = PedersenCommitmentScheme::batch_commit(&bin_com_g_param, &vec_b0, &alpha, "on b0")?
            + PedersenCommitmentScheme::batch_commit(&bin_com_h_param, &vec_b1, &C::ScalarField::zero(), "on b1")?;
        let com_B = PedersenCommitmentScheme::batch_commit(&bin_com_g_param, &vec_r0, &beta, "on r0")?
            + PedersenCommitmentScheme::batch_commit(&bin_com_h_param, &vec_r1, &C::ScalarField::zero(), "on r1")?;

        // P->V: A,B
        transcript.append_serializable_element(b"commitments A,B", &[com_A, com_B])?;

        // V->P: challenges y,z
        let y = transcript.get_and_append_challenge(b"challenge y")?;
        let z = transcript.get_and_append_challenge(b"challenge z")?;

        /***
        // t1 = <r_0 \circ y^n, z*1^n + b_1> + <(b0 + z*1^n) \circ y^n, r_1>
        let powers_yn = generate_powers(y, params.num_pub_inputs);
        let vec_z1n = vec![z; params.num_pub_inputs];
        let vec_r0_yn = hadamard_product(&vec_r0, &powers_yn);
        let vec_z1n_b1 = vec_add(&vec_z1n, &vec_b1);
        let vec_b0_z1n_yn = hadamard_product(&vec_add(&vec_z1n, &vec_b0), &powers_yn);
        let t1 = inner_product(&vec_r0_yn, &vec_z1n_b1) + inner_product(&vec_b0_z1n_yn, &vec_r1);
        // t2 = <r0 \circ y^n, r_1>
        let t2 = inner_product(&vec_r0_yn, &vec_r1);

        // computes
        // E = P^{y^n \circ r_0} Com_{ck}(0; -r_s)
        // T1 = v^{t1}u^{tau1}
        // T2 = v^{t2}u^{tau2}
        let rs = C::ScalarField::rand(rng);
        let neg_rs = -rs.clone();
        let tau1 = C::ScalarField::rand(rng);
        let tau2 = C::ScalarField::rand(rng);

        let com_E = C::msm(&params.vec_pk, &vec_r0_yn).unwrap() + PedersenCommitmentScheme::commit(&param_key, &vec![neg_rs], &C::ScalarField::zero(), "E")?;
        let param_u_v = PedersenParams {
            generator: param_h_v.generator.clone(),
            vec_gen: vec![param_g_u.generator.into_affine().clone()],
        };
        let com_T1 = PedersenCommitmentScheme::commit(&param_u_v, &vec![tau1], &t1, "T1")?;
        let com_T2 = PedersenCommitmentScheme::commit(&param_u_v, &vec![tau2], &t2, "T2")?;

        // P->V: E, T1, T2
        transcript.append_serializable_element(b"commitments A,B", &[com_E, com_T1, com_T2])?;

        // append the message digest to the transcript
        let h = digest(&params.message);
        let mut h_msg: &mut [u8] = &mut [0; 32];
        h_msg.write(h.as_bytes()).unwrap();
        transcript.append_message(b"message digest", &h_msg)?;

        // V->P: challenges x
        let x = transcript.get_and_append_challenge(b"challenge x")?;

        // computes zeta = (b_0 + z*1^n + r_0*x) \circ y^n, eta = b_1 + z*1^n + r_1*x
        let b0_z1n_r0x = vec_add(&vec_b0, &vec_add(&vec_z1n, &scalar_product(&vec_r0, &x)));
        let zeta = hadamard_product(&b0_z1n_r0x, &powers_yn);
        let eta = vec_add(&vec_b1, &vec_add(&vec_z1n, &scalar_product(&vec_r1, &x)));

        // computes hat_t = <zeta, eta>
        let hat_t = inner_product(&zeta, &eta);

        // // sanity check
        // let vec_1n = vec![C::ScalarField::one(); params.num_pub_inputs];
        // let delta = inner_product(&vec_1n, &powers_yn) * (z+z*z);
        // let t_prime = delta + t1*x + t2*x*x;
        // if t_prime == hat_t {println!("delta equality passes")}
        // else {println!("delta equality fails")}

        // tau_x = tau1*x + tau2*x^2
        let taux = tau1*x + tau2*x*x;
        // mu = alpha + beta*x
        let mu = alpha + beta*x;
        // fs = \sum_{j=1}^k y^{i_j} s_j + r_s*x
        let mut j = 0;
        let mut sum = C::ScalarField::zero();
        for i in 0..params.num_pub_inputs {
            let term = powers_yn[i]*vec_b[i];
            if term != C::ScalarField::zero() {
                sum += term*vec_sk[j];
                j += 1;
            }
        }
        let fs = sum + rs*x;
        let openings = Openings {
            zeta,
            eta,
            hat_t,
            taux,
            mu,
            fs,
        };
        assert_eq!(j, vec_sk.len());
        ***/
        let openings = Openings {
            zeta: vec![C::ScalarField::one()],
            eta: vec![C::ScalarField::one()],
            hat_t: C::ScalarField::one(),
            taux: C::ScalarField::one(),
            mu: C::ScalarField::one(),
            fs: C::ScalarField::one(),
        };
        // proving ends
        end_timer!(start);
        Ok(RangeProof {
            commitments: vec![com_A, com_B],
            openings,
            challenges: vec![y,z],
            digest: "0".to_string(),
        })
    }

    fn verify(
        params: &Self::PublicParams,
        proof: &Self::Proof
    ) -> Result<bool, SigmaErrors> {
//         // initialization
//         let start = start_timer!(|| "running sigma protocol prove algorithm...");
//         let mut transcript = ProofTranscript::<C::ScalarField>::new(b"RingSignature");
//         transcript.append_serializable_element(b"public list", &params.vec_pk)?;
//
//         // parse commitment parameters
//         let param_g_u = &params.com_parameters[0];
//         let param_h_v = &params.com_parameters[1];
//         let param_key = &params.com_parameters[2];
//
//         // parse proof
//         let commitments = &proof.commitments;
//         let (com_A, com_B, com_E, com_T1, com_T2) = (commitments[0], commitments[1], commitments[2], commitments[3], commitments[4]);
//         let openings = &proof.openings;
//         let challenges = &proof.challenges;
//         let digest = &proof.digest;
//
//         // check the challenges
//         transcript.append_serializable_element(b"commitments A,B", &[com_A, com_B])?;
//         let y = transcript.get_and_append_challenge(b"challenge y")?;
//         let z = transcript.get_and_append_challenge(b"challenge z")?;
//         transcript.append_serializable_element(b"commitments A,B", &[com_E, com_T1, com_T2])?;
//         let h = sha256::digest(&params.message);
//         assert_eq!(&h, digest);
//         let mut h_msg: &mut [u8] = &mut [0; 32];
//         h_msg.write(h.as_bytes()).unwrap();
//         transcript.append_message(b"message digest", &h_msg)?;
//         let x = transcript.get_and_append_challenge(b"challenge x")?;
//
//         if (y,z,x) != (challenges[0],challenges[1],challenges[2])  {
//             return Err(SigmaErrors::InvalidProof(
//                 "invalid challenge value".to_string(),
//             ));
//         }
//
//         // check validity of T1 T2
//         // v^{hat_t} y^taux = v^delta T1^x T2^{x^2}
//         let vec_0n = vec![C::ScalarField::zero(); params.num_pub_inputs];
//         let vec_1n = vec![C::ScalarField::one(); params.num_pub_inputs];
//         let powers_yn = generate_powers(y, params.num_pub_inputs);
//         let delta = inner_product(&vec_1n, &powers_yn) * (z+z*z);
//         let lhs = PedersenCommitmentScheme::commit(param_h_v, &vec_0n, &openings.hat_t, "on hat_t")?
//             + PedersenCommitmentScheme::commit(&param_g_u, &vec_0n, &openings.taux, "on tau_x")?;
//         let rhs = PedersenCommitmentScheme::commit(param_h_v, &vec_0n, &delta, "on delta")?
//             + com_T1.mul(x) + com_T2.mul(x*x);
//         assert_eq!(lhs, rhs, "step 1: T1, T2 checks fail");
//
//         // check validity of A B
//         // g^{zeta \circ y^n} h^eta u^mu = A B^x g^{z1^n} h^{z1^n}
//         let powers_yn_inverse = generate_powers(y.inverse().unwrap(), params.num_pub_inputs);
//         // assert_eq!(hadamard_product(&powers_yn, &powers_yn_inverse), vec![C::ScalarField::one(); params.num_pub_inputs]);
//         let zeta_yn = hadamard_product(&openings.zeta, &powers_yn_inverse);
//         let vec_z1n = vec![z; params.num_pub_inputs];
//         let lhs = PedersenCommitmentScheme::commit(&param_g_u, &zeta_yn, &openings.mu, "on zeta")?
//             + PedersenCommitmentScheme::commit(&param_h_v, &openings.eta, &C::ScalarField::zero(), "on eta")?;
//         let rhs = com_A + com_B.mul(x)
//             + PedersenCommitmentScheme::commit(&param_g_u, &vec_z1n, &C::ScalarField::zero(), "on z1n")?
//             + PedersenCommitmentScheme::commit(&param_h_v, &vec_z1n, &C::ScalarField::zero(), "on z1n")?;
//         assert_eq!(lhs, rhs, "step 2: A,B checks fail");
//
//         // check pk
//         // P^zeta = g^fs E^x P^{z y^n}
//         let vec_z_yn = scalar_product(&powers_yn, &z);
//         let lhs = C::msm(&params.vec_pk, &openings.zeta).unwrap();
//         let rhs = PedersenCommitmentScheme::commit(&param_key, &vec![openings.fs], &C::ScalarField::zero(), "on fs")?
//             + com_E.mul(x) + C::msm(&params.vec_pk, &vec_z_yn).unwrap();
//         assert_eq!(lhs, rhs, "step 3: pk check fails");
//
//         // check inner product hat_t = <zeta, eta>
//         let t = inner_product(&openings.zeta, &openings.eta);
//         assert_eq!(openings.hat_t, t, "step 4: hat_t check fails");
//         let result = true;
//         end_timer!(start);
//         Ok(result)
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_secp256k1::{Fr, Projective};
    use ark_std::UniformRand;

    #[test]
    fn test_rangeproof() {
        // parameter setting
        let mut rng = ark_std::test_rng();
        let val_num:usize = 2;
        let mut wit = (vec![16u128, 32u128], Vec::<Fr>::with_capacity(val_num));
        type RP = RangeProofScheme<Projective>;
        let message = String::from("Welcome to the world of Zero Knowledge!");
        // setup algorithm
        let ring_params = RP::setup(&mut rng, &mut wit, Some(&message), 128).unwrap();
        // prove algorithm
        let proof = RP::prove(&mut rng, &ring_params, &wit).unwrap();
        // // verify algorithm
        // let result = Ring::verify(&ring_params, &proof).unwrap();
        // assert_eq!(result, true);
    }
}