use std::marker::PhantomData;
use std::ops::Neg;
use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_std::{end_timer, rand::Rng, start_timer, UniformRand, Zero, One};

use crate::bulletproofs::ipa::*;
use crate::bulletproofs::structs::*;
use crate::toolbox::commitment::pedersen::PedersenCommitmentScheme;
use crate::rangeproof::structs::{LogarithmicRangeProof, RangeProofParams, Openings};
use crate::toolbox::commitment::PedersenParams;
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
    type Proof = LogarithmicRangeProof<C>;

    fn setup<R: Rng>(
        rng: &mut R,
        wit: &mut Self::Witness, // secret values
        _msg: Option<&String>,
        supported_size: usize, // value size (maximum bits)
    ) -> Result<Self::PublicParams, SigmaErrors> {
        // the number of values to be proved
        let value_num = wit.0.len();
        // parameters for binary commitments of values (b_0, b_1)
        let com_g_parameters= PedersenCommitmentScheme::<C>::setup(rng, value_num*supported_size)?;
        let com_h_parameters= PedersenCommitmentScheme::<C>::setup(rng, value_num*supported_size)?;
        // parameters for Z_p commitments of values
        let com_v_parameters = PedersenCommitmentScheme::<C>::setup(rng, 1)?;
        // the commitment vector of values
        let mut com_value = Vec::with_capacity(value_num);

        for i in 0..value_num {
            // compute the Z_p commitment of each value
            let random = C::ScalarField::rand(rng);
            let value_num_term = PedersenCommitmentScheme::<C>::commit(&com_v_parameters, &vec![C::ScalarField::from(wit.0[i])], &random, "value")?;
            wit.1.push(random);
            com_value.push(value_num_term.into_affine());
        }

        Ok(RangeProofParams {
            num_witness: wit.0.len(),
            supported_size,
            com_parameters: vec![com_g_parameters, com_h_parameters, com_v_parameters],
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
        let val_num = params.num_witness;
        let val_size = params.supported_size;

        // parse commitment parameters
        let com_g_param = &params.com_parameters[0];
        let com_h_param = &params.com_parameters[1];
        let com_v_param = &params.com_parameters[2];
        let u = com_v_param.generator;
        let v = com_v_param.vec_gen[0];

        // parse wit as vector of values and vector of randoms
        let vec_val = wit.0.clone();
        let vec_rand = wit.1.clone();

        // convert values to binary vectors in F^128
        let mut vec_b0 = Vec::<C::ScalarField>::with_capacity(val_num*val_size); // values' num * each value's size
        let mut vec_b1 = Vec::<C::ScalarField>::with_capacity(val_num*val_size);
        for i in 0..val_num {
            let temp:Vec<C::ScalarField> = u128_to_bin(vec_val[i].clone()); // return in little endian
            vec_b0.extend(temp.clone());
            let temp_neg: Vec<C::ScalarField> = temp.iter()
                .map(|&b_i| b_i - C::ScalarField::one())
                .collect();
            vec_b1.extend(temp_neg.clone());
        }

        // sanity check: ensure b_0 b_1 are well-formed
        // b_0 - b_1 = 1^n
        // b_0 \circ b_1 = 0^n
        // <b_0, 2^n> = v
        let powers_2n = generate_powers(C::ScalarField::from(2u64), val_size);
        let constraint_1 = vec_b0.iter()
            .zip(vec_b1.iter())
            .all(|(&b0_i, &b1_i)| b0_i - b1_i == C::ScalarField::one());
        let constraint_2 = vec_b0.iter()
            .zip(vec_b1.iter())
            .all(|(&b0_i, &b1_i)| b0_i * b1_i == C::ScalarField::zero());
        for i in 0..val_num {
            assert_eq!(inner_product(&vec_b0[i*val_size..(i+1)*val_size].to_vec(), &powers_2n), C::ScalarField::from(vec_val[i]));
        }
        assert!(constraint_1 && constraint_2);

        // computes batch commitment A, B for all vec_b0, vec_b1
        let alpha = C::ScalarField::rand(rng);
        let beta = C::ScalarField::rand(rng);
        let vec_r0 = vec![C::ScalarField::rand(rng); val_size*val_num];
        let vec_r1 = vec![C::ScalarField::rand(rng); val_size*val_num];

        let mut vec_g_h = Vec::<C::Affine>::with_capacity(2*val_num*val_size);
        vec_g_h.extend(&com_g_param.vec_gen);
        vec_g_h.extend(&com_h_param.vec_gen);
        let com_g_h_u_params = PedersenParams::<C>{
            generator: u,
            vec_gen: vec_g_h,
        };
        let mut vec_b0_b1 = Vec::<C::ScalarField>::with_capacity(2*val_num*val_size);
        let mut vec_r0_r1 = Vec::<C::ScalarField>::with_capacity(2*val_num*val_size);
        vec_b0_b1.extend(&vec_b0);
        vec_b0_b1.extend(&vec_b1);
        vec_r0_r1.extend(&vec_r0);
        vec_r0_r1.extend(&vec_r1);

        let com_A = PedersenCommitmentScheme::commit(&com_g_h_u_params, &vec_b0_b1, &alpha, "on b0, b1")?;
        let com_B = PedersenCommitmentScheme::commit(&com_g_h_u_params, &vec_r0_r1, &beta, "on r0, r1")?;

        // P->V: A,B
        transcript.append_serializable_element(b"commitments A,B", &[com_A, com_B])?;

        // V->P: challenges y,z
        let y = transcript.get_and_append_challenge(b"challenge y")?;
        let z = transcript.get_and_append_challenge(b"challenge z")?;

        // compute cross terms t1, t2
        let mut t1 = C::ScalarField::zero();
        let mut t2 = C::ScalarField::zero();
        let ym = y.pow(&[val_size as u64]);
        let powers_yn = generate_powers(y, val_size);
        let powers_2n = generate_powers(C::ScalarField::from(2u64), val_size);
        let vec_1n = vec![C::ScalarField::from(1u64); val_size];
        let vec_z1n = vec![z; val_size];
        let vec_neg_z1n = vec![z.neg(); val_size];

        for i in 0..val_num {
            let powers_ymn = scalar_product(&powers_yn, &ym.pow(&[i as u64]));
            // compute t1
            // = <r_0, y^n \circ b_1 + y^n \circ z*1^n + z^2*2^n>
            // + <b_0 - z*1^n, y^n \circ r_1>
            let vec_z2n = scalar_product(&powers_2n, &z.pow(&[(2+i) as u64]));
            let vec_b1_z1n = vec_add(&vec_b1[i*val_size..(i+1)*val_size].to_vec(), &vec_z1n);
            let vec_yn_b1_z1n = hadamard_product(&vec_b1_z1n, &powers_ymn);
            let t1_ip_1 = inner_product(&vec_r0[i*val_size..(i+1)*val_size].to_vec(), &vec_add(&vec_yn_b1_z1n, &vec_z2n));

            let vec_b0_z1n = vec_add(&vec_b0[i*val_size..(i+1)*val_size].to_vec(), &vec_neg_z1n);
            let vec_yn_r1 = hadamard_product(&vec_r1[i*val_size..(i+1)*val_size].to_vec(), &powers_ymn);
            let t1_ip_2 = inner_product(&vec_b0_z1n, &vec_yn_r1);

            let temp_t1 = t1_ip_1 + t1_ip_2;

            // compute t2
            // = <r_0, y^n \circ r_1>
            let temp_t2 = inner_product(&vec_r0[i*val_size..(i+1)*val_size].to_vec(), &vec_yn_r1);

            // add up
            t1 += temp_t1;
            t2 += temp_t2;
        }

        // computes
        // T1 = g^{t1} h^{tau1}
        // T2 = g^{t2} h^{tau2}
        let tau1 = C::ScalarField::rand(rng);
        let tau2 = C::ScalarField::rand(rng);
        let com_T1 = PedersenCommitmentScheme::commit(&com_v_param, &vec![t1], &tau1, "T1")?;
        let com_T2 = PedersenCommitmentScheme::commit(&com_v_param, &vec![t2], &tau2, "T2")?;

        // P->V: E, T1, T2
        transcript.append_serializable_element(b"commitments T1,T2", &[com_T1, com_T2])?;

        // V->P: challenges x
        let x = transcript.get_and_append_challenge(b"challenge x")?;

        // compute opening l, r
        let mut open_l = Vec::<C::ScalarField>::with_capacity(val_num*val_size);
        let mut open_r = Vec::<C::ScalarField>::with_capacity(val_num*val_size);
        for i in 0..val_num {
            // l = b0 - z1^n + r0 x
            // r = y^n \circ (b1 + z1^n + r1 x) + z^2 2^n
            let temp_l = vec_add(&vec_add(&vec_b0[i*val_size..(i+1)*val_size].to_vec(), &vec_neg_z1n), &scalar_product(&vec_r0[i*val_size..(i+1)*val_size].to_vec(), &x));
            let vec_b1_z1n_r1 = vec_add(&vec_add(&vec_b1[i*val_size..(i+1)*val_size].to_vec(), &vec_z1n), &scalar_product(&vec_r1[i*val_size..(i+1)*val_size].to_vec(), &x));
            let vec_z2n = scalar_product(&powers_2n, &z.pow(&[(2+i) as u64]));
            let powers_ymn = scalar_product(&powers_yn, &ym.pow(&[i as u64]));
            let temp_r = vec_add(&hadamard_product(&powers_ymn, &vec_b1_z1n_r1), &vec_z2n);
            open_l.extend(temp_l);
            open_r.extend(temp_r);
        }

        // computes hat_t = <zeta, eta>
        let hat_t = inner_product(&open_l, &open_r);

        // sanity check
        // lhs = (z - z^2) <1^n, y^n> - z^3 <1^n, 2^n> + z^2 v + t_1 x + t_2 x^2
        let mut t0 = C::ScalarField::zero();
        for i in 0..val_num {
            let powers_ymn = scalar_product(&powers_yn, &ym.pow(&[i as u64]));
            t0 += (z - z.pow(&[2u64])) * inner_product(&vec_1n, &powers_ymn)
                - z.pow(&[3+i as u64]) * inner_product(&vec_1n, &powers_2n)
                + z.pow(&[2+i as u64]) * C::ScalarField::from(vec_val[i].clone())
        }
        let lhs = t0 + t1 * x + t2 * x.pow(&[2u64]);
        let rhs = hat_t;
        assert_eq!(lhs, rhs);
        // sanity check ends

        // tau_x = tau1*x + tau2*x^2 + z^2 * rand
        let mut taux = tau1*x + tau2*x*x ;
        for i in 0..val_num {
            taux += z.pow(&[2+i as u64]) * vec_rand[i]
        }

        // mu = alpha + beta*x
        let mu = alpha + beta*x;

        // Bulletproofs Compression
        let inv_ym = y.inverse().unwrap().pow(&[val_size as u64]);
        let powers_inv_yn = generate_powers(y.inverse().unwrap(), val_size);
        let factors_G = vec![C::ScalarField::from(1u64); val_num * val_size];
        let mut factors_H = Vec::<C::ScalarField>::with_capacity(val_num * val_size);
        for i in 0..val_num {
            let powers_inv_ymn = scalar_product(&powers_inv_yn, &inv_ym.pow(&[i as u64]));
            factors_H.extend(powers_inv_ymn.clone());
        }
        let vec_G = com_g_param.vec_gen.clone();
        let vec_H = com_h_param.vec_gen.clone();
        let param = InnerProductParam {
            factors_G,
            factors_H,
            u: v,
            vec_G,
            vec_H,
        };

        let proof = InnerProductProtocol::<C>::prove(&param, open_l.clone(), open_r.clone())?;

        let openings = Openings {
            lx: vec![proof.a],
            rx: vec![proof.b],
            hat_t,
            taux,
            mu,
        };

        // proving ends
        end_timer!(start);
        Ok(LogarithmicRangeProof {
            commitments: vec![com_A, com_B, com_T1, com_T2],
            openings,
            compression_proof: proof,
            challenges: vec![y,z,x],
        })
    }

    fn verify(
        params: &Self::PublicParams,
        proof: &Self::Proof
    ) -> Result<bool, SigmaErrors> {
        // initialization
        let start = start_timer!(|| "running sigma protocol prove algorithm...");
        let mut transcript = ProofTranscript::<C::ScalarField>::new(b"RingSignature");
        transcript.append_serializable_element(b"public list", &params.com_value)?;
        let val_num = params.num_witness;
        let val_size = params.supported_size;

        // parse commitment parameters
        let com_g_param = &params.com_parameters[0];
        let com_h_param = &params.com_parameters[1];
        let com_v_param = &params.com_parameters[2];
        let u = com_v_param.generator;
        let v = com_v_param.vec_gen[0];

        // parse proof
        let commitments = &proof.commitments;
        let (com_A, com_B, com_T1, com_T2) = (commitments[0], commitments[1], commitments[2], commitments[3]);
        let openings = &proof.openings;
        let challenges = &proof.challenges;

        // check the challenges
        transcript.append_serializable_element(b"commitments A,B", &[com_A, com_B])?;
        let y = transcript.get_and_append_challenge(b"challenge y")?;
        let z = transcript.get_and_append_challenge(b"challenge z")?;
        transcript.append_serializable_element(b"commitments T1,T2", &[com_T1, com_T2])?;
        let x = transcript.get_and_append_challenge(b"challenge x")?;

        if (y,z,x) != (challenges[0],challenges[1],challenges[2])  {
            return Err(SigmaErrors::InvalidProof(
                "invalid challenge value".to_string(),
            ));
        }

        // check validity of T1 T2
        // V^{z^2} v^delta T1^x T2^{x^2} u^{-taux} = v^{hat_t}
        let vec_1n = vec![C::ScalarField::one(); val_size];
        let ym = y.pow(&[val_size as u64]);
        let powers_yn = generate_powers(y, val_size);
        let powers_2n = generate_powers(C::ScalarField::from(2u64), val_size);

        let mut delta = C::ScalarField::zero();
        let mut vec_zin = Vec::<C::ScalarField>::with_capacity(val_num);
        for i in 0..val_num {
            let powers_ymn = scalar_product(&powers_yn, &ym.pow(&[i as u64]));
            delta += (z - z.pow(&[2u64])) * inner_product(&vec_1n, &powers_ymn)
                - z.pow(&[3+i as u64]) * inner_product(&vec_1n, &powers_2n);
            vec_zin.push(C::ScalarField::from(z.pow(&[(2+i) as u64])));
        }

        assert_eq!(vec_zin.len(), params.com_value.len());
        let lhs_step1 = C::msm(&params.com_value, &vec_zin).unwrap()
            + PedersenCommitmentScheme::commit(com_v_param, &vec![delta], &openings.taux.neg(), "on delta ands -taux")?
            + com_T1.mul(x)
            + com_T2.mul(x*x);
        // let rhs_step1 = PedersenCommitmentScheme::commit(com_v_param, &vec![openings.hat_t], &C::ScalarField::zero(), "on hat_t")?;
        // assert_eq!(lhs_step1, rhs_step1, "step 1: T1, T2 checks fail");

        // check validity of A B
        // A B^x g^{-z1^n} (h')^{z*y^n + z^2*2^n} u^{-mu} = g^l (h')^r
        let powers_inv_yn = generate_powers(y.inverse().unwrap(), val_size);
        let inv_ym = y.inverse().unwrap().pow(&[val_size as u64]);

        let mut vec_zyn_z2n_yn = Vec::<C::ScalarField>::with_capacity(val_num*val_size);
        // let mut vec_r_yn = Vec::<C::ScalarField>::with_capacity(val_num*val_size);
        for i in 0..val_num {
            let powers_ymn = scalar_product(&powers_yn, &ym.pow(&[i as u64]));
            let powers_inv_ymn = scalar_product(&powers_inv_yn, &inv_ym.pow(&[i as u64]));
            // vec_rx \circ y^{-n}
            // let temp_r_yn = hadamard_product(&powers_inv_ymn, &openings.rx[i]);
            // vec_r_yn.extend(temp_r_yn);
            // z*y^n + z^2*2^n
            let temp_zyn_z2n = vec_add(&scalar_product(&powers_ymn, &z), &scalar_product(&powers_2n, &z.pow(&[(i+2) as u64])));
            // (z*y^n + z^2*2^n) \circ y^{-n}
            let temp_zyn_z2n_yn= hadamard_product(&powers_inv_ymn, &temp_zyn_z2n);
            vec_zyn_z2n_yn.extend(temp_zyn_z2n_yn);
        }

        let mut vec_g_h = Vec::<C::Affine>::with_capacity(2*val_num*val_size);
        vec_g_h.extend(&com_g_param.vec_gen);
        vec_g_h.extend(&com_h_param.vec_gen);
        let com_g_h_u_params = PedersenParams::<C>{
            generator: u,
            vec_gen: vec_g_h,
        };

        let mut vec_xy = vec![z.neg(); val_num*val_size];
        vec_xy.extend(vec_zyn_z2n_yn.clone());

        // let mut vec_lx_rx = Vec::<C::ScalarField>::with_capacity(2*val_num*val_size);
        // vec_lx_rx.extend(flatten_2d_vector(openings.lx.clone()));
        // vec_lx_rx.extend(vec_r_yn.clone());

        let lhs_step2 = com_A + com_B.mul(x)
            + PedersenCommitmentScheme::commit(&com_g_h_u_params, &vec_xy, &C::ScalarField::zero(), "on -z1n, z*yn + z2*2n")?
            + u.mul(&openings.mu.neg());
        // let rhs_step2 = PedersenCommitmentScheme::commit(&com_g_h_u_params, &vec_lx_rx, &C::ScalarField::zero(), "on lx, rx")?;
        // assert_eq!(lhs_step2, rhs_step2, "step 2: A,B checks fail");

        // run Bulletproofs Compression
        // consider aggregating the following two equation into one
        // V^{z^2} v^delta T1^x T2^{x^2} h^{-taux} = v^{hat_t}
        // A B^x g^{-z1^n} (h')^{z*y^n + z^2*2^n} u^{-mu} = g^l (h')^r
        let LHS = lhs_step1 + lhs_step2;
        let vec_G = com_g_param.vec_gen.clone();
        let vec_H = com_h_param.vec_gen.clone();

        let factors_G = vec![C::ScalarField::from(1u64); val_num * val_size];
        let mut factors_H = Vec::<C::ScalarField>::with_capacity(val_num * val_size);
        for i in 0..val_num {
            let powers_inv_ymn = scalar_product(&powers_inv_yn, &inv_ym.pow(&[i as u64]));
            factors_H.extend(powers_inv_ymn.clone());
        }

        let param = InnerProductParam {
            factors_G,
            factors_H,
            u: v,
            vec_G,
            vec_H,
        };

        // call Bulletproofs verifier
        InnerProductProtocol::<C>::verify(val_num*val_size, LHS, &param, &proof.compression_proof)?;

        let result = true;
        end_timer!(start);
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_secp256k1::{Fr, Projective};

    #[test]
    fn test_rangeproof() {
        // parameter setting
        let mut rng = ark_std::test_rng();
        let val_num: usize = 4;
        let vec_val = vec![114u128, 514u128, 1919u128, 810u128];
        let vec_rand = Vec::<Fr>::with_capacity(val_num);
        let mut wit = (vec_val, vec_rand);
        type RP = RangeProofScheme<Projective>;
        let message = String::from("Welcome to the world of Zero Knowledge!");
        // setup algorithm
        let rp_params = RP::setup(&mut rng, &mut wit, Some(&message), 128).unwrap();
        // prove algorithm
        let proof = RP::prove(&mut rng, &rp_params, &wit).unwrap();
        // verify algorithm
        let result = RP::verify(&rp_params, &proof).unwrap();
        assert_eq!(result, true);
    }
}