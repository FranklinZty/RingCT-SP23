#![allow(non_snake_case)]
#![allow(dead_code)]

use std::marker::PhantomData;
use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_std::{end_timer, start_timer};
use crate::toolbox::sigma::transcript::ProofTranscript;
use crate::toolbox::errors::SigmaErrors;
use crate::toolbox::vec::{vec_add, vec_split, inner_product, scalar_product, hadamard_product};
use crate::bulletproofs::structs::*;

#[derive(Clone, Debug)]
pub struct InnerProductProtocol<C: CurveGroup> {
    phantom: PhantomData<C>,
}
// IPA relation:
// vec_G^vec_a * vec_H^vec_b * u^<vec_a, vec_b>
// = A * B * u^c
impl<C: CurveGroup> InnerProductProtocol<C>
{
    pub fn prove(
        params: &InnerProductParam<C>,
        mut vec_a: Vec<C::ScalarField>,
        mut vec_b: Vec<C::ScalarField>,
    ) -> Result<InnerProductProof<C>, SigmaErrors> {
        // initialization
        let start = start_timer!(|| "running inner product argument prove algorithm...");
        let mut transcript = ProofTranscript::<C::ScalarField>::new(b"RingSignature");

        let mut n = params.vec_G.len();
        let mut vec_G = params.vec_G.clone();
        let mut vec_H = params.vec_H.clone();

        // Ensure all vectors have the same length
        if params.vec_H.len() != n || vec_a.len() != n || vec_b.len() !=n
            || params.factors_G.len() != n || params.factors_H.len() != n
        {
            return Err(SigmaErrors::InvalidParameters(
                "vectors length are different".to_string(),
            ));
        }

        if !n.is_power_of_two()
        {
            return Err(SigmaErrors::InvalidParameters(
                "vector length is not power of two".to_string(),
            ));
        }

        transcript.append_field_element(b"IPAsize", &C::ScalarField::from(n as u128))?;

        // log(n) is the trailing zeros of its binary form
        // e.g., 32 = 100000 -> log(32) = 5
        let log_n = n.trailing_zeros() as usize;
        let mut vec_L = Vec::with_capacity(log_n);
        let mut vec_R = Vec::with_capacity(log_n);
        let mut challenges = Vec::with_capacity(log_n);

        // compression
        // base step
        if n != 1 {
            n = n / 2;

            // split n-length vector to two sub-vectors
            let (a_L, a_R) = vec_split(&vec_a, n);
            let (b_L, b_R) = vec_split(&vec_b, n);
            let (G_L, G_R) = vec_split(&vec_G, n);
            let (H_L, H_R) = vec_split(&vec_H, n);

            // <a_L*x + a_R*x_inv, b_L*x_inv + b_R*x> = <a, b> + x^2*<a_L, b_R> + x_inv^2*<a_R, b_L>
            // compute c_L = <a_L, b_R>, c_R = <a_R, b_L>
            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            // compute L = (G_R^factors_G[n..2n])^a_L + (H_L^factors_H[0..n])^b_R
            let mut exp = vec![];
            let temp_a: Vec<C::ScalarField> = hadamard_product(&a_L, &params.factors_G[n..2*n].to_vec());
            let temp_b: Vec<C::ScalarField> = hadamard_product(&b_R, &params.factors_H[0..n].to_vec());
            exp.extend(temp_a);
            exp.extend(temp_b);
            exp.push(c_L);

            let mut base = G_R.to_vec();
            base.extend(H_L.to_vec());
            base.push(params.u);

            let com_L = C::msm(&base, &exp).unwrap().into_affine();

            // compute R = (G_L^factors_G[0..n])^a_R + (H_R^factors_H[n..2n])^b_L
            let mut exp = vec![];
            let temp_a: Vec<C::ScalarField> = hadamard_product(&a_R, &params.factors_G[0..n].to_vec());
            let temp_b: Vec<C::ScalarField> = hadamard_product(&b_L, &params.factors_H[n..2*n].to_vec());
            exp.extend(temp_a);
            exp.extend(temp_b);
            exp.push(c_R);

            let mut base = G_L.to_vec();
            base.extend(H_R.to_vec());
            base.push(params.u);

            let com_R = C::msm(&base, &exp).unwrap().into_affine();

            vec_L.push(com_L);
            vec_R.push(com_R);

            // get challenge
            transcript.append_serializable_element(b"commitments L, R", &[com_L, com_R])?;
            let x = transcript.get_and_append_challenge(b"challenge")?;
            let x_inv = x.inverse().unwrap();
            challenges.push(x);

            // // sanity check: L,R are correct
            // // L^{x^2}*(A*B)*R^{x_inv^2}*u^{<a,b>} = fold_G^fold_a * fold_H^fold_b * u^{<fold_a,fold_b>}
            // let LHS = com_L*(x*x)
            //     + C::msm(&vec_G, &hadamard_product(&vec_a, &factors_G)).unwrap()
            //     + C::msm(&vec_H, &hadamard_product(&vec_b, &factors_H)).unwrap()
            //     + com_R*(x_inv*x_inv)
            //     + u*(inner_product(&vec_a, &vec_b));

            // fold vec_G, vec_H, vec_a, vec_b
            vec_a = vec_add(&scalar_product(&a_L, &x), &scalar_product(&a_R, &x_inv)).clone();
            vec_b = vec_add(&scalar_product(&b_L, &x_inv), &scalar_product(&b_R, &x)).clone();
            vec_G = vec![];
            vec_H = vec![];
            for i in 0..n {
                let term_G = C::msm(&[G_L[i], G_R[i]], &[x_inv*params.factors_G[i], x*params.factors_G[n+i]]).unwrap();
                let term_H = C::msm(&[H_L[i], H_R[i]], &[x*params.factors_H[i], x_inv*params.factors_H[n+i]]).unwrap();
                vec_G.push(term_G.into_affine());
                vec_H.push(term_H.into_affine());
            }

            // // sanity check: L, R are correct
            // // L^{x^2}*(A*B)*R^{x_inv^2}*u^{<a,b>} = fold_G^fold_a * fold_H^fold_b * u^{<fold_a,fold_b>}
            // let RHS = C::msm(&vec_G, &vec_a).unwrap() + C::msm(&vec_H, &vec_b).unwrap() + u*(inner_product(&vec_a, &vec_b));
            // assert_eq!(LHS, RHS);
        }

        // loop step
        while n !=1 {
            n = n / 2;
            let (a_L, a_R) = vec_split(&vec_a, n);
            let (b_L, b_R) = vec_split(&vec_b, n);
            let (G_L, G_R) = vec_split(&vec_G, n);
            let (H_L, H_R) = vec_split(&vec_H, n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            let mut exp = a_L.clone();
            exp.extend(b_R.clone());
            exp.push(c_L);

            let mut base = G_R.to_vec();
            base.extend(H_L.to_vec());
            base.push(params.u);

            let com_L = C::msm(&base, &exp).unwrap().into_affine();

            let mut exp = vec![];
            exp.extend(a_R.clone());
            exp.extend(b_L.clone());
            exp.push(c_R);

            let mut base = G_L.to_vec();
            base.extend(H_R.to_vec());
            base.push(params.u);

            let com_R = C::msm(&base, &exp).unwrap().into_affine();

            vec_L.push(com_L);
            vec_R.push(com_R);

            transcript.append_serializable_element(b"commitments L, R", &[com_L, com_R])?;
            let x = transcript.get_and_append_challenge(b"challenge")?;
            let x_inv = x.inverse().unwrap();
            challenges.push(x);
            // // sanity check: L, R are correct
            // // L^{x^2}*(A*B)*R^{x_inv^2}*u^{<a,b>} = fold_G^fold_a * fold_H^fold_b * u^{<fold_a,fold_b>}
            // let LHS = com_L*(x*x)
            //     + C::msm(&vec_G, &vec_a).unwrap()
            //     + C::msm(&vec_H, &vec_b).unwrap()
            //     + com_R*(x_inv*x_inv)
            //     + u*(inner_product(&vec_a, &vec_b));

            vec_a = vec_add(&scalar_product(&a_L, &x), &scalar_product(&a_R, &x_inv)).clone();
            vec_b = vec_add(&scalar_product(&b_L, &x_inv), &scalar_product(&b_R, &x)).clone();
            vec_G = vec![];
            vec_H = vec![];
            for i in 0..n {
                let term_G = C::msm(&[G_L[i], G_R[i]], &[x_inv, x]).unwrap();
                let term_H = C::msm(&[H_L[i], H_R[i]], &[x, x_inv]).unwrap();
                vec_G.push(term_G.into_affine());
                vec_H.push(term_H.into_affine());
            }
            // // sanity check: L, R are correct
            // // L^{x^2}*(A*B)*R^{x_inv^2}*u^{<a,b>} = fold_G^fold_a * fold_H^fold_b * u^{<fold_a,fold_b>}
            // let RHS = C::msm(&vec_G, &vec_a).unwrap() + C::msm(&vec_H, &vec_b).unwrap() + u*(inner_product(&vec_a, &vec_b));
            // assert_eq!(LHS, RHS);
        }

        end_timer!(start);
        Ok(InnerProductProof {
            vec_L,
            vec_R,
            a: vec_a[0],
            b: vec_b[0],
            challenges,
        })
    }

    pub fn verify(
        n: usize,
        target_P: C,
        params: &InnerProductParam<C>,
        proof: &InnerProductProof<C>,
    ) -> Result<(), SigmaErrors> {
        let start = start_timer!(|| "running inner product argument verify algorithm...");
        let mut transcript = ProofTranscript::<C::ScalarField>::new(b"RingSignature");

        assert_eq!(params.vec_G.len(), n);
        let log_n = proof.vec_L.len();
        let vec_G = params.vec_G.clone();
        let vec_H = params.vec_H.clone();

        // prevents overflow
        if log_n >= 32 {
            return Err(
                SigmaErrors::InvalidParameters("vector size is too large".to_string())
            );
        }
        if n != (1 << log_n) {
            return Err(
                SigmaErrors::InvalidProof("incorrect proof length".to_string())
            );
        }

        transcript.append_field_element(b"IPAsize", &C::ScalarField::from(n as u128))?;

        // check challenges x at each round
        let mut challenges = Vec::with_capacity(log_n);
        let mut challenges_sq:Vec<C::ScalarField> = Vec::with_capacity(log_n);
        let mut challenges_inv_sq:Vec<C::ScalarField> = Vec::with_capacity(log_n);
        let mut all_inv = C::ScalarField::from(1u64);
        for i in 0..log_n {
            transcript.append_serializable_element(b"commitments L, R", &[proof.vec_L[i], proof.vec_R[i]])?;
            let x = transcript.get_and_append_challenge(b"challenge")?;
            challenges.push(x);
            let x_inv = x.inverse().unwrap();
            challenges_sq.push(x*x);
            challenges_inv_sq.push(x_inv*x_inv);
            all_inv *= x_inv;
            if x != proof.challenges[i] {
                return Err(SigmaErrors::InvalidProof("invalid challenge value".to_string()));
            }
        }

        // speed up the verification
        // instead of computing msm at each round
        // the verifier can record their scalars in log(n) boxes
        // and execute the msm at the final round
        // details can be referred to https://doc-internal.dalek.rs/bulletproofs/inner_product_proof/index.html
        let mut vec_box = Vec::with_capacity(log_n);
        vec_box.push(all_inv);
        for i in 1..n {
            let log_i = (32 - 1 - (i as u32).leading_zeros()) as usize; // e.g., 64u32 has 26 leading zeros
            let k = 1 << log_i; // = 2^{lg_i}
            let x_log_i_sq = challenges_sq[log_n-1-log_i];
            vec_box.push(vec_box[i-k] * x_log_i_sq);
        }
        let mut vec_box_reverse = vec_box.clone();
        vec_box_reverse.reverse();

        // // sanity check: make sure the final vectors G, H
        // // computed from the original G, H directly are correct
        // let mut expected_vec_G = Vec::with_capacity(n);
        // let mut expected_vec_H = Vec::with_capacity(n);
        // for i in 0..vec_G.len(){
        //     expected_vec_G.push(C::msm(&[vec_G[i]], &[factors_G[i]]).unwrap().into_affine());
        //     expected_vec_H.push(C::msm(&[vec_H[i]], &[factors_H[i]]).unwrap().into_affine());
        // }
        //
        // let mut m = n.clone();
        // for j in 0..proof.vec_L.len() {
        //     m = m / 2;
        //     let (G_L, G_R) = vec_split(&expected_vec_G, m);
        //     let (H_L, H_R) = vec_split(&expected_vec_H, m);
        //     expected_vec_G = vec![];
        //     expected_vec_H = vec![];
        //     for i in 0..m {
        //         let term_G = C::msm(&[G_L[i], G_R[i]], &[challenges[j].inverse().unwrap(), challenges[j]]).unwrap();
        //         let term_H = C::msm(&[H_L[i], H_R[i]], &[challenges[j], challenges[j].inverse().unwrap()]).unwrap();
        //         expected_vec_G.push(term_G.into_affine());
        //         expected_vec_H.push(term_H.into_affine());
        //     }
        // }
        // assert_eq!(expected_vec_G[0], C::msm(&vec_G, &hadamard_product(&vec_box, &factors_G)).unwrap().into_affine());
        // assert_eq!(expected_vec_H[0], C::msm(&vec_H, &hadamard_product(&vec_box_reverse, &factors_H)).unwrap().into_affine());

        // compute factors_g*vec_box*a and factors_h*vec_box_reverse*b
        let g_a_box = scalar_product(&hadamard_product(&vec_box, &params.factors_G), &proof.a);
        let h_b_box = scalar_product(&hadamard_product(&vec_box_reverse, &params.factors_H), &proof.b);

        // compute P =
        // u^{ab} *
        // vec_g^{factors_G * a * vec_box} *
        // vec_h^{factors_H * b * vec_box_reverse} *
        // (L_0*...*L_{log_n-1})^{x^2} *
        // (R_0*...*R_{log_n-1}})^{x^-2}
        let neg_challenges_sq = challenges_sq.iter().map(|&xi| -xi).collect::<Vec<C::ScalarField>>();
        let neg_challenges_inv_sq = challenges_inv_sq.iter().map(|&xi| -xi).collect::<Vec<C::ScalarField>>();

        let mut exp = vec![proof.a*proof.b];
        exp.extend(g_a_box);
        exp.extend(h_b_box);
        exp.extend(neg_challenges_sq);
        exp.extend(neg_challenges_inv_sq);

        let mut base = vec![params.u];
        base.extend(vec_G);
        base.extend(vec_H);
        base.extend(proof.vec_L.clone());
        base.extend(proof.vec_R.clone());

        let expected_P = C::msm(&base, &exp).unwrap();

        end_timer!(start);
        if expected_P == target_P {
            Ok(())
        }
        else {
            Err(SigmaErrors::InvalidProof("invalid IPA proof".to_string()))
        }
    }
}

#[cfg(test)]
mod tests {
    use ark_ec::VariableBaseMSM;
    use super::*;
    use ark_secp256k1::{Fr, Projective, Affine};
    use ark_std::UniformRand;
    use crate::toolbox::vec::vec_u64_to_F;

    #[test]
    fn test_ipa() {
        let mut rng = ark_std::test_rng();
        let n = 4;
        let vec_a: Vec<Fr> = vec_u64_to_F(&[1u64, 2u64, 3u64, 4u64]);
        let vec_b: Vec<Fr> = vec_u64_to_F(&[1u64, 1u64, 1u64, 1u64]);
        let vec_G = vec![Affine::rand(&mut rng); vec_a.len()];
        let vec_H = vec![Affine::rand(&mut rng); vec_a.len()];
        let u = Affine::rand(&mut rng);
        let fac_G: Vec<Fr> = vec_u64_to_F(&[1u64, 2u64, 3u64, 4u64]);
        let fac_H: Vec<Fr> = vec_u64_to_F(&[1u64, 1u64, 1u64, 1u64]);

        type IPA = InnerProductProtocol<Projective>;
        let params = InnerProductParam {
            factors_G: fac_G.clone(),
            factors_H: fac_H.clone(),
            u,
            vec_G: vec_G.clone(),
            vec_H: vec_H.clone()
        };

        let proof = IPA::prove(&params, vec_a.clone(), vec_b.clone()).unwrap();
        // compute P with uncompressed vectors vec_a, vec_b
        let t = inner_product(&vec_a, &vec_b);
        let mut exp = vec![];
        exp.extend(hadamard_product(&vec_a, &fac_G));
        exp.extend(hadamard_product(&vec_b, &fac_H));
        let mut base = vec![];
        base.extend(vec_G.clone());
        base.extend(vec_H.clone());

        let P = Projective::msm(&base, &exp).unwrap() + u*t;
        IPA::verify(n, P, &params, &proof).unwrap();
    }
}

