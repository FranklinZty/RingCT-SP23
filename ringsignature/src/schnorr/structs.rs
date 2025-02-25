use ark_ec::CurveGroup;
use crate::commitment::PedersenParams;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SchnorrProof<C: CurveGroup> {
    // the intermediate commitment vector generated along the proving
    pub commitments: Vec<C>,
    // the opening vector generated along the proving
    pub opening: Vec<C::ScalarField>,
    // the challenge vector generated by merlin transcript
    pub challenge: Vec<C::ScalarField>,
    // the digest of the message
    pub digest: String,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SchnorrParams<C: CurveGroup> {
    // the witness commitments in the statement
    pub com_witness: Vec<C>,
    // the number of witness elements
    pub num_witness: usize,
    // the number of public inputs (commitments)
    pub num_pub_inputs: usize,
    // the generators for commitment commitments
    pub com_parameters: PedersenParams<C>,
    // the signed message
    pub message: String,
}
