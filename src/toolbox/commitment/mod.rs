pub mod pedersen;
use ark_ec::CurveGroup;
use std::fmt::Debug;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PedersenParams<C: CurveGroup> {
    pub generator: C,
    pub vec_gen: Vec<C::Affine>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PedersenOpening<C: CurveGroup> {
    pub message: Vec<C::ScalarField>,
    pub random: C::ScalarField,
}
