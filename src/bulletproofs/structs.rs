use ark_ec::CurveGroup;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct InnerProductParam<C: CurveGroup> {
    pub factors_G: Vec<C::ScalarField>,
    pub factors_H: Vec<C::ScalarField>,
    pub u: C::Affine,
    pub vec_G: Vec<C::Affine>,
    pub vec_H: Vec<C::Affine>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct InnerProductProof<C: CurveGroup> {
    pub vec_L: Vec<C::Affine>,
    pub vec_R: Vec<C::Affine>,
    pub a: C::ScalarField,
    pub b: C::ScalarField,
    pub challenges: Vec<C::ScalarField>,
}
