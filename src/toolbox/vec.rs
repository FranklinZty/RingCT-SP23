use ark_ff::PrimeField;
use ark_ec::CurveGroup;
use rand::{seq::SliceRandom, thread_rng};
use std::iter;

pub fn vec_u64_to_F<F: PrimeField>(m: &[u64]) -> Vec<F> {
    let mut vec_field: Vec<F> = Vec::new();
    for i in m.iter() {
        vec_field.push(F::from(*i));
    }
    vec_field
}

pub fn flatten_2d_vector<T: Clone>(matrix: Vec<Vec<T>>) -> Vec<T> {
    matrix.into_iter().flat_map(|row| row.into_iter()).collect()
}

/// convert u128 value to a binary vector Vec<F> in little endian
pub fn u128_to_bin<F: PrimeField>(n: u128) -> Vec<F> {
    // convert u128 to binary string
    let binary_str = format!("{:b}", n);

    let length = binary_str.len();

    // pad the length to powers of two
    let mut padded_binary_str = String::new();
    for _ in 0..(128 - length) {
        padded_binary_str.push('0');
    }
    padded_binary_str.push_str(&binary_str);

    // convert binary str to vector of F
    padded_binary_str.chars().map(|c| F::from(c.to_digit(2).unwrap() as u128)).rev().collect()
}

pub fn shuffle<C: CurveGroup>(vec_pk: & mut Vec<C::Affine>, pk: C::Affine) -> Vec<C::ScalarField>{
    let mut rng = thread_rng();
    vec_pk.shuffle(&mut rng);
    let mut vec_b:Vec<C::ScalarField> = Vec::new();
    for i in 0..vec_pk.len() {
        if pk == vec_pk[i] {
            vec_b.push(C::ScalarField::from(1u64));
        } else {
            vec_b.push(C::ScalarField::from(0u64));
        }
    }
    vec_b
}

pub fn scalar_product<F: PrimeField>(vec_a: &Vec<F>, c: &F) -> Vec<F> {
    vec_a.iter()
        .map(|&a| a * c).collect()
}

pub fn inner_product<F: PrimeField>(vec_a: &Vec<F>, vec_b: &Vec<F>) -> F {
    assert_eq!(vec_a.len(), vec_b.len(), "Vectors must be of the same length");

    vec_a.iter()
        .zip(vec_b.iter())
        .map(|(&a, &b)| a * b)
        .fold(F::zero(), |acc, x| acc + x)
}

pub fn vec_add<F: PrimeField>(vec_a: &Vec<F>, vec_b: &Vec<F>) -> Vec<F> {
    assert_eq!(vec_a.len(), vec_b.len(), "Vectors must be of the same length");
    let result = vec_a.iter()
        .zip(vec_b.iter())
        .map(|(&a, &b)| a + b).collect();
    result
}

pub fn vec_split<T: Clone>(vec: &Vec<T>, n: usize) -> (Vec<T>, Vec<T>) {
    assert!(vec.len() >= n, "Vectors must have length than n");
    let (slice_l, slice_r) = vec.split_at(n);
    (slice_l.to_vec(), slice_r.to_vec())
}

pub fn hadamard_product<F: PrimeField>(vec_a: &Vec<F>, vec_b: &Vec<F>) -> Vec<F> {
    assert_eq!(vec_a.len(), vec_b.len(), "Vectors must be of the same length");
    let result = vec_a.iter()
        .zip(vec_b.iter())
        .map(|(&a, &b)| a * b).collect();
    result
}

pub fn generate_powers<F: PrimeField>(y: F, n: usize) -> Vec<F> {
    iter::successors(Some(F::one()), |&current_power| Some(current_power * y))
        .take(n)
        .collect()
}

#[cfg(test)]
mod tests {
    use ark_ec::{CurveGroup};
    use super::*;
    use ark_secp256k1::{Fr, Projective, Affine};
    use ark_std::{UniformRand};

    #[test]
    fn test_vec_u64_to_F() {
        let msg: [u64; 4] = [1, 2, 3, 4];
        let msg_field: Vec<Fr> = vec_u64_to_F(&msg);
        assert_eq!(msg_field, vec![Fr::from(1u64), Fr::from(2u64), Fr::from(3u64), Fr::from(4u64)]);
    }

    #[test]
    fn test_flatten_2d_vector() {
        let matrix = vec![
        vec![1, 2, 3],
        vec![4, 5, 6],
        vec![7, 8, 9],
    ];
        let flattened = flatten_2d_vector(matrix);
        println!("{:?}", flattened);
    }

    #[test]
    fn test_u128_to_bin() {
        let m:u128 = 64 + 32;
        let vec_bin:Vec<Fr> = u128_to_bin(m);
        println!("{:?}", vec_bin);
    }

    #[test]
    fn test_shuffle() {
        let mut rng = ark_std::test_rng();
        let scalar = Fr::from(1u64);
        let g = Projective::rand(&mut rng);
        let pk = g*scalar;
        let mut vec_pk = vec![Affine::rand(&mut rng); 3usize];
        let vec_b = shuffle::<Projective>(&mut vec_pk, pk.into_affine());
        for i in 0..vec_b.len() {
            if vec_b[i] == Fr::from(1u64) {
                assert_eq!(pk, vec_pk[i]);
            }
        }
    }

    #[test]
    fn test_inner_product() {
        let a: [u64; 4] = [1, 2, 3, 4];
        let vec_a: Vec<Fr> = vec_u64_to_F(&a);
        let b: [u64; 4] = [4, 3, 2, 1];
        let vec_b: Vec<Fr> = vec_u64_to_F(&b);

        let result = inner_product(&vec_a, &vec_b);
        assert_eq!(result, Fr::from(20u64));
    }

    #[test]
    fn test_generate_powers() {
        let y = Fr::from(2u64);
        let n = 4;
        let result = generate_powers(y, n);
        assert_eq!(result, vec![Fr::from(1u64), Fr::from(2u64), Fr::from(4u64), Fr::from(8u64)]);
    }
}
