use std::marker::PhantomData;

use ark_crypto_primitives::{
    merkle_tree::Config,
    sponge::{Absorb, CryptographicSponge},
};
use ark_ff::{FftField, PrimeField};

use crate::{ldt::LowDegreeTest, parameters::Parameters};

pub mod common;
pub mod parameters;
pub mod prover;
pub mod verifier;

#[derive(Default)]
pub struct Rstir<F, MerkleConfig, FSConfig> {
    _field: PhantomData<F>,
    _merkle_config: PhantomData<MerkleConfig>,
    _fs_config: PhantomData<FSConfig>,
}

impl<F, MerkleConfig, FSConfig> Rstir<F, MerkleConfig, FSConfig> {
    pub const fn const_default() -> Self {
        Self {
            _field: PhantomData,
            _merkle_config: PhantomData,
            _fs_config: PhantomData,
        }
    }
}

// impl<F, MerkleConfig, FSConfig> LowDegreeTest<F, MerkleConfig, FSConfig>
//     for Rstir<F, MerkleConfig, FSConfig>
// where
//     F: FftField + PrimeField + Absorb,
//     MerkleConfig: Config<Leaf = Vec<F>>,
//     MerkleConfig::InnerDigest: Absorb,
//     FSConfig: CryptographicSponge,
//     FSConfig::Config: Clone,
// {
//     type Prover = prover::RstirProver<F, MerkleConfig, FSConfig>;
//     type Verifier = verifier::RstirVerifier<F, MerkleConfig, FSConfig>;

//     fn display(parameters: Parameters<F, MerkleConfig, FSConfig>) {
//         println!("{}", parameters::FullParameters::from(parameters));
//     }
// }
