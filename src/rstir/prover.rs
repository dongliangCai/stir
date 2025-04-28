use ark_crypto_primitives::{
    merkle_tree::{Config, MerkleTree},
    sponge::{Absorb, CryptographicSponge},
};
use ark_ff::{FftField, Field, PrimeField};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Polynomial};
use ark_std::log2;
use derivative::Derivative;

use crate::{domain::Domain, ldt::Prover, parameters::Parameters, poly_utils, utils};

use super::{
    common::{Commitment, Proof, RoundProof},
    parameters::FullParameters,
};

#[derive(Derivative)]
#[derivative(Clone(bound = "F: Clone"))]
pub struct Witness<F: FftField, MerkleConfig: Config> {
    pub(crate) domain: Vec<F>,
    pub(crate) polynomial: DensePolynomial<F>,
    pub(crate) merkle_tree: MerkleTree<MerkleConfig>,
    pub(crate) folded_evals: Vec<Vec<F>>,
}

#[derive(Derivative)]
#[derivative(Debug)]
pub struct WitnessExtended<F: FftField, MerkleConfig: Config> {
    #[derivative(Debug = "ignore")]
    pub(crate) domain: Vec<F>,
    pub(crate) polynomial: DensePolynomial<F>,

    #[derivative(Debug = "ignore")]
    pub(crate) merkle_tree: MerkleTree<MerkleConfig>,
    #[derivative(Debug = "ignore")]
    pub(crate) folded_evals: Vec<Vec<F>>,
    pub(crate) num_round: usize,
}

pub struct RstirProver<F, MerkleConfig, FSConfig>
where
    F: FftField,
    MerkleConfig: Config,
    FSConfig: CryptographicSponge,
    FSConfig::Config: Clone,
{
    pub(crate) parameters: FullParameters<F, MerkleConfig, FSConfig>,
}

impl<F, MerkleConfig, FSConfig> Prover<F, MerkleConfig, FSConfig>
    for RstirProver<F, MerkleConfig, FSConfig>
where
    F: FftField + PrimeField + Absorb,
    MerkleConfig: Config<Leaf = Vec<F>>,
    MerkleConfig::InnerDigest: Absorb,
    FSConfig: CryptographicSponge,
    FSConfig::Config: Clone,
{
    type FullParameter = FullParameters<F, MerkleConfig, FSConfig>;
    type Commitment = Commitment<MerkleConfig>;
    type Witness = Witness<F, MerkleConfig>;
    type Proof = Proof<F, MerkleConfig>;

    fn new(parameters: Parameters<F, MerkleConfig, FSConfig>) -> Self {
        Self::new_full(parameters.into())
    }

    fn new_full(full_parameters: Self::FullParameter) -> Self {
        Self {
            parameters: full_parameters,
        }
    }

    // TODO: Rename witness_polynomial
    fn commit(
        &self,
        witness_polynomial: DensePolynomial<F>,
    ) -> (Commitment<MerkleConfig>, Witness<F, MerkleConfig>) {
        //TODO: random select domain L^(0)?
        let domain = Domain::<F>::new(
            self.parameters.starting_degree,
            self.parameters.starting_rate,
        )
        .unwrap();

        let n = domain.size();
        let w = domain.root_of_unity;

        //1, w, w^2,..., w^(n-1)
        let vec_domain: Vec<F> = std::iter::successors(Some(F::ONE), |&prev| Some(prev * w))
            .take(n)
            .collect();

        //evals:h^(0)   witness_polynomial:\hat{h}^(0)
        let evals = witness_polynomial
            .evaluate_over_domain_by_ref(domain.backing_domain)
            .evals;

        //h^(0) is not folded
        let folded_evals = utils::stack_evaluations(evals, 1);

        //oracle of h^(0): L^(0) -> Fq
        let merkle_tree = MerkleTree::<MerkleConfig>::new(
            &self.parameters.leaf_hash_params,
            &self.parameters.two_to_one_params,
            &folded_evals,
        )
        .unwrap();

        let initial_commitment = merkle_tree.root();

        (
            Commitment {
                root: initial_commitment,
            },
            Witness {
                domain: vec_domain,
                polynomial: witness_polynomial,
                merkle_tree,
                folded_evals,
            },
        )
    }

    fn prove(&self, witness: Witness<F, MerkleConfig>) -> Proof<F, MerkleConfig> {
        assert!(witness.polynomial.degree() < self.parameters.starting_degree);

        let mut sponge = FSConfig::new(&self.parameters.fiat_shamir_config);
        //Add parameters to FS
        sponge.absorb(&witness.merkle_tree.root());

        let mut witness = WitnessExtended {
            domain: witness.domain,
            polynomial: witness.polynomial,
            merkle_tree: witness.merkle_tree,
            folded_evals: witness.folded_evals,
            num_round: 0,
        };

        let mut round_proofs = vec![];
        let domain_size = self.parameters.starting_degree * (1 << self.parameters.starting_rate);
        let mut ni = domain_size / self.parameters.folding_factor;

        let kth_rou = F::get_root_of_unity(self.parameters.folding_factor as u64).unwrap();

        //1, w_k^1, ... w_k^(k-1)
        let rou_powers = std::iter::successors(Some(F::ONE), |&prev| Some(prev * kth_rou))
            .take(self.parameters.folding_factor)
            .collect();

        for _ in 0..self.parameters.num_rounds {
            let (new_witness, round_proof) = self.round(ni, &rou_powers, &mut sponge, &witness);
            witness = new_witness;
            ni = ni / 2;
            round_proofs.push(round_proof);
        }

        let final_polynomial = witness.polynomial;

        let final_repetitions = self.parameters.repetitions[self.parameters.num_rounds];
        let scaling_factor = witness.domain.len();
        let final_randomness_indexes = utils::dedup(
            (0..final_repetitions).map(|_| utils::squeeze_integer(&mut sponge, scaling_factor)),
        );

        let queries_to_final_ans: Vec<_> = final_randomness_indexes
            .iter()
            .map(|index| witness.folded_evals[*index].clone())
            .collect();

        let queries_to_final_proof = witness
            .merkle_tree
            .generate_multi_proof(final_randomness_indexes)
            .unwrap();

        let queries_to_final = (queries_to_final_ans, queries_to_final_proof);

        let pow_nonce = utils::proof_of_work(
            &mut sponge,
            self.parameters.pow_bits[self.parameters.num_rounds],
        );

        Proof {
            round_proofs,
            final_polynomial,
            queries_to_final,
            pow_nonce,
        }
    }
}

impl<F, MerkleConfig, FSConfig> RstirProver<F, MerkleConfig, FSConfig>
where
    F: FftField + PrimeField + Absorb,
    MerkleConfig: Config<Leaf = Vec<F>>,
    MerkleConfig::InnerDigest: Absorb,
    FSConfig: CryptographicSponge,
    FSConfig::Config: Clone,
{
    pub fn new(parameters: Parameters<F, MerkleConfig, FSConfig>) -> Self {
        Self {
            parameters: parameters.into(),
        }
    }

    // TODO: Rename to better name
    fn round(
        &self,
        ni: usize,
        rou_powers: &Vec<F>,
        sponge: &mut impl CryptographicSponge,
        witness: &WitnessExtended<F, MerkleConfig>,
    ) -> (
        WitnessExtended<F, MerkleConfig>,
        RoundProof<F, MerkleConfig>,
    ) {
        let k = rou_powers.len();

        //beta_1,...,beta_ni
        let beta_ni: Vec<F> = sponge.squeeze_field_elements(ni);

        //get random domain as f_domain(L_i)
        let mut random_domain = Vec::with_capacity(ni * k);

        //folded random domain as L^(i+1) = (L_i)^k
        let mut fold_random_domain = Vec::with_capacity(ni);

        for beta_j in beta_ni {
            for rou_power in rou_powers {
                random_domain.push(beta_j * rou_power);
            }
            fold_random_domain.push(beta_j.pow([k as u64]));
        }

        //\hat{h}_{i}
        let h_poly = witness.polynomial.clone();

        //TODO:just use Horner's method now
        // f^(i) is the eval of \hat{h}_{i} over random domain L_i
        let f_evaluations = random_domain
            .iter()
            .map(|alpha| h_poly.evaluate(alpha))
            .collect();

        let f_folded_evaluations =
            utils::stack_evaluations(f_evaluations, self.parameters.folding_factor);
        let f_merkle = MerkleTree::<MerkleConfig>::new(
            &self.parameters.leaf_hash_params,
            &self.parameters.two_to_one_params,
            &f_folded_evaluations,
        )
        .unwrap();
        let f_root = f_merkle.root();
        sponge.absorb(&f_root);

        // Out of domain sample
        let ood_randomness = sponge.squeeze_field_elements(self.parameters.ood_samples);
        let gammas: Vec<F> = ood_randomness
            .iter()
            .map(|alpha| h_poly.evaluate(alpha))
            .collect();
        sponge.absorb(&gammas);

        // Proximity generator  TODO: check witness.num_round?
        // let comb_randomness: Vec<F> = sponge.squeeze_field_elements(self.parameters.ood_samples + self.parameters.repetitions[witness.num_round]);

        // Folding randomness for this round
        // let folding_randomness: Vec<F> = sponge.squeeze_field_elements(log2(k) as usize);

        //TODO: use 1 elem now
        // Proximity generator
        let comb_randomness: F = sponge.squeeze_field_elements(1)[0];

        // Folding randomness for next round
        let folding_randomness = sponge.squeeze_field_elements(1)[0];

        // Sample the indexes of L^k that we are going to use for querying the previous Merkle tree
        // let scaling_factor = witness.domain.len() / self.parameters.folding_factor;
        let num_repetitions = self.parameters.repetitions[witness.num_round];

        let stir_randomness_indexes = utils::dedup(
            (0..num_repetitions).map(|_| utils::squeeze_integer(sponge, witness.domain.len())),
        );

        let pow_nonce = utils::proof_of_work(sponge, self.parameters.pow_bits[witness.num_round]);

        // Not used
        let _shake_randomness: F = sponge.squeeze_field_elements(1)[0];

        // The verifier queries the previous oracle at the indexes of L^k (reading the
        // corresponding evals)

        let shift_challenge_domain = stir_randomness_indexes
            .iter()
            .map(|&index| witness.domain[index].clone())
            .collect();
        let queries_to_prev_ans: Vec<_> = stir_randomness_indexes
            .iter()
            .map(|&index| witness.folded_evals[index].clone())
            .collect();
        let queries_to_prev_proof = witness
            .merkle_tree
            .generate_multi_proof(stir_randomness_indexes.clone())
            .unwrap();
        let queries_to_prev = (queries_to_prev_ans, queries_to_prev_proof);

        // Here, we update the witness
        // First, compute the set of points we are actually going to query at
        let stir_randomness: Vec<_> = stir_randomness_indexes
            .iter()
            .map(|index| witness.domain[*index])
            .collect();

        let gamma_answers = gammas
            .iter()
            .zip(ood_randomness.iter())
            .map(|(y, x)| (*x, *y))
            .collect::<Vec<_>>();

        let quotient_answers = stir_randomness
            .iter()
            .map(|x| (*x, h_poly.evaluate(x)))
            .chain(gamma_answers.into_iter())
            .collect::<Vec<_>>();

        // Then compute the set we are quotienting by
        let quotient_set: Vec<_> = ood_randomness
            .into_iter()
            .chain(stir_randomness.iter().cloned())
            .collect();

        let ans_polynomial = poly_utils::interpolation::naive_interpolation(&quotient_answers);

        let mut shake_polynomial = DensePolynomial::from_coefficients_vec(vec![]);
        for (x, y) in quotient_answers {
            let num_polynomial = &ans_polynomial - &DensePolynomial::from_coefficients_vec(vec![y]);
            let den_polynomial = DensePolynomial::from_coefficients_vec(vec![-x, F::ONE]);
            shake_polynomial = shake_polynomial + (&num_polynomial / &den_polynomial);
        }

        // The quotient_polynomial is then computed
        let vanishing_poly = poly_utils::interpolation::vanishing_poly(&quotient_set);
        // Resue the ans_polynomial to compute the quotient_polynomial
        let numerator = &h_poly + &ans_polynomial;
        let quotient_polynomial = &numerator / &vanishing_poly;

        // This is the polynomial 1 + r * x + r^2 * x^2 + ... + r^n * x^n where n = |quotient_set|
        let scaling_polynomial = DensePolynomial::from_coefficients_vec(
            (0..quotient_set.len() + 1)
                .map(|i| comb_randomness.pow([i as u64]))
                .collect(),
        );

        let g_poly = &quotient_polynomial * &scaling_polynomial;

        //TODO: add folding_randomness
        let next_h_poly = poly_utils::folding::poly_fold(
            &g_poly,
            self.parameters.folding_factor,
            folding_randomness,
        );

        (
            WitnessExtended {
                domain: fold_random_domain,
                polynomial: next_h_poly,
                merkle_tree: f_merkle,
                folded_evals: f_folded_evaluations,
                num_round: witness.num_round + 1,
            },
            RoundProof {
                shift_challenge_domain,
                root: f_root,
                gammas,
                queries_to_prev,
                ans_polynomial,
                shake_polynomial,
                pow_nonce,
            },
        )
    }
}
