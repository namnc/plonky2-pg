// HACK: Ideally this would live in `benches/`, but `cargo bench` doesn't allow
// custom CLI argument parsing (even with harness disabled). We could also have
// put it in `src/bin/`, but then we wouldn't have access to
// `[dev-dependencies]`.

use core::num::ParseIntError;
use core::ops::RangeInclusive;
use core::str::FromStr;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use anyhow::{anyhow, Context as _, Result};
use log::{info, Level, LevelFilter};
use maybe_rayon::rayon;
use plonky2::field::types::{Field, Sample};
use plonky2::gates::noop::NoopGate;
use plonky2::hash::hash_types::{HashOut, HashOutTarget, MerkleCapTarget, RichField};
use plonky2::hash::merkle_proofs::{MerkleProof, MerkleProofTarget};
use plonky2::hash::merkle_tree::MerkleTree;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartialWitness, Witness};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{
    CircuitConfig, CommonCircuitData, VerifierCircuitTarget, VerifierOnlyCircuitData,
};
use plonky2::plonk::config::{
    AlgebraicHasher, GenericConfig, GenericHashOut, Hasher, PoseidonGoldilocksConfig,
};
use plonky2::plonk::proof::{CompressedProofWithPublicInputs, ProofWithPublicInputs};
use plonky2::plonk::prover::prove;
use plonky2::util::timing::TimingTree;
use plonky2_field::extension::{Extendable, FieldExtension};
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_util::log2_strict;
use rand::rngs::OsRng;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use serde::Serialize;
use structopt::StructOpt;

type ProofTuple<F, C, const D: usize> = (
    ProofWithPublicInputs<F, C, D>,
    VerifierOnlyCircuitData<C, D>,
    CommonCircuitData<F, D>,
);

#[derive(Clone, StructOpt, Debug)]
#[structopt(name = "bench_recursion")]
struct Options {
    /// Verbose mode (-v, -vv, -vvv, etc.)
    #[structopt(short, long, parse(from_occurrences))]
    verbose: usize,

    /// Apply an env_filter compatible log filter
    #[structopt(long, env, default_value)]
    log_filter: String,

    /// Random seed for deterministic runs.
    /// If not specified a new seed is generated from OS entropy.
    #[structopt(long, parse(try_from_str = parse_hex_u64))]
    seed: Option<u64>,

    /// Number of compute threads to use. Defaults to number of cores. Can be a single
    /// value or a rust style range.
    #[structopt(long, parse(try_from_str = parse_range_usize))]
    threads: Option<RangeInclusive<usize>>,

    /// Log2 gate count of the inner proof. Can be a single value or a rust style
    /// range.
    #[structopt(long, default_value="14", parse(try_from_str = parse_range_usize))]
    size: RangeInclusive<usize>,
}

/// Creates a dummy proof which should have `2 ** log2_size` rows.
fn dummy_proof<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    config: &CircuitConfig,
    log2_size: usize,
) -> Result<ProofTuple<F, C, D>> {
    // 'size' is in degree, but we want number of noop gates. A non-zero amount of padding will be added and size will be rounded to the next power of two. To hit our target size, we go just under the previous power of two and hope padding is less than half the proof.
    let num_dummy_gates = match log2_size {
        0 => return Err(anyhow!("size must be at least 1")),
        1 => 0,
        2 => 1,
        n => (1 << (n - 1)) + 1,
    };
    info!("Constructing inner proof with {} gates", num_dummy_gates);
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    for _ in 0..num_dummy_gates {
        builder.add_gate(NoopGate, vec![]);
    }
    builder.print_gate_counts(0);

    let data = builder.build::<C>();
    let inputs = PartialWitness::new();

    let mut timing = TimingTree::new("prove", Level::Debug);
    let proof = prove(&data.prover_only, &data.common, inputs, &mut timing)?;
    timing.print();
    data.verify(proof.clone())?;

    Ok((proof, data.verifier_only, data.common))
}

struct SemaphoreTargets {
    merkle_root: HashOutTarget,
    topic: [Target; 4],
    merkle_proof: MerkleProofTarget,
    private_key: [Target; 4],
    public_key_index: Target,
}

fn tree_height() -> usize {
    20
}

fn semaphore_proof<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    config: &CircuitConfig,
    private_key: [F; 4],
    topic: [F; 4],
    public_key_index: usize,
    merkle_proof: MerkleProof<F, PoseidonHash>,
    merkle_root_value: HashOut<F>,
) -> Result<ProofTuple<F, C, D>> {
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    let merkle_root_target = builder.add_virtual_hash();
    builder.register_public_inputs(&merkle_root_target.elements);
    let nullifier_target = builder.add_virtual_hash();
    builder.register_public_inputs(&nullifier_target.elements);
    let topic_target: [Target; 4] = builder.add_virtual_targets(4).try_into().unwrap();
    builder.register_public_inputs(&topic_target);

    // Merkle proof
    let merkle_proof_target = MerkleProofTarget {
        siblings: builder.add_virtual_hashes(tree_height()),
    };

    // Verify public key Merkle proof.
    let private_key_target: [Target; 4] = builder.add_virtual_targets(4).try_into().unwrap();
    let public_key_index_target = builder.add_virtual_target();
    let public_key_index_bits_target = builder.split_le(public_key_index_target, tree_height());
    let zero_target = builder.zero();
    builder.verify_merkle_proof::<PoseidonHash>(
        [private_key_target, [zero_target; 4]].concat(),
        &public_key_index_bits_target,
        merkle_root_target,
        &merkle_proof_target,
    );

    // Check nullifier.
    let should_be_nullifier_target =
        builder.hash_n_to_hash_no_pad::<PoseidonHash>([private_key_target, topic_target].concat());
    for i in 0..4 {
        builder.connect(
            nullifier_target.elements[i],
            should_be_nullifier_target.elements[i],
        );
    }

    let data = builder.build::<C>();
    let mut pw = PartialWitness::new();

    pw.set_hash_target(merkle_root_target, merkle_root_value);
    pw.set_target_arr(private_key_target, private_key);
    pw.set_target_arr(topic_target, topic);
    pw.set_target(
        public_key_index_target,
        F::from_canonical_usize(public_key_index),
    );

    for (ht, h) in merkle_proof_target
        .siblings
        .into_iter()
        .zip(merkle_proof.siblings.clone())
    {
        pw.set_hash_target(ht, h);
    }

    let mut timing = TimingTree::new("prove", Level::Debug);
    let proof = prove(&data.prover_only, &data.common, pw, &mut timing)?;
    timing.print();
    data.verify(proof.clone())?;

    Ok((proof, data.verifier_only, data.common))
}

fn recursive_proof<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    InnerC: GenericConfig<D, F = F>,
    const D: usize,
>(
    inner1: &ProofTuple<F, InnerC, D>,
    inner2: &ProofTuple<F, InnerC, D>,
    config: &CircuitConfig,
    min_degree_bits: Option<usize>,
) -> Result<ProofTuple<F, C, D>>
where
    InnerC::Hasher: AlgebraicHasher<F>,
{
    let (inner_proof1, inner_vd1, inner_cd1) = inner1;
    let (inner_proof2, inner_vd2, inner_cd2) = inner2;

    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    let pt1 = builder.add_virtual_proof_with_pis::<InnerC>(inner_cd1);
    let pt2 = builder.add_virtual_proof_with_pis::<InnerC>(inner_cd2);

    let inner_data1 = VerifierCircuitTarget {
        constants_sigmas_cap: builder.add_virtual_cap(inner_cd1.config.fri_config.cap_height),
        circuit_digest: builder.add_virtual_hash(),
    };
    let inner_data2 = VerifierCircuitTarget {
        constants_sigmas_cap: builder.add_virtual_cap(inner_cd2.config.fri_config.cap_height),
        circuit_digest: builder.add_virtual_hash(),
    };

    builder.register_public_inputs(inner_data1.circuit_digest.elements.as_slice());
    for i in 0..builder.config.fri_config.num_cap_elements() {
        builder.register_public_inputs(&inner_data1.constants_sigmas_cap.0[i].elements);
    }
    builder.verify_proof::<InnerC>(&pt1, &inner_data1, inner_cd1);

    builder.register_public_inputs(inner_data2.circuit_digest.elements.as_slice());
    for i in 0..builder.config.fri_config.num_cap_elements() {
        builder.register_public_inputs(&inner_data2.constants_sigmas_cap.0[i].elements);
    }
    builder.verify_proof::<InnerC>(&pt2, &inner_data2, inner_cd2);

    builder.print_gate_counts(0);

    if let Some(min_degree_bits) = min_degree_bits {
        // We don't want to pad all the way up to 2^min_degree_bits, as the builder will
        // add a few special gates afterward. So just pad to 2^(min_degree_bits
        // - 1) + 1. Then the builder will pad to the next power of two,
        // 2^min_degree_bits.
        let min_gates = (1 << (min_degree_bits - 1)) + 1;
        for _ in builder.num_gates()..min_gates {
            builder.add_gate(NoopGate, vec![]);
        }
    }

    let data = builder.build::<C>();

    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target(&pt1, inner_proof1);
    pw.set_verifier_data_target(&inner_data1, inner_vd1);
    pw.set_proof_with_pis_target(&pt2, inner_proof2);
    pw.set_verifier_data_target(&inner_data2, inner_vd2);

    let mut timing = TimingTree::new("prove", Level::Debug);
    let proof = prove(&data.prover_only, &data.common, pw, &mut timing)?;
    timing.print();

    data.verify(proof.clone())?;

    Ok((proof, data.verifier_only, data.common))
}

#[derive(Serialize)]
pub struct VerifierConfig {
    hash_size: usize,
    field_size: usize,
    ext_field_size: usize,
    merkle_height_size: usize,

    num_wires_cap: usize,
    num_plonk_zs_partial_products_cap: usize,
    num_quotient_polys_cap: usize,

    // openings
    num_openings_constants: usize,
    num_openings_plonk_sigmas: usize,
    num_openings_wires: usize,
    num_openings_plonk_zs: usize,
    num_openings_plonk_zs_next: usize,
    num_openings_partial_products: usize,
    num_openings_quotient_polys: usize,

    // fri proof
    // .commit phase
    num_fri_commit_round: usize,
    fri_commit_merkle_cap_height: usize,
    // .query round
    num_fri_query_round: usize,
    // ..init
    num_fri_query_init_constants_sigmas_v: usize,
    num_fri_query_init_constants_sigmas_p: usize,
    num_fri_query_init_wires_v: usize,
    num_fri_query_init_wires_p: usize,
    num_fri_query_init_zs_partial_v: usize,
    num_fri_query_init_zs_partial_p: usize,
    num_fri_query_init_quotient_v: usize,
    num_fri_query_init_quotient_p: usize,
    // ..steps
    num_fri_query_step0_v: usize,
    num_fri_query_step0_p: usize,
    num_fri_query_step1_v: usize,
    num_fri_query_step1_p: usize,
    // .final poly
    num_fri_final_poly_ext_v: usize,
    // public inputs
    num_public_inputs: usize,
}

#[derive(Serialize)]
pub struct ProofForCircom {
    wires_cap: Vec<Vec<String>>,
    plonk_zs_partial_products_cap: Vec<Vec<String>>,
    quotient_polys_cap: Vec<Vec<String>>,

    openings_constants: Vec<Vec<String>>,
    openings_plonk_sigmas: Vec<Vec<String>>,
    openings_wires: Vec<Vec<String>>,
    openings_plonk_zs: Vec<Vec<String>>,
    openings_plonk_zs_next: Vec<Vec<String>>,
    openings_partial_products: Vec<Vec<String>>,
    openings_quotient_polys: Vec<Vec<String>>,

    fri_commit_phase_merkle_caps: Vec<Vec<Vec<String>>>,

    fri_query_init_constants_sigmas_v: Vec<Vec<String>>,
    fri_query_init_constants_sigmas_p: Vec<Vec<Vec<String>>>,
    fri_query_init_wires_v: Vec<Vec<String>>,
    fri_query_init_wires_p: Vec<Vec<Vec<String>>>,
    fri_query_init_zs_partial_v: Vec<Vec<String>>,
    fri_query_init_zs_partial_p: Vec<Vec<Vec<String>>>,
    fri_query_init_quotient_v: Vec<Vec<String>>,
    fri_query_init_quotient_p: Vec<Vec<Vec<String>>>,

    fri_query_step0_v: Vec<Vec<Vec<String>>>,
    fri_query_step0_p: Vec<Vec<Vec<String>>>,
    fri_query_step1_v: Vec<Vec<Vec<String>>>,
    fri_query_step1_p: Vec<Vec<Vec<String>>>,

    fri_final_poly_ext_v: Vec<Vec<String>>,
    fri_pow_witness: String,

    public_inputs: Vec<String>,
}

// TODO: The input should be CommonCircuitData
pub fn generate_verifier_config<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    pwpi: &ProofWithPublicInputs<F, C, D>,
) -> anyhow::Result<VerifierConfig> {
    let proof = &pwpi.proof;
    assert_eq!(proof.opening_proof.query_round_proofs[0].steps.len(), 2);

    const HASH_SIZE: usize = 32;
    const FIELD_SIZE: usize = 8;
    const EXT_FIELD_SIZE: usize = 16;
    const MERKLE_HEIGHT_SIZE: usize = 1;

    let query_round_init_trees = &proof.opening_proof.query_round_proofs[0]
        .initial_trees_proof
        .evals_proofs;
    let query_round_steps = &proof.opening_proof.query_round_proofs[0].steps;

    let conf = VerifierConfig {
        hash_size: HASH_SIZE,
        field_size: FIELD_SIZE,
        ext_field_size: EXT_FIELD_SIZE,
        merkle_height_size: MERKLE_HEIGHT_SIZE,

        num_wires_cap: proof.wires_cap.0.len(),
        num_plonk_zs_partial_products_cap: proof.plonk_zs_partial_products_cap.0.len(),
        num_quotient_polys_cap: proof.quotient_polys_cap.0.len(),

        num_openings_constants: proof.openings.constants.len(),
        num_openings_plonk_sigmas: proof.openings.plonk_sigmas.len(),
        num_openings_wires: proof.openings.wires.len(),
        num_openings_plonk_zs: proof.openings.plonk_zs.len(),
        num_openings_plonk_zs_next: proof.openings.plonk_zs_next.len(),
        num_openings_partial_products: proof.openings.partial_products.len(),
        num_openings_quotient_polys: proof.openings.quotient_polys.len(),

        num_fri_commit_round: proof.opening_proof.commit_phase_merkle_caps.len(),
        fri_commit_merkle_cap_height: proof.opening_proof.commit_phase_merkle_caps[0].0.len(),
        num_fri_query_round: proof.opening_proof.query_round_proofs.len(),
        num_fri_query_init_constants_sigmas_v: query_round_init_trees[0].0.len(),
        num_fri_query_init_constants_sigmas_p: query_round_init_trees[0].1.siblings.len(),
        num_fri_query_init_wires_v: query_round_init_trees[1].0.len(),
        num_fri_query_init_wires_p: query_round_init_trees[1].1.siblings.len(),
        num_fri_query_init_zs_partial_v: query_round_init_trees[2].0.len(),
        num_fri_query_init_zs_partial_p: query_round_init_trees[2].1.siblings.len(),
        num_fri_query_init_quotient_v: query_round_init_trees[3].0.len(),
        num_fri_query_init_quotient_p: query_round_init_trees[3].1.siblings.len(),
        num_fri_query_step0_v: query_round_steps[0].evals.len(),
        num_fri_query_step0_p: query_round_steps[0].merkle_proof.siblings.len(),
        num_fri_query_step1_v: query_round_steps[1].evals.len(),
        num_fri_query_step1_p: query_round_steps[1].merkle_proof.siblings.len(),
        num_fri_final_poly_ext_v: proof.opening_proof.final_poly.coeffs.len(),

        num_public_inputs: pwpi.public_inputs.len(),
    };
    Ok(conf)
}

pub fn generate_proof_base64<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    pwpi: &ProofWithPublicInputs<F, C, D>,
    conf: &VerifierConfig,
) -> anyhow::Result<String> {
    let mut proof_size: usize =
        (conf.num_wires_cap + conf.num_plonk_zs_partial_products_cap + conf.num_quotient_polys_cap)
            * conf.hash_size;

    let mut wires_cap = vec![vec!["0".to_string(); 4]; conf.num_wires_cap];
    for i in 0..conf.num_wires_cap {
        let h = pwpi.proof.wires_cap.0[i].to_vec();
        for j in 0..h.len() {
            wires_cap[i][j] = h[j].to_canonical_u64().to_string();
        }
    }

    let mut plonk_zs_partial_products_cap =
        vec![vec!["0".to_string(); 4]; conf.num_plonk_zs_partial_products_cap];
    for i in 0..conf.num_plonk_zs_partial_products_cap {
        let h = pwpi.proof.plonk_zs_partial_products_cap.0[i].to_vec();
        for j in 0..h.len() {
            plonk_zs_partial_products_cap[i][j] = h[j].to_canonical_u64().to_string();
        }
    }

    let mut quotient_polys_cap = vec![vec!["0".to_string(); 4]; conf.num_quotient_polys_cap];
    for i in 0..conf.num_quotient_polys_cap {
        let h = pwpi.proof.quotient_polys_cap.0[i].to_vec();
        for j in 0..h.len() {
            quotient_polys_cap[i][j] = h[j].to_canonical_u64().to_string();
        }
    }

    proof_size += (conf.num_openings_constants
        + conf.num_openings_plonk_sigmas
        + conf.num_openings_wires
        + conf.num_openings_plonk_zs
        + conf.num_openings_plonk_zs_next
        + conf.num_openings_partial_products
        + conf.num_openings_quotient_polys)
        * conf.ext_field_size;

    let mut openings_constants = vec![vec!["0".to_string(); 2]; conf.num_openings_constants];
    for i in 0..conf.num_openings_constants {
        openings_constants[i][0] = pwpi.proof.openings.constants[i].to_basefield_array()[0]
            .to_canonical_u64()
            .to_string();
        openings_constants[i][1] = pwpi.proof.openings.constants[i].to_basefield_array()[1]
            .to_canonical_u64()
            .to_string();
    }
    let mut openings_plonk_sigmas = vec![vec!["0".to_string(); 2]; conf.num_openings_plonk_sigmas];
    for i in 0..conf.num_openings_plonk_sigmas {
        openings_plonk_sigmas[i][0] = pwpi.proof.openings.plonk_sigmas[i].to_basefield_array()[0]
            .to_canonical_u64()
            .to_string();
        openings_plonk_sigmas[i][1] = pwpi.proof.openings.plonk_sigmas[i].to_basefield_array()[1]
            .to_canonical_u64()
            .to_string();
    }
    let mut openings_wires = vec![vec!["0".to_string(); 2]; conf.num_openings_wires];
    for i in 0..conf.num_openings_wires {
        openings_wires[i][0] = pwpi.proof.openings.wires[i].to_basefield_array()[0]
            .to_canonical_u64()
            .to_string();
        openings_wires[i][1] = pwpi.proof.openings.wires[i].to_basefield_array()[1]
            .to_canonical_u64()
            .to_string();
    }
    let mut openings_plonk_zs = vec![vec!["0".to_string(); 2]; conf.num_openings_plonk_zs];
    for i in 0..conf.num_openings_plonk_zs {
        openings_plonk_zs[i][0] = pwpi.proof.openings.plonk_zs[i].to_basefield_array()[0]
            .to_canonical_u64()
            .to_string();
        openings_plonk_zs[i][1] = pwpi.proof.openings.plonk_zs[i].to_basefield_array()[1]
            .to_canonical_u64()
            .to_string();
    }
    let mut openings_plonk_zs_next =
        vec![vec!["0".to_string(); 2]; conf.num_openings_plonk_zs_next];
    for i in 0..conf.num_openings_plonk_zs_next {
        openings_plonk_zs_next[i][0] = pwpi.proof.openings.plonk_zs_next[i].to_basefield_array()[0]
            .to_canonical_u64()
            .to_string();
        openings_plonk_zs_next[i][1] = pwpi.proof.openings.plonk_zs_next[i].to_basefield_array()[1]
            .to_canonical_u64()
            .to_string();
    }
    let mut openings_partial_products =
        vec![vec!["0".to_string(); 2]; conf.num_openings_partial_products];
    for i in 0..conf.num_openings_partial_products {
        openings_partial_products[i][0] = pwpi.proof.openings.partial_products[i]
            .to_basefield_array()[0]
            .to_canonical_u64()
            .to_string();
        openings_partial_products[i][1] = pwpi.proof.openings.partial_products[i]
            .to_basefield_array()[1]
            .to_canonical_u64()
            .to_string();
    }
    let mut openings_quotient_polys =
        vec![vec!["0".to_string(); 2]; conf.num_openings_quotient_polys];
    for i in 0..conf.num_openings_quotient_polys {
        openings_quotient_polys[i][0] = pwpi.proof.openings.quotient_polys[i].to_basefield_array()
            [0]
        .to_canonical_u64()
        .to_string();
        openings_quotient_polys[i][1] = pwpi.proof.openings.quotient_polys[i].to_basefield_array()
            [1]
        .to_canonical_u64()
        .to_string();
    }

    proof_size += (conf.num_fri_commit_round * conf.fri_commit_merkle_cap_height) * conf.hash_size;

    let mut fri_commit_phase_merkle_caps =
        vec![
            vec![vec!["0".to_string(); 4]; conf.fri_commit_merkle_cap_height];
            conf.num_fri_commit_round
        ];
    for i in 0..conf.num_fri_commit_round {
        let h = pwpi.proof.opening_proof.commit_phase_merkle_caps[i].flatten();
        assert_eq!(h.len(), 4 * conf.fri_commit_merkle_cap_height);
        for j in 0..conf.fri_commit_merkle_cap_height {
            for k in 0..4 {
                fri_commit_phase_merkle_caps[i][j][k] = h[j * 4 + k].to_canonical_u64().to_string();
            }
        }
    }

    proof_size += conf.num_fri_query_round
        * ((conf.num_fri_query_init_constants_sigmas_v
            + conf.num_fri_query_init_wires_v
            + conf.num_fri_query_init_zs_partial_v
            + conf.num_fri_query_init_quotient_v)
            * conf.field_size
            + (conf.num_fri_query_init_constants_sigmas_p
                + conf.num_fri_query_init_wires_p
                + conf.num_fri_query_init_zs_partial_p
                + conf.num_fri_query_init_quotient_p)
                * conf.hash_size
            + conf.merkle_height_size * 4);

    proof_size += conf.num_fri_query_round
        * (conf.num_fri_query_step0_v * conf.ext_field_size
            + conf.num_fri_query_step0_p * conf.hash_size
            + conf.merkle_height_size
            + conf.num_fri_query_step1_v * conf.ext_field_size
            + conf.num_fri_query_step1_p * conf.hash_size
            + conf.merkle_height_size);

    let mut fri_query_init_constants_sigmas_v =
        vec![
            vec!["0".to_string(); conf.num_fri_query_init_constants_sigmas_v];
            conf.num_fri_query_round
        ];
    let mut fri_query_init_wires_v =
        vec![vec!["0".to_string(); conf.num_fri_query_init_wires_v]; conf.num_fri_query_round];
    let mut fri_query_init_zs_partial_v =
        vec![vec!["0".to_string(); conf.num_fri_query_init_zs_partial_v]; conf.num_fri_query_round];
    let mut fri_query_init_quotient_v =
        vec![vec!["0".to_string(); conf.num_fri_query_init_quotient_v]; conf.num_fri_query_round];

    let mut fri_query_init_constants_sigmas_p =
        vec![
            vec![vec!["0".to_string(); 4]; conf.num_fri_query_init_constants_sigmas_p];
            conf.num_fri_query_round
        ];
    let mut fri_query_init_wires_p =
        vec![
            vec![vec!["0".to_string(); 4]; conf.num_fri_query_init_wires_p];
            conf.num_fri_query_round
        ];
    let mut fri_query_init_zs_partial_p =
        vec![
            vec![vec!["0".to_string(); 4]; conf.num_fri_query_init_zs_partial_p];
            conf.num_fri_query_round
        ];
    let mut fri_query_init_quotient_p =
        vec![
            vec![vec!["0".to_string(); 4]; conf.num_fri_query_init_quotient_p];
            conf.num_fri_query_round
        ];

    let mut fri_query_step0_v =
        vec![vec![vec!["0".to_string(); 2]; conf.num_fri_query_step0_v]; conf.num_fri_query_round];
    let mut fri_query_step1_v =
        vec![vec![vec!["0".to_string(); 2]; conf.num_fri_query_step1_v]; conf.num_fri_query_round];
    let mut fri_query_step0_p =
        vec![vec![vec!["0".to_string(); 4]; conf.num_fri_query_step0_p]; conf.num_fri_query_round];
    let mut fri_query_step1_p =
        vec![vec![vec!["0".to_string(); 4]; conf.num_fri_query_step1_p]; conf.num_fri_query_round];

    for i in 0..conf.num_fri_query_round {
        assert_eq!(
            pwpi.proof.opening_proof.query_round_proofs[i]
                .initial_trees_proof
                .evals_proofs
                .len(),
            4
        );
        for j in 0..conf.num_fri_query_init_constants_sigmas_v {
            fri_query_init_constants_sigmas_v[i][j] = pwpi.proof.opening_proof.query_round_proofs
                [i]
                .initial_trees_proof
                .evals_proofs[0]
                .0[j]
                .to_canonical_u64()
                .to_string();
        }
        for j in 0..conf.num_fri_query_init_wires_v {
            fri_query_init_wires_v[i][j] = pwpi.proof.opening_proof.query_round_proofs[i]
                .initial_trees_proof
                .evals_proofs[1]
                .0[j]
                .to_canonical_u64()
                .to_string();
        }
        for j in 0..conf.num_fri_query_init_zs_partial_v {
            fri_query_init_zs_partial_v[i][j] = pwpi.proof.opening_proof.query_round_proofs[i]
                .initial_trees_proof
                .evals_proofs[2]
                .0[j]
                .to_canonical_u64()
                .to_string();
        }
        for j in 0..conf.num_fri_query_init_quotient_v {
            fri_query_init_quotient_v[i][j] = pwpi.proof.opening_proof.query_round_proofs[i]
                .initial_trees_proof
                .evals_proofs[3]
                .0[j]
                .to_canonical_u64()
                .to_string();
        }
        for j in 0..conf.num_fri_query_init_constants_sigmas_p {
            let h = pwpi.proof.opening_proof.query_round_proofs[i]
                .initial_trees_proof
                .evals_proofs[0]
                .1
                .siblings[j]
                .to_vec();
            assert_eq!(h.len(), 4);
            for k in 0..4 {
                fri_query_init_constants_sigmas_p[i][j][k] = h[k].to_canonical_u64().to_string();
            }
        }
        for j in 0..conf.num_fri_query_init_wires_p {
            let h = pwpi.proof.opening_proof.query_round_proofs[i]
                .initial_trees_proof
                .evals_proofs[1]
                .1
                .siblings[j]
                .to_vec();
            assert_eq!(h.len(), 4);
            for k in 0..4 {
                fri_query_init_wires_p[i][j][k] = h[k].to_canonical_u64().to_string();
            }
        }
        for j in 0..conf.num_fri_query_init_zs_partial_p {
            let h = pwpi.proof.opening_proof.query_round_proofs[i]
                .initial_trees_proof
                .evals_proofs[2]
                .1
                .siblings[j]
                .to_vec();
            assert_eq!(h.len(), 4);
            for k in 0..4 {
                fri_query_init_zs_partial_p[i][j][k] = h[k].to_canonical_u64().to_string();
            }
        }
        for j in 0..conf.num_fri_query_init_quotient_p {
            let h = pwpi.proof.opening_proof.query_round_proofs[i]
                .initial_trees_proof
                .evals_proofs[3]
                .1
                .siblings[j]
                .to_vec();
            assert_eq!(h.len(), 4);
            for k in 0..4 {
                fri_query_init_quotient_p[i][j][k] = h[k].to_canonical_u64().to_string();
            }
        }
        for j in 0..conf.num_fri_query_step0_v {
            fri_query_step0_v[i][j][0] = pwpi.proof.opening_proof.query_round_proofs[i].steps[0]
                .evals[j]
                .to_basefield_array()[0]
                .to_canonical_u64()
                .to_string();
            fri_query_step0_v[i][j][1] = pwpi.proof.opening_proof.query_round_proofs[i].steps[0]
                .evals[j]
                .to_basefield_array()[1]
                .to_canonical_u64()
                .to_string();
        }
        for j in 0..conf.num_fri_query_step1_v {
            fri_query_step1_v[i][j][0] = pwpi.proof.opening_proof.query_round_proofs[i].steps[1]
                .evals[j]
                .to_basefield_array()[0]
                .to_canonical_u64()
                .to_string();
            fri_query_step1_v[i][j][1] = pwpi.proof.opening_proof.query_round_proofs[i].steps[1]
                .evals[j]
                .to_basefield_array()[1]
                .to_canonical_u64()
                .to_string();
        }
        assert_eq!(
            pwpi.proof.opening_proof.query_round_proofs[i].steps.len(),
            2
        );
        for j in 0..conf.num_fri_query_step0_p {
            let h = pwpi.proof.opening_proof.query_round_proofs[i].steps[0]
                .merkle_proof
                .siblings[j]
                .to_vec();
            assert_eq!(h.len(), 4);
            for k in 0..4 {
                fri_query_step0_p[i][j][k] = h[k].to_canonical_u64().to_string();
            }
        }
        for j in 0..conf.num_fri_query_step1_p {
            let h = pwpi.proof.opening_proof.query_round_proofs[i].steps[1]
                .merkle_proof
                .siblings[j]
                .to_vec();
            assert_eq!(h.len(), 4);
            for k in 0..4 {
                fri_query_step1_p[i][j][k] = h[k].to_canonical_u64().to_string();
            }
        }
    }

    proof_size += conf.num_fri_final_poly_ext_v * conf.ext_field_size;

    let mut fri_final_poly_ext_v = vec![vec!["0".to_string(); 2]; conf.num_fri_final_poly_ext_v];
    for i in 0..conf.num_fri_final_poly_ext_v {
        fri_final_poly_ext_v[i][0] = pwpi.proof.opening_proof.final_poly.coeffs[i]
            .to_basefield_array()[0]
            .to_canonical_u64()
            .to_string();
        fri_final_poly_ext_v[i][1] = pwpi.proof.opening_proof.final_poly.coeffs[i]
            .to_basefield_array()[1]
            .to_canonical_u64()
            .to_string();
    }

    proof_size += conf.field_size;

    proof_size += conf.num_public_inputs * conf.field_size;

    let mut public_inputs = vec!["0".to_string(); conf.num_public_inputs];
    for i in 0..conf.num_public_inputs {
        public_inputs[i] = pwpi.public_inputs[i].to_canonical_u64().to_string();
    }

    let circom_proof = ProofForCircom {
        wires_cap,
        plonk_zs_partial_products_cap,
        quotient_polys_cap,
        openings_constants,
        openings_plonk_sigmas,
        openings_wires,
        openings_plonk_zs,
        openings_plonk_zs_next,
        openings_partial_products,
        openings_quotient_polys,
        fri_commit_phase_merkle_caps,
        fri_query_init_constants_sigmas_v,
        fri_query_init_constants_sigmas_p,
        fri_query_init_wires_v,
        fri_query_init_wires_p,
        fri_query_init_zs_partial_v,
        fri_query_init_zs_partial_p,
        fri_query_init_quotient_v,
        fri_query_init_quotient_p,
        fri_query_step0_v,
        fri_query_step0_p,
        fri_query_step1_v,
        fri_query_step1_p,
        fri_final_poly_ext_v,
        fri_pow_witness: pwpi
            .proof
            .opening_proof
            .pow_witness
            .to_canonical_u64()
            .to_string(),
        public_inputs,
    };

    let proof_bytes = pwpi.to_bytes();
    assert_eq!(proof_bytes.len(), proof_size);
    println!("proof size: {}", proof_size);

    Ok(serde_json::to_string(&circom_proof).unwrap())
}

pub fn generate_circom_verifier<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    conf: &VerifierConfig,
    common: &CommonCircuitData<F, D>,
    verifier_only: &VerifierOnlyCircuitData<C, D>,
) -> anyhow::Result<(String, String)> {
    assert_eq!(F::BITS, 64);
    assert_eq!(F::Extension::BITS, 128);
    println!("Generating Circom files ...");

    /*
    // TEST FILE PATH
    let path = Path::new("lorem_ipsum.txt");
    let display = path.display();

    // Open a file in write-only mode, returns `io::Result<File>`
    let mut file = match File::create(&path) {
        Err(why) => panic!("couldn't create {}: {}", display, why),
        Ok(file) => file,
    };

    // Write the `LOREM_IPSUM` string to `file`, returns `io::Result<()>`
    match file.write_all("LOREM_IPSUM".as_bytes()) {
        Err(why) => panic!("couldn't write to {}: {}", display, why),
        Ok(_) => println!("successfully wrote to {}", display),
    }
    // --------------
    */

    // Load template contract
    let mut constants = std::fs::read_to_string("./template_constants.circom")
        .expect("Something went wrong reading the file");

    let k_is = &common.k_is;
    let mut k_is_str = "".to_owned();
    for i in 0..k_is.len() {
        k_is_str += &*("  k_is[".to_owned()
            + &*i.to_string()
            + "] = "
            + &*k_is[i].to_canonical_u64().to_string()
            + ";\n");
    }
    constants = constants.replace("  $SET_K_IS;\n", &*k_is_str);

    let reduction_arity_bits = &common.fri_params.reduction_arity_bits;
    let mut reduction_arity_bits_str = "".to_owned();
    for i in 0..reduction_arity_bits.len() {
        reduction_arity_bits_str += &*("  bits[".to_owned()
            + &*i.to_string()
            + "] = "
            + &*reduction_arity_bits[i].to_string()
            + ";\n");
    }
    constants = constants.replace("  $SET_REDUCTION_ARITY_BITS;\n", &*reduction_arity_bits_str);
    constants = constants.replace(
        "$NUM_REDUCTION_ARITY_BITS",
        &*reduction_arity_bits.len().to_string(),
    );

    constants = constants.replace("$NUM_PUBLIC_INPUTS", &*conf.num_public_inputs.to_string());
    constants = constants.replace("$NUM_WIRES_CAP", &*conf.num_wires_cap.to_string());
    constants = constants.replace(
        "$NUM_PLONK_ZS_PARTIAL_PRODUCTS_CAP",
        &*conf.num_plonk_zs_partial_products_cap.to_string(),
    );
    constants = constants.replace(
        "$NUM_QUOTIENT_POLYS_CAP",
        &*conf.num_quotient_polys_cap.to_string(),
    );
    constants = constants.replace(
        "$NUM_OPENINGS_CONSTANTS",
        &*conf.num_openings_constants.to_string(),
    );
    constants = constants.replace(
        "$NUM_OPENINGS_PLONK_SIGMAS",
        &*conf.num_openings_plonk_sigmas.to_string(),
    );
    constants = constants.replace("$NUM_OPENINGS_WIRES", &*conf.num_openings_wires.to_string());
    constants = constants.replace(
        "$NUM_OPENINGS_PLONK_ZS0",
        &*conf.num_openings_plonk_zs.to_string(),
    );
    constants = constants.replace(
        "$NUM_OPENINGS_PLONK_ZS_NEXT",
        &*conf.num_openings_plonk_zs_next.to_string(),
    );
    constants = constants.replace(
        "$NUM_OPENINGS_PARTIAL_PRODUCTS",
        &*conf.num_openings_partial_products.to_string(),
    );
    constants = constants.replace(
        "$NUM_OPENINGS_QUOTIENT_POLYS",
        &*conf.num_openings_quotient_polys.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_COMMIT_ROUND",
        &*conf.num_fri_commit_round.to_string(),
    );
    constants = constants.replace(
        "$FRI_COMMIT_MERKLE_CAP_HEIGHT",
        &*conf.fri_commit_merkle_cap_height.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_ROUND",
        &*conf.num_fri_query_round.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_INIT_CONSTANTS_SIGMAS_V",
        &*conf.num_fri_query_init_constants_sigmas_v.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_INIT_CONSTANTS_SIGMAS_P",
        &*conf.num_fri_query_init_constants_sigmas_p.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_INIT_WIRES_V",
        &*conf.num_fri_query_init_wires_v.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_INIT_WIRES_P",
        &*conf.num_fri_query_init_wires_p.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_INIT_ZS_PARTIAL_V",
        &*conf.num_fri_query_init_zs_partial_v.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_INIT_ZS_PARTIAL_P",
        &*conf.num_fri_query_init_zs_partial_p.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_INIT_QUOTIENT_V",
        &*conf.num_fri_query_init_quotient_v.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_INIT_QUOTIENT_P",
        &*conf.num_fri_query_init_quotient_p.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_STEP0_V",
        &*conf.num_fri_query_step0_v.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_STEP0_P",
        &*conf.num_fri_query_step0_p.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_STEP1_V",
        &*conf.num_fri_query_step1_v.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_QUERY_STEP1_P",
        &*conf.num_fri_query_step1_p.to_string(),
    );
    constants = constants.replace(
        "$NUM_FRI_FINAL_POLY_EXT_V",
        &*conf.num_fri_final_poly_ext_v.to_string(),
    );
    constants = constants.replace(
        "$NUM_CHALLENGES",
        &*common.config.num_challenges.to_string(),
    );

    let circuit_digest = verifier_only.circuit_digest.to_vec();
    let mut circuit_digest_str = "".to_owned();
    for i in 0..circuit_digest.len() {
        circuit_digest_str += &*("  cd[".to_owned()
            + &*i.to_string()
            + "] = "
            + &*circuit_digest[i].to_canonical_u64().to_string()
            + ";\n");
    }
    constants = constants.replace("  $SET_CIRCUIT_DIGEST;\n", &*circuit_digest_str);

    constants = constants.replace(
        "$FRI_RATE_BITS",
        &*common.config.fri_config.rate_bits.to_string(),
    );
    constants = constants.replace("$DEGREE_BITS", &*common.degree_bits().to_string());
    constants = constants.replace(
        "$NUM_GATE_CONSTRAINTS",
        &*common.num_gate_constraints.to_string(),
    );
    constants = constants.replace(
        "$QUOTIENT_DEGREE_FACTOR",
        &*common.quotient_degree_factor.to_string(),
    );
    constants = constants.replace(
        "$MIN_FRI_POW_RESPONSE",
        &*(common.config.fri_config.proof_of_work_bits + (64 - F::order().bits()) as u32)
            .to_string(),
    );
    let g = F::Extension::primitive_root_of_unity(common.degree_bits());
    constants = constants.replace(
        "$G_FROM_DEGREE_BITS_0",
        &g.to_basefield_array()[0].to_string(),
    );
    constants = constants.replace(
        "$G_FROM_DEGREE_BITS_1",
        &g.to_basefield_array()[1].to_string(),
    );
    let log_n = log2_strict(common.fri_params.lde_size());
    constants = constants.replace("$LOG_SIZE_OF_LDE_DOMAIN", &*log_n.to_string());
    constants = constants.replace(
        "$MULTIPLICATIVE_GROUP_GENERATOR",
        &*F::MULTIPLICATIVE_GROUP_GENERATOR.to_string(),
    );
    constants = constants.replace(
        "$PRIMITIVE_ROOT_OF_UNITY_LDE",
        &*F::primitive_root_of_unity(log_n).to_string(),
    );
    // TODO: add test with config zero_knoledge = true
    constants = constants.replace(
        "$ZERO_KNOWLEDGE",
        &*common.config.zero_knowledge.to_string(),
    );
    let g = F::primitive_root_of_unity(1);
    constants = constants.replace("$G_ARITY_BITS_1", &g.to_string());
    let g = F::primitive_root_of_unity(2);
    constants = constants.replace("$G_ARITY_BITS_2", &g.to_string());
    let g = F::primitive_root_of_unity(3);
    constants = constants.replace("$G_ARITY_BITS_3", &g.to_string());
    let g = F::primitive_root_of_unity(4);
    constants = constants.replace("$G_ARITY_BITS_4", &g.to_string());

    // Load gate template
    let mut gates_lib = std::fs::read_to_string("./template_gates.circom")
        .expect("Something went wrong reading the file");

    let num_selectors = common.selectors_info.num_selectors();
    constants = constants.replace("$NUM_SELECTORS", &num_selectors.to_string());
    let mut evaluate_gate_constraints_str = "".to_owned();
    let mut last_component_name = "".to_owned();
    for (row, gate) in common.gates.iter().enumerate() {
        if gate.0.id().eq("NoopGate") {
            continue;
        }
        let selector_index = common.selectors_info.selector_indices[row];
        let group_range = common.selectors_info.groups[selector_index].clone();
        let mut c = 0;

        evaluate_gate_constraints_str = evaluate_gate_constraints_str + "\n";
        let mut filter_str = "filter <== ".to_owned();
        let filter_chain = group_range
            .filter(|&i| i != row)
            .chain((num_selectors > 1).then_some(u32::MAX as usize));
        for i in filter_chain {
            filter_str += &*("GlExtMul()(GlExtSub()(GlExt(".to_owned()
                + &i.to_string()
                + ", 0)(), "
                + "constants["
                + &*selector_index.to_string()
                + "]), ");
            c = c + 1;
        }
        filter_str += &*("GlExt(1, 0)()".to_owned());
        for _ in 0..c {
            filter_str = filter_str + ")";
        }
        filter_str = filter_str + ";";

        let mut eval_str = "  // ".to_owned() + &*gate.0.id() + "\n";
        let gate_name = gate.0.id();
        if gate_name.eq("PublicInputGate")
            || gate_name[0..11].eq("BaseSumGate")
            || gate_name[0..12].eq("ConstantGate")
            || gate_name[0..12].eq("PoseidonGate")
            || gate_name[0..12].eq("ReducingGate")
            || gate_name[0..14].eq("ArithmeticGate")
            || gate_name[0..15].eq("PoseidonMdsGate")
            || gate_name[0..16].eq("MulExtensionGate")
            || gate_name[0..16].eq("RandomAccessGate")
            || gate_name[0..18].eq("ExponentiationGate")
            || gate_name[0..21].eq("ReducingExtensionGate")
            || gate_name[0..23].eq("ArithmeticExtensionGate")
            || gate_name[0..26].eq("LowDegreeInterpolationGate")
        {
            //TODO: use num_coeff as a param (same TODO for other gates)
            let mut code_str = gate.0.export_circom_verification_code();
            code_str = code_str.replace("$SET_FILTER;", &*filter_str);
            let v: Vec<&str> = code_str.split(' ').collect();
            let template_name = &v[1][0..v[1].len() - 2];
            let component_name = "c_".to_owned() + template_name;
            eval_str +=
                &*("  component ".to_owned() + &*component_name + " = " + template_name + "();\n");
            eval_str += &*("  ".to_owned() + &*component_name + ".constants <== constants;\n");
            eval_str += &*("  ".to_owned() + &*component_name + ".wires <== wires;\n");
            eval_str += &*("  ".to_owned()
                + &*component_name
                + ".public_input_hash <== public_input_hash;\n");
            if last_component_name == "" {
                eval_str +=
                    &*("  ".to_owned() + &*component_name + ".constraints <== constraints;\n");
            } else {
                eval_str += &*("  ".to_owned()
                    + &*component_name
                    + ".constraints <== "
                    + &*last_component_name
                    + ".out;\n");
            }
            gates_lib += &*(code_str + "\n");
            last_component_name = component_name.clone();
        } else {
            todo!("{}", "gate not implemented: ".to_owned() + &gate_name)
        }
        evaluate_gate_constraints_str += &*eval_str;
    }

    evaluate_gate_constraints_str += &*("  out <== ".to_owned() + &*last_component_name + ".out;");
    gates_lib = gates_lib.replace(
        "  $EVALUATE_GATE_CONSTRAINTS;",
        &evaluate_gate_constraints_str,
    );

    gates_lib = gates_lib.replace(
        "$NUM_GATE_CONSTRAINTS",
        &*common.num_gate_constraints.to_string(),
    );
    gates_lib = gates_lib.replace("$NUM_SELECTORS", &num_selectors.to_string());
    gates_lib = gates_lib.replace(
        "$NUM_OPENINGS_CONSTANTS",
        &*conf.num_openings_constants.to_string(),
    );
    gates_lib = gates_lib.replace("$NUM_OPENINGS_WIRES", &*conf.num_openings_wires.to_string());
    gates_lib = gates_lib.replace("$F_EXT_W", &*F::W.to_basefield_array()[0].to_string());

    let sigma_cap_count = 1 << common.config.fri_config.cap_height;
    constants = constants.replace("$SIGMA_CAP_COUNT", &*sigma_cap_count.to_string());

    let mut sigma_cap_str = "".to_owned();
    for i in 0..sigma_cap_count {
        let cap = verifier_only.constants_sigmas_cap.0[i];
        let hash = cap.to_vec();
        assert_eq!(hash.len(), 4);
        sigma_cap_str += &*("  sc[".to_owned()
            + &*i.to_string()
            + "][0] = "
            + &*hash[0].to_canonical_u64().to_string()
            + ";\n");
        sigma_cap_str += &*("  sc[".to_owned()
            + &*i.to_string()
            + "][1] = "
            + &*hash[1].to_canonical_u64().to_string()
            + ";\n");
        sigma_cap_str += &*("  sc[".to_owned()
            + &*i.to_string()
            + "][2] = "
            + &*hash[2].to_canonical_u64().to_string()
            + ";\n");
        sigma_cap_str += &*("  sc[".to_owned()
            + &*i.to_string()
            + "][3] = "
            + &*hash[3].to_canonical_u64().to_string()
            + ";\n");
    }
    constants = constants.replace("  $SET_SIGMA_CAP;\n", &*sigma_cap_str);

    Ok((constants, gates_lib))
}

/// Test serialization and print some size info.
fn test_serialization<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    proof: &ProofWithPublicInputs<F, C, D>,
    vd: &VerifierOnlyCircuitData<C, D>,
    cd: &CommonCircuitData<F, D>,
) -> Result<()> {
    let proof_bytes = proof.to_bytes();
    info!("Proof length: {} bytes", proof_bytes.len());
    let proof_from_bytes = ProofWithPublicInputs::from_bytes(proof_bytes, cd)?;
    assert_eq!(proof, &proof_from_bytes);

    let now = std::time::Instant::now();
    let compressed_proof = proof.clone().compress(&vd.circuit_digest, cd)?;
    let decompressed_compressed_proof = compressed_proof
        .clone()
        .decompress(&vd.circuit_digest, cd)?;
    info!("{:.4}s to compress proof", now.elapsed().as_secs_f64());
    assert_eq!(proof, &decompressed_compressed_proof);

    let compressed_proof_bytes = compressed_proof.to_bytes();
    info!(
        "Compressed proof length: {} bytes",
        compressed_proof_bytes.len()
    );
    let compressed_proof_from_bytes =
        CompressedProofWithPublicInputs::from_bytes(compressed_proof_bytes, cd)?;
    assert_eq!(compressed_proof, compressed_proof_from_bytes);

    Ok(())
}

fn benchmark(config: &CircuitConfig, log2_inner_size: usize) -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = GoldilocksField;

    // CREATE TREE WITH 2^n leaves
    let n = 1 << tree_height();

    let private_keys: Vec<[F; 4]> = (0..n).map(|_| F::rand_array()).collect();
    let public_keys: Vec<Vec<F>> = private_keys
        .iter()
        .map(|&sk| {
            PoseidonHash::hash_no_pad(&[sk, [F::ZERO; 4]].concat())
                .elements
                .to_vec()
        })
        .collect();

    let merkle_tree: MerkleTree<GoldilocksField, PoseidonHash> = MerkleTree::new(public_keys, 0);
    let merkle_root_value = merkle_tree.cap.0[0];

    // Start with a dummy proof of specified size
    let merkle_proof1 = merkle_tree.prove(1);
    let topic1: [GoldilocksField; 4] = F::rand_array();
    let nullifier1 = PoseidonHash::hash_no_pad(&[private_keys[1], topic1].concat()).elements;
    let inner1 = semaphore_proof(
        config,
        private_keys[1],
        topic1,
        1,
        merkle_proof1,
        merkle_root_value,
    )?; //dummy_proof::<F, C, D>(config, log2_inner_size)?;
    let (_, _, cd1) = &inner1;
    info!(
        "Initial proof 1 degree {} = 2^{}",
        cd1.degree(),
        cd1.degree_bits()
    );

    let merkle_proof2 = merkle_tree.prove(2);
    let topic2: [GoldilocksField; 4] = F::rand_array();
    let nullifier2 = PoseidonHash::hash_no_pad(&[private_keys[2], topic2].concat()).elements;
    let inner2 = semaphore_proof(
        config,
        private_keys[2],
        topic1,
        2,
        merkle_proof2,
        merkle_root_value,
    )?; //dummy_proof::<F, C, D>(config, log2_inner_size)?;
        //let inner2 = dummy_proof::<F, C, D>(config, log2_inner_size)?;
    let (_, _, cd2) = &inner2;
    info!(
        "Initial proof 2 degree {} = 2^{}",
        cd2.degree(),
        cd2.degree_bits()
    );

    // Recursively verify the proof
    let middle1 = recursive_proof::<F, C, C, D>(&inner1, &inner2, config, None)?;
    let (_, _, cdm1) = &middle1;
    info!(
        "Single recursion proof 1 degree {} = 2^{}",
        cdm1.degree(),
        cdm1.degree_bits()
    );

    let merkle_proof3 = merkle_tree.prove(3);
    let topic3: [GoldilocksField; 4] = F::rand_array();
    //let inner3 = dummy_proof::<F, C, D>(config, log2_inner_size)?;
    let nullifier3 = PoseidonHash::hash_no_pad(&[private_keys[3], topic3].concat()).elements;
    let inner3 = semaphore_proof(
        config,
        private_keys[3],
        topic1,
        3,
        merkle_proof3,
        merkle_root_value,
    )?; //dummy_proof::<F, C, D>(config, log2_inner_size)?;
    let (_, _, cd3) = &inner3;
    info!(
        "Initial proof 3 degree {} = 2^{}",
        cd3.degree(),
        cd3.degree_bits()
    );

    let merkle_proof4 = merkle_tree.prove(4);
    let topic4: [GoldilocksField; 4] = F::rand_array();
    let nullifier4 = PoseidonHash::hash_no_pad(&[private_keys[4], topic1].concat()).elements;
    let inner4 = semaphore_proof(
        config,
        private_keys[4],
        topic4,
        4,
        merkle_proof4,
        merkle_root_value,
    )?; //dummy_proof::<F, C, D>(config, log2_inner_size)?;
        //let inner4 = dummy_proof::<F, C, D>(config, log2_inner_size)?;
    let (_, _, cd4) = &inner4;
    info!(
        "Initial proof 4 degree {} = 2^{}",
        cd4.degree(),
        cd4.degree_bits()
    );

    // Recursively verify the proof
    let middle2 = recursive_proof::<F, C, C, D>(&inner3, &inner4, config, None)?;
    let (_, _, cdm2) = &middle2;
    info!(
        "Single recursion proof 2 degree {} = 2^{}",
        cdm2.degree(),
        cdm2.degree_bits()
    );

    // Add a second layer of recursion to shrink the proof size further
    let outer = recursive_proof::<F, C, C, D>(&middle1, &middle2, config, None)?;
    let (proof, vd, cd) = &outer;
    info!(
        "Double recursion proof degree {} = 2^{}",
        cd.degree(),
        cd.degree_bits()
    );

    test_serialization(proof, vd, cd)?;

    let conf = generate_verifier_config(&proof)?;
    let (circom_constants, circom_gates) = generate_circom_verifier(&conf, &cd, &vd)?;

    let mut circom_file = File::create("./circom/circuits/constants.circom")?;
    circom_file.write_all(circom_constants.as_bytes())?;
    circom_file = File::create("./circom/circuits/gates.circom")?;
    circom_file.write_all(circom_gates.as_bytes())?;

    let proof_json = generate_proof_base64(&proof, &conf)?;

    if !Path::new("./circom/test/data").is_dir() {
        std::fs::create_dir("./circom/test/data")?;
    }

    let mut proof_file = File::create("./circom/test/data/proof.json")?;
    proof_file.write_all(proof_json.as_bytes())?;

    let mut conf_file = File::create("./circom/test/data/conf.json")?;
    conf_file.write_all(serde_json::to_string(&conf)?.as_ref())?;

    Ok(())
}

fn main() -> Result<()> {
    // Parse command line arguments, see `--help` for details.
    let options = Options::from_args_safe()?;

    // Initialize logging
    let mut builder = env_logger::Builder::from_default_env();
    builder.parse_filters(&options.log_filter);
    builder.format_timestamp(None);
    match options.verbose {
        0 => &mut builder,
        1 => builder.filter_level(LevelFilter::Info),
        2 => builder.filter_level(LevelFilter::Debug),
        _ => builder.filter_level(LevelFilter::Trace),
    };
    builder.try_init()?;

    // Initialize randomness source
    let rng_seed = options.seed.unwrap_or_else(|| OsRng::default().next_u64());
    info!("Using random seed {rng_seed:16x}");
    let _rng = ChaCha8Rng::seed_from_u64(rng_seed);
    // TODO: Use `rng` to create deterministic runs

    let num_cpus = num_cpus::get();
    let threads = options.threads.unwrap_or(num_cpus..=num_cpus);

    let config = CircuitConfig::standard_recursion_config();
    for log2_inner_size in options.size {
        // Since the `size` is most likely to be and unbounded range we make that the outer iterator.
        for threads in threads.clone() {
            rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .context("Failed to build thread pool.")?
                .install(|| {
                    info!(
                        "Using {} compute threads on {} cores",
                        rayon::current_num_threads(),
                        num_cpus
                    );
                    // Run the benchmark
                    benchmark(&config, log2_inner_size)
                })?;
        }
    }

    Ok(())
}

fn parse_hex_u64(src: &str) -> Result<u64, ParseIntError> {
    let src = src.strip_prefix("0x").unwrap_or(src);
    u64::from_str_radix(src, 16)
}

fn parse_range_usize(src: &str) -> Result<RangeInclusive<usize>, ParseIntError> {
    if let Some((left, right)) = src.split_once("..=") {
        Ok(RangeInclusive::new(
            usize::from_str(left)?,
            usize::from_str(right)?,
        ))
    } else if let Some((left, right)) = src.split_once("..") {
        Ok(RangeInclusive::new(
            usize::from_str(left)?,
            if right.is_empty() {
                usize::MAX
            } else {
                usize::from_str(right)?.saturating_sub(1)
            },
        ))
    } else {
        let value = usize::from_str(src)?;
        Ok(RangeInclusive::new(value, value))
    }
}
