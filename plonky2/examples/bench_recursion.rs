// HACK: Ideally this would live in `benches/`, but `cargo bench` doesn't allow
// custom CLI argument parsing (even with harness disabled). We could also have
// put it in `src/bin/`, but then we wouldn't have access to
// `[dev-dependencies]`.

use core::num::ParseIntError;
use core::ops::RangeInclusive;
use core::str::FromStr;

use anyhow::{anyhow, Context as _, Result};
use log::{info, Level, LevelFilter};
use maybe_rayon::rayon;
use plonky2::gates::noop::NoopGate;
use plonky2::hash::hash_types::{RichField, HashOutTarget, MerkleCapTarget, HashOut};
use plonky2::hash::merkle_proofs::{MerkleProofTarget, MerkleProof};
use plonky2::hash::merkle_tree::MerkleTree;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartialWitness, Witness};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{
    CircuitConfig, CommonCircuitData, VerifierCircuitTarget, VerifierOnlyCircuitData,
};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig, Hasher};
use plonky2::plonk::proof::{CompressedProofWithPublicInputs, ProofWithPublicInputs};
use plonky2::plonk::prover::prove;
use plonky2::util::timing::TimingTree;
use plonky2_field::extension::Extendable;
use plonky2_field::goldilocks_field::GoldilocksField;
use rand::rngs::OsRng;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use structopt::StructOpt;
use plonky2::field::types::{Sample,Field};

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
    merkle_root_value: HashOut<F> 
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
        builder.connect(nullifier_target.elements[i], should_be_nullifier_target.elements[i]);
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

    let inner_data = VerifierCircuitTarget {
        constants_sigmas_cap: builder.add_virtual_cap(inner_cd1.config.fri_config.cap_height),
        circuit_digest: builder.add_virtual_hash(),
    };

    builder.verify_proof::<InnerC>(&pt1, &inner_data, inner_cd1);
    builder.verify_proof::<InnerC>(&pt2, &inner_data, inner_cd2);
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
    pw.set_verifier_data_target(&inner_data, inner_vd1);
    pw.set_proof_with_pis_target(&pt2, inner_proof2);
    pw.set_verifier_data_target(&inner_data, inner_vd2);

    let mut timing = TimingTree::new("prove", Level::Debug);
    let proof = prove(&data.prover_only, &data.common, pw, &mut timing)?;
    timing.print();

    data.verify(proof.clone())?;

    Ok((proof, data.verifier_only, data.common))
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

    let private_keys: Vec<[F;4]> = (0..n).map(|_| F::rand_array()).collect();
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
    let inner1 = semaphore_proof(config, private_keys[1], topic1, 1, merkle_proof1, merkle_root_value)?;//dummy_proof::<F, C, D>(config, log2_inner_size)?;
    let (_, _, cd1) = &inner1;
    info!(
        "Initial proof 1 degree {} = 2^{}",
        cd1.degree(),
        cd1.degree_bits()
    );

    let merkle_proof2 = merkle_tree.prove(2);
    let topic2: [GoldilocksField; 4] = F::rand_array();
    let nullifier2 = PoseidonHash::hash_no_pad(&[private_keys[2], topic2].concat()).elements;
    let inner2 = semaphore_proof(config, private_keys[2], topic1, 2, merkle_proof2, merkle_root_value)?;//dummy_proof::<F, C, D>(config, log2_inner_size)?;
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
    let inner3 = semaphore_proof(config, private_keys[3], topic1, 3, merkle_proof3, merkle_root_value)?;//dummy_proof::<F, C, D>(config, log2_inner_size)?;
    let (_, _, cd3) = &inner3;
    info!(
        "Initial proof 3 degree {} = 2^{}",
        cd3.degree(),
        cd3.degree_bits()
    );

    let merkle_proof4 = merkle_tree.prove(4);
    let topic4: [GoldilocksField; 4] = F::rand_array();
    let nullifier4 = PoseidonHash::hash_no_pad(&[private_keys[4], topic1].concat()).elements;
    let inner4 = semaphore_proof(config, private_keys[4], topic4, 4, merkle_proof4, merkle_root_value)?;//dummy_proof::<F, C, D>(config, log2_inner_size)?;
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
