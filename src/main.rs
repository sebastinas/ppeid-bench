mod samecommit;
mod utils;

use bignat::hash::circuit::CircuitHasher;
use bignat::hash::hashes;
use bignat::hash::Hasher;
use sapling_crypto::bellman::pairing::bls12_381::Bls12;
use sapling_crypto::jubjub::JubjubEngine;
use serde::Serialize;
use stats::OnlineStats;
use std::io;
use structopt::StructOpt;

#[derive(StructOpt)]
#[structopt(name = "bench2", about = "Benchmarking for various SSI circuits")]
struct Arguments {
    #[structopt(long, default_value = "100")]
    rounds: usize,
    #[structopt(long)]
    attestation: bool,
    #[structopt(long)]
    showing_poseidon: bool,
    #[structopt(long)]
    showing_sha256: bool,
    #[structopt(long)]
    showing_mimc: bool,
    #[structopt(long, default_value = "1")]
    min_priv_attrs: usize,
    #[structopt(long, default_value = "4")]
    max_priv_attrs: usize,
    #[structopt(long, default_value = "5")]
    min_merkle_tree_depth: usize,
    #[structopt(long, default_value = "12")]
    max_merkle_tree_depth: usize,
    #[structopt(long, default_value = "benchmark.csv")]
    output: String,
}

#[derive(Serialize)]
struct Record<'a> {
    bench: &'a str,
    proof: u128,
    verify: u128,
    merkle_tree_depth: Option<usize>,
    num_revocation_ids: Option<usize>,
    priv_attrs: Option<usize>,
}

fn process_showing_results<F: io::Write>(
    name: &str,
    merkle_tree_depth: usize,
    num_revocation_ids: usize,
    priv_attrs: usize,
    proof_times: Vec<u128>,
    verify_times: Vec<u128>,
    writer: &mut csv::Writer<F>,
) -> Result<(OnlineStats, OnlineStats), csv::Error> {
    let mut proof_stats = OnlineStats::new();
    let mut verify_stats = OnlineStats::new();

    for (proof, verify) in proof_times.iter().zip(verify_times.iter()) {
        writer.serialize(Record {
            bench: name,
            proof: *proof,
            verify: *verify,
            merkle_tree_depth: Some(merkle_tree_depth),
            num_revocation_ids: Some(num_revocation_ids),
            priv_attrs: Some(priv_attrs),
        })?;

        proof_stats.add(*proof);
        verify_stats.add(*verify);
    }

    writer.flush()?;
    Ok((proof_stats, verify_stats))
}

fn print_stats(name: &str, stats: OnlineStats) {
    println!(
        "{}: {:.2} µs (+/- {:.2})\t{:.2} ms (+/- {:.2})",
        name,
        stats.mean(),
        stats.stddev(),
        (stats.mean()) / 1000f64,
        (stats.stddev()) / 1000f64
    );
}

fn run_showing<Writer: io::Write, E: JubjubEngine, H1, H2>(
    hash_name: &str,
    args: &Arguments,
    writer: &mut csv::Writer<Writer>,
    hasher1: H1,
    hasher2: H2,
) -> Result<(), io::Error>
where
    H1: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    H2: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
    for merkle_tree_depth in args.min_merkle_tree_depth..(args.max_merkle_tree_depth + 1) {
        let mut showing =
            samecommit::Showing::new(merkle_tree_depth, hasher1.clone(), hasher2.clone());

        for priv_attrs in args.min_priv_attrs..(args.max_priv_attrs + 1) {
            println!(
                "Showing ({}): {} runs\n# Private Attributes: {}\t# MT depth: {}",
                hash_name, args.rounds, priv_attrs, merkle_tree_depth
            );
            let (num_revocation_ids, proof_times, verify_times) =
                showing.run(priv_attrs, args.rounds);

            let (proof_stats, verify_stats) = process_showing_results(
                format!("showing ({})", hash_name).as_str(),
                merkle_tree_depth,
                num_revocation_ids,
                priv_attrs,
                proof_times,
                verify_times,
                writer,
            )?;
            print_stats("Proof", proof_stats);
            print_stats("Verify", verify_stats);
        }
    }
    println!();
    Ok(())
}

fn main() {
    let args = Arguments::from_args();
    if args.max_priv_attrs > 4 {
        panic!("Max 4 priv attrs allowed.")
    }
    if args.min_priv_attrs > args.max_priv_attrs {
        panic!("Number of min priv attrs needs to be less or equal to max.");
    }
    if args.min_merkle_tree_depth > args.max_merkle_tree_depth {
        panic!("Min depth of Merkle tree is larger than max depth.");
    }

    let mut wtr = csv::Writer::from_path(args.output.clone()).expect("Failed to open output file.");
    if args.attestation {
        let (proof_times, verify_times) = samecommit::Attestation {
            hasher1: hashes::Sha256::<Bls12>::default(),
            hasher2: hashes::Pedersen::<Bls12>::default(),
        }
        .run(args.rounds);
        let mut proof_stats = OnlineStats::new();
        let mut verify_stats = OnlineStats::new();

        for (proof, verify) in proof_times.iter().zip(verify_times.iter()) {
            wtr.serialize(Record {
                bench: "attestation",
                proof: *proof,
                verify: *verify,
                merkle_tree_depth: None,
                num_revocation_ids: None,
                priv_attrs: None,
            })
            .unwrap();

            proof_stats.add(*proof);
            verify_stats.add(*verify);
        }

        println!("Attestation: {} runs", args.rounds);
        print_stats("Proving", proof_stats);
        print_stats("Verification", verify_stats);
        println!();
    }

    if args.showing_poseidon {
        run_showing(
            "Poseidon",
            &args,
            &mut wtr,
            hashes::Poseidon::<Bls12>::default(),
            hashes::Pedersen::<Bls12>::default(),
        )
        .expect("Failed to write results to CSV file.");
    }
    if args.showing_sha256 {
        run_showing(
            "SHA256",
            &args,
            &mut wtr,
            hashes::Sha256::<Bls12>::default(),
            hashes::Pedersen::<Bls12>::default(),
        )
        .expect("Failed to write results to CSV file.");
    }
    if args.showing_mimc {
        run_showing(
            "MiMC",
            &args,
            &mut wtr,
            hashes::Mimc::<Bls12>::default(),
            hashes::Pedersen::<Bls12>::default(),
        )
        .expect("Failed to write results to CSV file.");
    }
}
