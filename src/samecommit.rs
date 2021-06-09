use std::include_str;
use std::time::Instant;

use bignat::hash::circuit::CircuitHasher;
use bignat::hash::Hasher;
use rand::{SeedableRng, XorShiftRng};
use sapling_crypto::bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use sapling_crypto::bellman::pairing::ff::PrimeField;
use sapling_crypto::bellman::{Circuit, ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::num::AllocatedNum;
use sapling_crypto::circuit::{boolean, multipack, Assignment};
use sapling_crypto::jubjub::JubjubEngine;

use super::utils::{MerkleTree, RngHelpers};

/// Convert a sequence of bytes (with a maximal length) to elements in the field
fn bytes_to_inputs<E: JubjubEngine>(inputs: &[u8], max_length: usize) -> Vec<E::Fr> {
    assert!(inputs.len() <= max_length);

    let mut image = multipack::bytes_to_bits_le(&inputs);
    // pad to max_length
    while image.len() < 8 * max_length {
        image.push(false)
    }
    assert_eq!(image.len(), 8 * max_length);

    multipack::compute_multipacking::<E>(&image)
}

/// Convert a sequence of (optional) Strings and sizes to allocated inputs
fn convert<
    'a,
    E: JubjubEngine,
    CS: ConstraintSystem<E>,
    Iter: Iterator<Item = (&'a &'a Option<String>, &'a usize)>,
>(
    mut cs: CS,
    iter: Iter,
) -> Vec<AllocatedNum<E>> {
    iter.flat_map(|(str_input, max_length)| -> Vec<Option<E::Fr>> {
        match str_input {
            None => {
                vec![
                    None;
                    (*max_length * 8 + E::Fr::CAPACITY as usize - 1) / E::Fr::CAPACITY as usize
                ]
            }
            Some(value) => bytes_to_inputs::<E>(value.as_bytes(), *max_length as usize)
                .iter()
                .map(|f| Some(*f))
                .collect(),
        }
    })
    .enumerate()
    .flat_map(|(index, value)| {
        // allocate input
        AllocatedNum::alloc(cs.namespace(|| format!("input {}", index)), || {
            Ok(*value.get()?)
        })
    })
    .collect()
}

// 4 Attributes (+ Revocation)
// Given Name + Family Name + Identifier + Date of Birth
const MIN_GIVEN_NAME: usize = 3;
const MAX_GIVEN_NAME: usize = 16;
const MIN_FAMILY_NAME: usize = 3;
const MAX_FAMILY_NAME: usize = 16;
const IDENTIFIER_LENGTH: usize = 31;
const REVOCATION_ID_LENGTH: usize = 31;
const XML_TEXT: &str = include_str!("assertion.xml");
const ATTR_LENGTH: [usize; 5] = [
    MAX_GIVEN_NAME,
    MAX_FAMILY_NAME,
    IDENTIFIER_LENGTH,
    10,
    REVOCATION_ID_LENGTH,
];

struct AttestationCircuit<E, H1, H2>
where
    E: JubjubEngine,
    H1: Hasher,
    H2: Hasher,
{
    given_name: Option<String>,
    family_name: Option<String>,
    identifier: Option<String>,
    date_of_birth: Option<String>,
    revocation_id: Option<String>,
    hash1: Option<E::Fr>,
    hash2: Option<E::Fr>,
    /// SHA256 as in the IdP's signature scheme
    hasher1: H1,
    /// Pedersen commitment
    hasher2: H2,
}

impl<E, H1, H2> AttestationCircuit<E, H1, H2>
where
    E: JubjubEngine,
    H1: Hasher,
    H2: Hasher,
{
    fn empty(hasher1: H1, hasher2: H2) -> Self {
        Self {
            given_name: None,
            family_name: None,
            identifier: None,
            date_of_birth: None,
            revocation_id: None,
            hash1: None,
            hash2: None,
            hasher1,
            hasher2,
        }
    }
}

impl<E, H1, H2> Circuit<E> for AttestationCircuit<E, H1, H2>
where
    E: JubjubEngine,
    H1: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    H2: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        // convert the private inputs to AllocatedNum instances
        let input1: Vec<AllocatedNum<E>> = convert(
            cs.namespace(|| "private inputs"),
            [
                &self.given_name,
                &self.family_name,
                &self.identifier,
                &self.date_of_birth,
            ]
            .iter()
            .zip(ATTR_LENGTH.iter().take(4)),
        );
        let mut input2 = input1.clone();
        // convert the public inputs to AllocatedNum instances and mark them as public inputs
        let mut xml_inputs = convert(
            cs.namespace(|| "XML"),
            [&Some(String::from(XML_TEXT))]
                .iter()
                .zip([XML_TEXT.len()].iter()),
        );
        xml_inputs.iter().enumerate().for_each(|(index, input)| {
            input
                .inputize(cs.namespace(|| format!("XML inputs {}", index)))
                .unwrap();
        });

        let public_inputs1 = convert(
            cs.namespace(|| "public inputs"),
            [&self.revocation_id]
                .iter()
                .zip([REVOCATION_ID_LENGTH].iter()),
        );
        public_inputs1
            .iter()
            .enumerate()
            .for_each(|(index, input)| {
                input
                    .inputize(cs.namespace(|| format!("public input {}", index)))
                    .unwrap();
            });
        // merge private and public inputs
        xml_inputs.extend(input1);
        let mut input1 = xml_inputs;
        input1.extend(public_inputs1.clone());
        input2.extend(public_inputs1);

        // hash with hasher1
        let hash1 = AllocatedNum::alloc(cs.namespace(|| "hash1 output"), || {
            let value = self.hash1;
            Ok(*value.get()?)
        })?;
        hash1.inputize(cs.namespace(|| "hash1 input"))?;
        let calculated1 = self
            .hasher1
            .allocate_hash(cs.namespace(|| "inputs 1"), &input1)?;
        cs.enforce(
            || "add constraint between input and pedersen hash output",
            |lc| lc + calculated1.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + hash1.get_variable(),
        );

        // hash with hasher2
        let hash2 = AllocatedNum::alloc(cs.namespace(|| "hash2 output"), || {
            let value = self.hash2;
            Ok(*value.get()?)
        })?;
        hash2.inputize(cs.namespace(|| "hash2 input"))?;
        let calculated2 = self
            .hasher2
            .allocate_hash(cs.namespace(|| "inputs 2"), &input2)?;
        cs.enforce(
            || "add constraint between input and pedersen hash output",
            |lc| lc + calculated2.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + hash2.get_variable(),
        );
        Ok(())
    }
}

pub struct Attestation<E, H1, H2>
where
    E: JubjubEngine,
    H1: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    H2: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
    pub hasher1: H1,
    pub hasher2: H2,
}

impl<E, H1, H2> Attestation<E, H1, H2>
where
    E: JubjubEngine,
    H1: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    H2: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
    pub fn run(&self, rounds: usize) -> (Vec<u128>, Vec<u128>) {
        let mut rng = XorShiftRng::from_seed([0x3dbe6258, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        // generate SNARK parameters
        let circuit_parameters = {
            let empty_circuit =
                AttestationCircuit::empty(self.hasher1.clone(), self.hasher2.clone());
            generate_random_parameters(empty_circuit, &mut rng).unwrap()
        };
        let verifing_key = prepare_verifying_key(&circuit_parameters.vk);

        let mut proof_stats = Vec::with_capacity(rounds);
        let mut verify_stats = Vec::with_capacity(rounds);

        for _ in 0..rounds {
            // create input specific instance
            let (public_inputs, circuit) = {
                let given_name = rng.random_string(MIN_GIVEN_NAME, MAX_GIVEN_NAME);
                let family_name = rng.random_string(MIN_FAMILY_NAME, MAX_FAMILY_NAME);
                let identifier = rng.random_string(IDENTIFIER_LENGTH, IDENTIFIER_LENGTH);
                let date_of_birth = rng.random_birthday();
                let revocation_id = rng.random_string(REVOCATION_ID_LENGTH, REVOCATION_ID_LENGTH);

                let input1: Vec<E::Fr> = [
                    &String::from(XML_TEXT),
                    &given_name,
                    &family_name,
                    &identifier,
                    &date_of_birth,
                    &revocation_id,
                ]
                .iter()
                .zip([XML_TEXT.len()].iter().chain(ATTR_LENGTH.iter()))
                .map(|(value, max_length)| bytes_to_inputs::<E>(value.as_bytes(), *max_length))
                .flatten()
                .collect();

                let input2: Vec<E::Fr> = [
                    &given_name,
                    &family_name,
                    &identifier,
                    &date_of_birth,
                    &revocation_id,
                ]
                .iter()
                .zip(ATTR_LENGTH.iter())
                .map(|(value, max_length)| bytes_to_inputs::<E>(value.as_bytes(), *max_length))
                .flatten()
                .collect();

                let output1 = self.hasher1.hash(&input1);
                let output2 = self.hasher2.hash(&input2);
                let instance = AttestationCircuit {
                    given_name: Some(given_name),
                    family_name: Some(family_name),
                    identifier: Some(identifier),
                    date_of_birth: Some(date_of_birth),
                    revocation_id: Some(revocation_id.clone()),
                    hash1: Some(output1),
                    hash2: Some(output2),
                    hasher1: self.hasher1.clone(),
                    hasher2: self.hasher2.clone(),
                };

                let mut public_inputs = bytes_to_inputs::<E>(XML_TEXT.as_bytes(), XML_TEXT.len());
                public_inputs.extend(bytes_to_inputs::<E>(
                    revocation_id.as_bytes(),
                    REVOCATION_ID_LENGTH,
                ));
                public_inputs.extend(vec![output1, output2]);
                (public_inputs, instance)
            };

            // create the actual proof
            let start_proof = Instant::now();
            let proof = create_random_proof(circuit, &circuit_parameters, &mut rng).unwrap();
            let proof_duration = Instant::now().duration_since(start_proof);
            proof_stats.push(proof_duration.as_micros());

            // verify the proof
            let start_verify = Instant::now();
            let is_valid = verify_proof(&verifing_key, &proof, &public_inputs).unwrap();
            let verify_duration = Instant::now().duration_since(start_verify);
            verify_stats.push(verify_duration.as_micros());

            assert!(is_valid);
        }

        (proof_stats, verify_stats)
    }
}

// Showing starts here
// Parts of the Merkle tree showing have been adapted from
// https://github.com/kilic/bellman-playground by Onur Kilic

trait GenericMerkleHasher<E: JubjubEngine>: Clone {
    fn hash_to_leaf<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        raw: &[AllocatedNum<E>],
    ) -> Result<AllocatedNum<E>, SynthesisError>;

    fn hash_couple<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
        xl: &AllocatedNum<E>,
        xr: &AllocatedNum<E>,
    ) -> Result<AllocatedNum<E>, SynthesisError>;
}

#[derive(Clone)]
struct MerkleHasher<E, H>
where
    E: JubjubEngine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr> + Clone,
{
    hasher: H,
}

impl<E, H> GenericMerkleHasher<E> for MerkleHasher<E, H>
where
    E: JubjubEngine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
    fn hash_to_leaf<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        raw: &[AllocatedNum<E>],
    ) -> Result<AllocatedNum<E>, SynthesisError> {
        self.hasher
            .allocate_hash(cs.namespace(|| "hash_to_leaf"), raw)
    }
    fn hash_couple<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        xl: &AllocatedNum<E>,
        xr: &AllocatedNum<E>,
    ) -> Result<AllocatedNum<E>, SynthesisError> {
        self.hasher
            .allocate_hash2(cs.namespace(|| "hash_to_leaf"), xl, xr)
    }
}

struct MembershipCircuit<E, H>
where
    E: JubjubEngine,
    H: GenericMerkleHasher<E>,
{
    hasher: H,
    leaf: AllocatedNum<E>,
    root: AllocatedNum<E>,
    witness: Vec<(AllocatedNum<E>, boolean::Boolean)>,
}

impl<E, H> MembershipCircuit<E, H>
where
    E: JubjubEngine,
    H: GenericMerkleHasher<E>,
{
    pub fn alloc<CS: ConstraintSystem<E>>(
        mut cs: CS,
        hasher: H,
        root: Option<E::Fr>,
        member: AllocatedNum<E>,
        witness: Vec<Option<(E::Fr, bool)>>,
    ) -> Result<Self, SynthesisError> {
        let root = AllocatedNum::alloc(cs.namespace(|| "root"), || Ok(*root.get()?))?;
        root.inputize(cs.namespace(|| "root public input"))?;

        let mut allocated_witness: Vec<(AllocatedNum<E>, boolean::Boolean)> =
            Vec::with_capacity(witness.len());
        for (i, e) in witness.into_iter().enumerate() {
            let cs = &mut cs.namespace(|| format!("witness {}", i));
            let position = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                cs.namespace(|| "position bit"),
                e.map(|e| e.1),
            )?);
            let path_element =
                AllocatedNum::alloc(cs.namespace(|| "path element"), || Ok(e.get()?.0))?;
            allocated_witness.push((path_element, position));
        }
        let leaf = hasher.hash_to_leaf(cs.namespace(|| "hash to leaf"), &[member])?;
        Ok(Self {
            hasher,
            leaf,
            root,
            witness: allocated_witness,
        })
    }

    pub fn check_inclusion<CS: ConstraintSystem<E>>(
        &mut self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        // accumulator up to the root
        let mut acc = self.leaf.clone();
        // ascend the tree
        // taken from sapling circuit
        // https://github.com/zcash-hackworks/sapling-crypto/blob/49017b4e055ba4322dad1f03fe7d80dc0ed449cc/src/circuit/sapling/mod.rs#L353
        for (i, e) in self.witness.iter().enumerate() {
            let cs = &mut cs.namespace(|| format!("merkle tree hash {}", i));

            let (xr, xl) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of preimage"),
                &acc,
                &e.0,
                &e.1,
            )?;
            acc = self
                .hasher
                .hash_couple(cs.namespace(|| "hash couple"), &xl, &xr)?;
        }

        cs.enforce(
            || "enforce membership",
            |lc| lc + acc.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + self.root.get_variable(),
        );
        Ok(())
    }
}

struct ShowingCircuit<E, H1, H2>
where
    E: JubjubEngine,
    H1: Hasher,
    H2: Hasher,
{
    given_name: Option<String>,
    family_name: Option<String>,
    identifier: Option<String>,
    date_of_birth: Option<String>,
    revocation_id: Option<String>,
    priv_attrs: usize,
    merkle_tree_root: Option<E::Fr>,
    merkle_tree_witnesses: Vec<Option<(E::Fr, bool)>>,
    hash2: Option<E::Fr>,
    /// hasher used for Merkle tree
    hasher1: H1,
    /// hasher for Pedersen commitment
    hasher2: H2,
}

impl<E, H1, H2> ShowingCircuit<E, H1, H2>
where
    E: JubjubEngine,
    H1: Hasher,
    H2: Hasher,
{
    fn empty(hasher1: H1, hasher2: H2, priv_attrs: usize, merkle_tree_depth: usize) -> Self {
        Self {
            given_name: None,
            family_name: None,
            identifier: None,
            date_of_birth: None,
            revocation_id: None,
            priv_attrs,
            merkle_tree_witnesses: vec![None; merkle_tree_depth],
            merkle_tree_root: None,
            hash2: None,
            hasher1,
            hasher2,
        }
    }
}

impl<E, H1, H2> Circuit<E> for ShowingCircuit<E, H1, H2>
where
    E: JubjubEngine,
    H1: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    H2: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let all_attributes = [
            &self.given_name,
            &self.family_name,
            &self.identifier,
            &self.date_of_birth,
        ];
        // convert the private inputs to AllocatedNum instances
        let mut input2 = convert(
            cs.namespace(|| "private inputs"),
            all_attributes
                .iter()
                .zip(ATTR_LENGTH.iter())
                .take(self.priv_attrs),
        );

        // convert the public inputs to AllocatedNum instances and mark them as public inputs
        // if priv_attrs == 4 --> we do not have any public attributes
        if self.priv_attrs <= 3 {
            let pub_attr_input = convert(
                cs.namespace(|| "public attributes"),
                all_attributes
                    .iter()
                    .zip(ATTR_LENGTH.iter())
                    .skip(self.priv_attrs),
            );
            pub_attr_input
                .iter()
                .enumerate()
                .for_each(|(index, input)| {
                    input
                        .inputize(cs.namespace(|| format!("public inputs {}", index)))
                        .unwrap();
                });
            input2.extend(pub_attr_input);
        }

        let revocation_id = convert(
            cs.namespace(|| "public inputs"),
            [&self.revocation_id]
                .iter()
                .zip([REVOCATION_ID_LENGTH].iter()),
        );
        assert_eq!(revocation_id.len(), 1);

        input2.extend(revocation_id.clone());

        // hash with hasher2
        let hash2 = AllocatedNum::alloc(cs.namespace(|| "hash2 output"), || {
            let value = self.hash2;
            Ok(*value.get()?)
        })?;
        hash2.inputize(cs.namespace(|| "hash2 input"))?;
        let calculated2 = self
            .hasher2
            .allocate_hash(cs.namespace(|| "inputs 2"), &input2)?;
        cs.enforce(
            || "add constraint between input and pedersen hash output",
            |lc| lc + calculated2.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + hash2.get_variable(),
        );

        let mut membership_circuit = MembershipCircuit::alloc(
            cs.namespace(|| "alloc membership circuit"),
            MerkleHasher {
                hasher: self.hasher1.clone(),
            },
            self.merkle_tree_root,
            revocation_id[0].clone(),
            self.merkle_tree_witnesses,
        )?;
        membership_circuit.check_inclusion(cs.namespace(|| "check inclusion"))?;
        Ok(())
    }
}

pub struct Showing<E, H1, H2>
where
    E: JubjubEngine,
    H1: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    H2: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
    hasher1: H1,
    hasher2: H2,
    merkle_tree: MerkleTree<H1>,
    revocation_ids: Vec<String>,
}

impl<E, H1, H2> Showing<E, H1, H2>
where
    E: JubjubEngine,
    H1: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    H2: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
    pub fn new(merkle_tree_depth: usize, hasher1: H1, hasher2: H2) -> Self {
        let mut rng = XorShiftRng::from_seed([0xe5bc0654, 0x3dbe6258, 0x8d313d76, 0x3237db17]);

        // generate random revocation IDs
        let num_revocation_ids = 2usize.pow(merkle_tree_depth as u32);
        let mut merkle_tree = MerkleTree::empty(hasher1.clone(), merkle_tree_depth);
        let mut revocation_ids: Vec<String> = Vec::with_capacity(num_revocation_ids);

        for index in 0..num_revocation_ids {
            let revocation_id = rng.random_string(REVOCATION_ID_LENGTH, REVOCATION_ID_LENGTH);
            // add revocation ID to the Merkle tree
            let converted = bytes_to_inputs::<E>(revocation_id.as_bytes(), REVOCATION_ID_LENGTH);
            assert_eq!(converted.len(), 1);
            merkle_tree.insert(index, converted[0]);
            revocation_ids.push(revocation_id);
        }

        Self {
            hasher1,
            hasher2,
            merkle_tree,
            revocation_ids,
        }
    }

    pub fn run(&mut self, priv_attrs: usize, rounds: usize) -> (usize, Vec<u128>, Vec<u128>) {
        assert!(priv_attrs <= 4); // max. 4 private attributes

        let mut rng = XorShiftRng::from_seed([0x3dbe6258, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        // generate SNARK parameters
        let circuit_parameters = {
            let empty_circuit = ShowingCircuit::empty(
                self.hasher1.clone(),
                self.hasher2.clone(),
                priv_attrs,
                self.merkle_tree.depth,
            );
            generate_random_parameters(empty_circuit, &mut rng).unwrap()
        };
        let verifing_key = prepare_verifying_key(&circuit_parameters.vk);

        let mut proof_stats = Vec::with_capacity(rounds);
        let mut verify_stats = Vec::with_capacity(rounds);

        for (index, revocation_id) in self.revocation_ids.iter().enumerate().cycle().take(rounds) {
            // create input specific instance
            let (public_inputs, circuit) = {
                let given_name = rng.random_string(MIN_GIVEN_NAME, MAX_GIVEN_NAME);
                let family_name = rng.random_string(MIN_FAMILY_NAME, MAX_FAMILY_NAME);
                let identifier = rng.random_string(IDENTIFIER_LENGTH, IDENTIFIER_LENGTH);
                let date_of_birth = rng.random_birthday();

                let all_attributes = [
                    &given_name,
                    &family_name,
                    &identifier,
                    &date_of_birth,
                    &revocation_id,
                ];
                let input2: Vec<E::Fr> = all_attributes
                    .iter()
                    .zip(ATTR_LENGTH.iter())
                    .map(|(value, max_length)| bytes_to_inputs::<E>(value.as_bytes(), *max_length))
                    .flatten()
                    .collect();

                let output2 = self.hasher2.hash(&input2);
                let instance = ShowingCircuit {
                    given_name: Some(given_name),
                    family_name: Some(family_name),
                    identifier: Some(identifier),
                    date_of_birth: Some(date_of_birth),
                    revocation_id: Some(revocation_id.clone()),
                    priv_attrs: priv_attrs,
                    merkle_tree_root: Some(self.merkle_tree.root()),
                    merkle_tree_witnesses: self
                        .merkle_tree
                        .witness(index)
                        .into_iter()
                        .map(Some)
                        .collect(),
                    hash2: Some(output2),
                    hasher1: self.hasher1.clone(),
                    hasher2: self.hasher2.clone(),
                };

                let mut public_inputs: Vec<E::Fr> = vec![];
                public_inputs.extend(input2.iter().skip(priv_attrs).take(4usize - priv_attrs));
                public_inputs.push(output2);
                public_inputs.push(self.merkle_tree.root());
                (public_inputs, instance)
            };

            // create the actual proof
            let start_proof = Instant::now();
            let proof = create_random_proof(circuit, &circuit_parameters, &mut rng).unwrap();
            let proof_duration = Instant::now().duration_since(start_proof);
            proof_stats.push(proof_duration.as_micros());

            // verify the proof
            let start_verify = Instant::now();
            let is_valid = verify_proof(&verifing_key, &proof, &public_inputs).unwrap();
            let verify_duration = Instant::now().duration_since(start_verify);
            verify_stats.push(verify_duration.as_micros());

            assert!(is_valid);
        }

        (self.revocation_ids.len(), proof_stats, verify_stats)
    }
}
