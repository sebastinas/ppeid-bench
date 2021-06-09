use std::collections::HashMap;

use bignat::hash::Hasher;
use rand::Rng;
use sapling_crypto::bellman::pairing::ff::PrimeField;

pub trait RngHelpers {
    /// Sample a random string with a random length
    fn random_string(&mut self, min_len: usize, max_len: usize) -> String;

    /// Sample a random birthday
    fn random_birthday(&mut self) -> String;
}

impl<T: Rng> RngHelpers for T {
    fn random_string(&mut self, min_len: usize, max_len: usize) -> String {
        let length = if min_len == max_len {
            min_len
        } else {
            self.gen_range(min_len, max_len + 1)
        };
        self.gen_ascii_chars().take(length).collect::<String>()
    }

    fn random_birthday(&mut self) -> String {
        let year = self.gen_range(1910, 2022);
        let month = self.gen_range(1, 13);
        let day = self.gen_range(1, 32);
        format!("{:04}-{:02}-{:02}", year, month, day)
    }
}

// Merkle tree implementation from https://github.com/kilic/bellman-playground written by Onur Kilic
pub struct MerkleTree<H>
where
    H: Hasher,
{
    pub hasher: H,
    pub zero: Vec<H::F>,
    pub depth: usize,
    pub nodes: HashMap<(usize, usize), H::F>,
}

impl<H> MerkleTree<H>
where
    H: Hasher,
{
    pub fn empty(hasher: H, depth: usize) -> Self {
        let mut zero: Vec<H::F> = Vec::with_capacity(depth + 1);
        zero.push(H::F::from_str("0").unwrap());
        for i in 0..depth {
            zero.push(hasher.hash(&[zero[i]; 2]));
        }
        zero.reverse();
        MerkleTree {
            hasher,
            zero,
            depth,
            nodes: HashMap::new(),
        }
    }

    fn get_node(&self, depth: usize, index: usize) -> H::F {
        *self
            .nodes
            .get(&(depth, index))
            .unwrap_or_else(|| &self.zero[depth])
    }

    fn hash_couple(&self, depth: usize, index: usize) -> H::F {
        let b = index & !1;
        self.hasher
            .hash2(self.get_node(depth, b), self.get_node(depth, b + 1))
    }

    fn recalculate_from(&mut self, leaf_index: usize) {
        let mut i = leaf_index;
        let mut depth = self.depth;
        loop {
            let h = self.hash_couple(depth, i);
            i >>= 1;
            depth -= 1;
            self.nodes.insert((depth, i), h);
            if depth == 0 {
                break;
            }
        }
        assert_eq!(depth, 0);
        assert_eq!(i, 0);
    }

    // takes the of leaf preimage
    pub fn insert(&mut self, leaf_index: usize, new: H::F) {
        let d = self.depth;
        self.nodes.insert((d, leaf_index), self.hasher.hash(&[new]));
        self.recalculate_from(leaf_index);
    }

    pub fn root(&self) -> H::F {
        self.get_node(0, 0)
    }

    pub fn witness(&mut self, leaf_index: usize) -> Vec<(H::F, bool)> {
        let mut witness = Vec::<(H::F, bool)>::with_capacity(self.depth);
        let mut i = leaf_index;
        let mut depth = self.depth;
        loop {
            i ^= 1;
            witness.push((self.get_node(depth, i), (i & 1 == 1)));
            i >>= 1;
            depth -= 1;
            if depth == 0 {
                break;
            }
        }
        assert_eq!(i, 0);
        witness
    }
}
