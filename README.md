# Benchmarks for "Privacy-Preserving eID Derivation to Self-Sovereign Identity Systems with Offline Revocation"

This repository contains all benchmarks that were performed for our paper:

* Andreas Abraham, Karl Koch, Stefan More, Sebastian Ramacher, Miha Stopar: *Privacy-Preserving eID Derivation to Self-Sovereign Identity Systems with Offline Revocation*. [IEEE TrustCom 2021](https://trustcom2021.sau.edu.cn/)

## Building

Note that the repository does not include an `src/assertion.xml` file as it typically contains personal information. You need to create the file with content yourself before building.

```shell
$ cargo build --release
```

## Benchmarks

### Attestation

```shell
$ ./target/release/ppeid-bench --attestation --output benchmark-attestation.csv
```

### Showing

With Poseidon:
```shell
$ ./target/release/ppeid-bench --showing-poseidon --output benchmark-showing.csv --min-priv-attrs 0 --max-priv-attrs 4 --max-merkle-tree-depth 20
```

With MiMC
```shell
$ ./target/release/ppeid-bench --showing-mimc --output benchmark-mimc.csv --min-priv-attrs 0 --max-priv-attrs 4 --max-merkle-tree-depth 20
```

With SHA256:
```shell
$ ./target/release/ppeid-bench --showing-sha256 --output benchmark-sha256.csv --min-priv-attrs 0 --max-priv-attrs 4
```