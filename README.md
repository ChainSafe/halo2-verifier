# Halo2 Verifier

A `no-std` Rust library for verifying Halo2 proofs. Most of the code is ported from the audided `halo2_proofs` crate, `v0.3.0`.

## Crates

- `halo2_verifier`: verify Halo2 proofs. Exposes `VerifyingKey`, `ParansKZG` structs, and `verify_proof` function.
- `serialize`: tools to convert between `halo2_proofs` types and `no-std` types.

## Features

- Verification of Halo2 proofs.
- Generic circuit proof serialization without knowledge of a circuit structure.
- Space efficient serialization of `VerifyingKey`, `ParansKZG` types. Uses multilinear polynomial for expressions instead of Rust's recursive enum types.

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
halo2_verifier = "0.1.0"
```
