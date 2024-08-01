# Rust Verifier

A formal verifier for (a subset of) Rust programs using Constrained Horn Clauses. Uses prophecy variables to simplify the clauses for verifying pointers/references. Please read more in my master's thesis. <!-- TODO: add link -->

## Prerequisites

- [Rust](https://www.rust-lang.org/tools/install)
- [Z3](https://github.com/Z3Prover/z3/releases)
- Python 3 (tested with version 3.10.12)

## How to

Use the helper script to run the verifier on a Rust file:

```sh
python3 verify.py examples/test1.rs
```

Use the helper script to verify all files in the `examples` directory:

```sh
python3 verify.py
```

Run verifier on `examples/test1.rs`:

```sh
cargo run examples/test1.rs
```

Run an example file (not analyze but execute):

```sh
cargo run --example test1
```
