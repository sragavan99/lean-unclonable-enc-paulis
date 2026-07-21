# lean-unclonable-enc-paulis

`lean-unclonable-enc-paulis` is a Lean 4 formalization of information-theoretic uncloneable-bit
encryption. It defines an operational interface for finite-dimensional quantum
bit-encryption schemes and cloning attacks, then gives machine-checked security
proofs for finite-key Pauli encryption and Haar-random conjugate-subspace
encryption.

The formalization includes:

- key distributions, encryption and decryption families, and perfect
  correctness;
- key-independent pirate channels followed by key-dependent local
  measurements;
- the average probability that two receivers both recover the encrypted bit;
- negligible-error and polynomial-ciphertext-dimension security definitions;
- a finite Pauli construction with exact additive security error
  `1/2 * sqrt (2^(n+1) / (4^(n+1) - 1))`;
- a proof that the Pauli construction witnesses uncloneable-bit existence; and
- a Pauli-to-Haar reduction establishing the same bound for suitable closed
  unitary subgroups, including the full unitary group.

## Lean version

The project uses **Lean 4.30.0**, selected by [`lean-toolchain`](lean-toolchain):

```text
leanprover/lean4:v4.30.0
```

The recommended way to install and manage Lean is
[`elan`](https://github.com/leanprover/elan). Elan will select the repository's
pinned toolchain automatically.

## Build

Clone the repository and run the default Lake target:

```sh
lake build
```

`lake build` downloads the locked dependencies when necessary and checks the
public `UE` library, the Pauli construction and proof, and the Haar construction
and proof. This repository is a proof library, not a command-line executable;
building it is the primary way to run and verify it.

To check only the public API smoke test, run:

```sh
lake env lean UE/SmokeTest.lean
```

## Repository layout

| Path | Purpose |
| --- | --- |
| [`UE/`](UE) | Shared public definitions and security statements. It defines encryption families, cloning attacks, cloning success, negligible error, and secure constructions. |
| [`UE/Examples/`](UE/Examples) | Small examples showing how to instantiate the public interface. The current example is intentionally insecure and is included only as an interface demonstration. |
| [`PauliConstructionAndProof/`](PauliConstructionAndProof) | The finite-key Pauli construction and its complete security proof, including Pauli algebra, the reflection-game reduction, matrix and norm bounds, asymptotics, and final theorem assembly. |
| [`HaarConstructionAndProof/`](HaarConstructionAndProof) | Clifford transitivity, normalized Haar measure, the continuous-key conjugate-subspace construction, and the reduction from Pauli security to Haar security. |
| [`UE.lean`](UE.lean) | Top-level public module importing the shared API, examples, smoke test, and the Pauli and Haar endpoints. |
| [`lakefile.toml`](lakefile.toml) | Lake package configuration and library targets. |
| [`lake-manifest.json`](lake-manifest.json) | Reproducible lockfile containing the complete resolved dependency graph. |

## Dependencies

The only direct Lake dependency is
[`Lean-QIT`](https://github.com/QuAIR/Lean-QIT), pinned to commit
`d95a4cb78334`. It provides the finite-dimensional quantum-information
infrastructure used throughout the project.

The complete dependency graph locked in `lake-manifest.json` is:

| Package | Relationship | Locked ref |
| --- | --- | --- |
| [`QIT`](https://github.com/QuAIR/Lean-QIT) | Direct | `d95a4cb78334` |
| [`mathlib`](https://github.com/leanprover-community/mathlib4) | Transitive | `v4.30.0` (`c5ea00351c28`) |
| [`plausible`](https://github.com/leanprover-community/plausible) | Transitive | `main` (`a456461b368b`) |
| [`LeanSearchClient`](https://github.com/leanprover-community/LeanSearchClient) | Transitive | `main` (`c5d5b8fe6e51`) |
| [`importGraph`](https://github.com/leanprover-community/import-graph) | Transitive | `main` (`515cf9d0c00e`) |
| [`proofwidgets`](https://github.com/leanprover-community/ProofWidgets4) | Transitive | `v0.0.99` (`a84b3e2475d5`) |
| [`aesop`](https://github.com/leanprover-community/aesop) | Transitive | `v4.30.0` (`558915ae105b`) |
| [`Qq`](https://github.com/leanprover-community/quote4) | Transitive | `v4.30.0` (`a6e6c34c4ef1`) |
| [`batteries`](https://github.com/leanprover-community/batteries) | Transitive | `main` (`32dc18cde368`) |
| [`Cli`](https://github.com/leanprover/lean4-cli) | Transitive | `v4.30.0` (`6b907cf12b2e`) |

The manifest records the full commit hashes; no manual dependency installation
is required beyond Lean/Elan and Git.
