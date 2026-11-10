# Unconditional Unclonable Encryption in Lean 4

This repository formalises the one-bit Pauli scheme in the combined paper
*Unconditional Unclonable Encryption* by Prabhanjan Ananth, Seyoon Ragavan, and
Amit Sahai (ARS26). It proves perfect correctness (Lemma 3.1) and the
information-theoretic unclonable-indistinguishability bound (Theorem 4.1).
[ARS26, arXiv:2607.21551v4](https://arxiv.org/abs/2607.21551v4)

The two proofs of the correlation-product bound draw on the authors' independent
original versions. [Ananth–Sahai](https://arxiv.org/abs/2607.21551v1) · [Ragavan](https://arxiv.org/abs/2607.21811v1)

The scheme samples uniformly from the `4^q - 1` nonidentity Paulis on `q`
qubits. The ciphertext is the normalized state on the selected eigenspace
(equation (15)), and decryption measures the corresponding projectors.
Lean indexes the construction from zero, so `q = n + 1` for Lean's parameter
`n`. The additive security bound is `1/2 * sqrt (2^q / (4^q - 1))`.
The formalisation covers the state-and-channel construction. ARS26 §3.1
describes its efficient local circuit implementation.

This formalization was made using Codex GPT-5.6 Sol and GPT-6 Astra.

## Proof structure

| ARS26 | Lean formalisation |
| --- | --- |
| §2.3, Definitions 2.10–2.11 and Remark 2.12 | The fixed-message one-bit game and security interface in [UE](UE/). |
| §3 and Lemma 3.1 | Uniform keys, eigenspace ciphertexts, decoding, and perfect correctness in [Construction.lean](PauliConstructionAndProof/Construction.lean). |
| §4.1, Definition 4.3 and equation (22) | The ricochet reduction uses the normalized Choi identity (Theorem 2.1) and simultaneous local Naimark dilation. The dilation preserves the success probability and realizes the receivers' POVMs as projective measurements. [Reduction](PauliConstructionAndProof/Step1RicochetReduction/) · [Game operators](PauliConstructionAndProof/GameOperator.lean) |
| §4.2.1, Proof A of Lemma 4.4 | A commutation-sign matrix factorization bounds `‖EB * EC‖`. [Proof A](PauliConstructionAndProof/Step2CorrelationProduct/ProofA/GammaBound.lean) |
| §4.2.2, Proof B of Lemma 4.4 | Conditional overlap (Lemma 4.5) and Hilbert–Schmidt orthogonality bound the same product. [Proof B](PauliConstructionAndProof/Step2CorrelationProduct/ProofB/EndpointBound.lean) · [Conditional overlap](PauliConstructionAndProof/Step2CorrelationProduct/ProofB/ConditionalOverlap.lean) |
| §4.3, Proposition 4.6 and Lemma 4.8 | Ordered-word estimates propagate the product bound `γ` through the disagreement filter for `D = I - EBC`. [Disagreement filter](PauliConstructionAndProof/Step3Disagreement/Filter.lean) |
| §4.4, Lemma 4.9, Proposition 4.11, and Corollary 4.12 | The proof applies the Schur-complement bound and evaluates Corollary 4.12 on a top eigenvector of the centered game. [Shared completion](PauliConstructionAndProof/Step4Completion/Bound.lean) |

### Public theorems

| Result | Proof A | Proof B |
| --- | --- | --- |
| Abstract reflection-family security | `reflectionCloningSuccess_le_ragavan` | `reflectionCloningSuccess_le_ananthSahai` |
| Theorem 4.1 for the Pauli scheme | `cloningSuccess_le_exact_ragavan` | `cloningSuccess_le_exact_ananthSahai` |
| `SecureBitEncryption` | `pauliConstructionSecure_ragavan` | `pauliConstructionSecure_ananthSahai` |
| Existence witness | `pauliConstructionProvesUncloneableBit_ragavan` | `pauliConstructionProvesUncloneableBit_ananthSahai` |

The abstract theorems apply to any nonempty, uniformly sampled subset of
nonidentity Paulis. For `K` selected keys, Proof B supplies `γ = 2^q / K`.
Proof A can use `γ = ‖Γ‖ / K` for the sign matrix restricted to those keys.
Both give a success bound of `1/2 + 1/2 * sqrt γ`.

`pauliConstructionPerfectlyCorrect` exposes Lemma 3.1. The advantage rate
`O(2^(-q/2))` is formalised by `pauliPaperExactCorrection_isBigO_invSqrtTwo_pow`
and its Lean-indexed version `pauliSecurityError_isBigO_invSqrtTwo_pow`.
The pointwise bound `pauliPaperExactCorrection_le_invSqrtTwo_pow` and the
negligibility proof are available through the Pauli umbrella.

### Haar extension

The repository also proves security of Haar-random conjugate-subspace
encryption by reducing to Theorem 4.1 via Proof A. The fixed-parameter theorem
`haarCloningSuccess_le_exact_fixed` applies to a closed unitary subgroup
containing the Clifford subgroup at that parameter. The family theorem
`haarCloningSuccess_le_exact_family` supports `haarConstructionSecure`, and
`fullUnitaryHaar_cloningSuccess_le_exact` specialises it to the full unitary group.

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
git clone https://github.com/sragavan99/lean-unclonable-enc-paulis.git
cd lean-unclonable-enc-paulis
lake build
```

`lake build` downloads the locked dependencies when necessary and checks the
generic `UE` interface, every Pauli and Haar proof module reachable through
their separate umbrellas, and the examples. This repository is a proof
library, not a command-line executable; building it is the primary way to run
and verify it.

To check only the public API smoke test, run:

```sh
lake env lean Examples/SmokeTest.lean
```

## Repository layout

| Path | Purpose |
| --- | --- |
| [`UE/`](UE) | Operational definitions for one-bit unclonable encryption, finite-dimensional attacks, and negligible advantage. |
| [`Examples/`](Examples) | An intentionally insecure interface demonstration and a public API smoke test. |
| [`PauliConstructionAndProof/`](PauliConstructionAndProof) | The Pauli construction of §3 and the two product bounds and shared security proof of §4. |
| [`HaarConstructionAndProof/`](HaarConstructionAndProof) | The Haar extension, including Clifford transitivity, normalized Haar measure, and the Pauli-to-Haar reduction. |
| [`UE.lean`](UE.lean) | Public umbrella for the operational interface in `UE.Security`. |
| [`PauliConstructionAndProof.lean`](PauliConstructionAndProof.lean) | Public Pauli umbrella. |
| [`HaarConstructionAndProof.lean`](HaarConstructionAndProof.lean) | Public Haar umbrella. |
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
