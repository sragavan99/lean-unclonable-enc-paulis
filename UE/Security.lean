import UE.Definitions

/-!
# Security of one-bit unclonable encryption
-/

open Filter

namespace UE

noncomputable section

/-- A nonnegative real error is cryptographically negligible when it is
eventually bounded by every inverse positive power.  Values at finitely many
small parameters, including `n = 0`, are irrelevant to this eventual condition.
-/
def Negligible (ε : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ ε n) ∧
  ∀ c : ℕ, 0 < c → ∀ᶠ n in atTop, ε n ≤ ((n : ℝ) ^ c)⁻¹

namespace BitEncryptionFamily

/-- The ciphertext register uses at most polynomially many qubits in the
security parameter.  The inequality allows arbitrary finite Hilbert-space
dimensions: `cipherDim n` need not be a power of two.

This normalization is necessary because, without it, inverse-polynomial
security in the number `q` of ciphertext qubits could be made negligible in a
nominal parameter `n` merely by reindexing the family with `q(n) = 2^n`.
-/
def PolynomiallyBoundedCipherDimension (E : BitEncryptionFamily) : Prop :=
  ∃ C degree : ℕ, ∀ n : ℕ,
    E.cipherDim n ≤ 2 ^ (C * (n + 1) ^ degree)

/-- Information-theoretic unclonable indistinguishability in the fixed-message
one-bit game (Definition 2.11 of arXiv:2607.21551v4). The additive bound
`ε` applies to every admissible finite-dimensional attack. -/
def DeltaSecure (E : BitEncryptionFamily) (ε : ℕ → ℝ) : Prop :=
  ∀ n (T : CloningAttack E n),
    cloningSuccess T ≤ (2 : ℝ)⁻¹ + ε n

end BitEncryptionFamily

/-- All concrete data and proof obligations of a prospective secure bit
encryption construction. -/
structure SecureBitEncryption where
  /-- The concrete encryption states and key distributions. -/
  encryption : BitEncryptionFamily
  /-- The concrete key-dependent decoder channels. -/
  decryption : encryption.DecryptionFamily
  /-- Exact correctness of the concrete encryption and decoder. -/
  perfectCorrectness : encryption.PerfectlyCorrect decryption
  /-- The ciphertext Hilbert-space dimension embeds in polynomially many
  qubits, preventing artificial rescaling of the security parameter. -/
  cipherDimension_polynomiallyBounded :
    encryption.PolynomiallyBoundedCipherDimension
  /-- The additive security error. -/
  error : ℕ → ℝ
  /-- The security error is negligible. -/
  error_negligible : Negligible error
  /-- Every finite-dimensional cloning attack satisfies the security bound. -/
  security : encryption.DeltaSecure error

/-- Existence of an information-theoretically secure one-bit scheme. -/
def UncloneableBitExists : Prop :=
  Nonempty SecureBitEncryption

end

end UE
