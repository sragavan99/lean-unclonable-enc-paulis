import PauliConstructionAndProof.PauliSecurity
import PauliConstructionAndProof.Bounds

/-!
# Packaging the Pauli scheme as secure one-bit encryption

Each package combines the construction and correctness of §3 with the
negligible advantage from Theorem 4.1. The two security fields use Proof A
and Proof B of Lemma 4.4.
-/

open Filter

namespace UE.PauliConstructionAndProof

open UE

noncomputable section

/-- The advantage bound in equation (17) at Lean index `n`, with
`q = n + 1` qubits. -/
def pauliSecurityError (n : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ * Real.sqrt
    (((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1))

theorem pauliSecurityError_eq_exactCorrection :
    pauliSecurityError = pauliExactCorrection := by
  funext n
  rfl

/-- The exact correction is negligible, by its checked geometric envelope. -/
theorem pauliSecurityError_negligible : Negligible pauliSecurityError := by
  constructor
  · intro n
    exact pauliExactCorrection_nonneg n
  · intro c hc
    have hgeo := three_fourths_pow_negligible.2 c hc
    filter_upwards [hgeo] with n hn
    exact (pauliExactCorrection_le_three_fourths_pow n).trans hn

/-- Evaluate the bound of Theorem 4.1 at qubit count `n + 1`. -/
theorem pauliSecurityError_eq_paper_reindex (n : ℕ) :
    pauliSecurityError n = pauliPaperExactCorrection (n + 1) :=
  rfl

/-- A pointwise advantage estimate at Lean index `n`. -/
theorem pauliSecurityError_le_invSqrtTwo_pow (n : ℕ) :
    pauliSecurityError n ≤
      ((1 : ℝ) / Real.sqrt 2) ^ (n + 2) := by
  rw [pauliSecurityError_eq_paper_reindex]
  simpa [Nat.add_assoc] using
    pauliPaperExactCorrection_le_invSqrtTwo_pow (n + 1) (by omega)

/-- The `O(2^{-n/2})` advantage bound in the Lean family index `n`,
corresponding to `n + 1` qubits. -/
theorem pauliSecurityError_isBigO_invSqrtTwo_pow :
    Asymptotics.IsBigO atTop pauliSecurityError
      (fun n : ℕ => ((1 : ℝ) / Real.sqrt 2) ^ n) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [] with n
  rw [Real.norm_eq_abs,
    abs_of_nonneg (pauliSecurityError_negligible.1 n)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpoint := pauliSecurityError_le_invSqrtTwo_pow n
  have hb : (1 : ℝ) / Real.sqrt 2 ≤ 1 := by
    have hsqrt :=
      Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)
    exact (div_le_one (Real.sqrt_pos.2 (by norm_num))).2 hsqrt
  have hnonneg : 0 ≤ (1 : ℝ) / Real.sqrt 2 := by positivity
  calc
    pauliSecurityError n ≤
        ((1 : ℝ) / Real.sqrt 2) ^ (n + 2) := hpoint
    _ ≤ ((1 : ℝ) / Real.sqrt 2) ^ n := by
      rw [pow_add]
      have hsq : ((1 : ℝ) / Real.sqrt 2) ^ 2 ≤ 1 := by
        exact pow_le_one₀ hnonneg hb
      exact mul_le_of_le_one_right (pow_nonneg hnonneg n) hsq
    _ = 1 * ((1 : ℝ) / Real.sqrt 2) ^ n := by ring

/-- Shared package constructor for the common Pauli encryption, decryption,
correctness, dimension, and asymptotic fields. -/
def assemblePauliSecureWith
    (hsecurity :
      pauliBitEncryption.DeltaSecure pauliSecurityError) :
    SecureBitEncryption where
  encryption := pauliBitEncryption
  decryption := pauliDecryption
  perfectCorrectness := pauliPerfectlyCorrect
  cipherDimension_polynomiallyBounded :=
    pauliCipherDimension_polynomiallyBounded
  error := pauliSecurityError
  error_negligible := pauliSecurityError_negligible
  security := hsecurity

/-- Theorem 4.1 as a `DeltaSecure` proof using the Proof A product bound. -/
theorem pauliDeltaSecure_ragavan :
    pauliBitEncryption.DeltaSecure pauliSecurityError := by
  intro n attack
  simpa [pauliSecurityError] using
    cloningSuccess_le_exact_ragavan n attack

/-- Theorem 4.1 as a `DeltaSecure` proof using the Proof B product bound. -/
theorem pauliDeltaSecure_ananthSahai :
    pauliBitEncryption.DeltaSecure pauliSecurityError := by
  intro n attack
  simpa [pauliSecurityError] using
    cloningSuccess_le_exact_ananthSahai n attack

/-- The Pauli security package from Proof A. -/
def assemblePauliSecure_ragavan : SecureBitEncryption :=
  assemblePauliSecureWith pauliDeltaSecure_ragavan

/-- The Pauli security package from Proof B. -/
def assemblePauliSecure_ananthSahai : SecureBitEncryption :=
  assemblePauliSecureWith pauliDeltaSecure_ananthSahai

/-- The default assembly uses the Proof A security package. -/
def assemblePauliSecure : SecureBitEncryption :=
  assemblePauliSecure_ragavan

end

end UE.PauliConstructionAndProof
