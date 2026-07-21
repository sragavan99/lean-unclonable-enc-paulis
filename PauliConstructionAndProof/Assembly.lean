import PauliConstructionAndProof.PauliSecurity
import PauliConstructionAndProof.Bounds

/-!
# Assembly of the exact Pauli construction

The public error is the exact finite-parameter correction, not the older
geometric upper envelope. The latter is used only to prove negligibility.
-/

open Filter

namespace UE.PauliConstructionAndProof

open UE

noncomputable section

/-- The exact additive correction at protected parameter `n`, corresponding
to the paper parameter `q = n + 1`. -/
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

/-- The concrete finite-key Pauli scheme packaged with its exact error. -/
def assemblePauliSecure : SecureBitEncryption where
  encryption := pauliBitEncryption
  decryption := pauliDecryption
  perfectCorrectness := pauliPerfectlyCorrect
  cipherDimension_polynomiallyBounded :=
    pauliCipherDimension_polynomiallyBounded
  error := pauliSecurityError
  error_negligible := pauliSecurityError_negligible
  security := by
    intro n attack
    simpa [pauliSecurityError] using cloningSuccess_le_exact n attack

end

end UE.PauliConstructionAndProof
