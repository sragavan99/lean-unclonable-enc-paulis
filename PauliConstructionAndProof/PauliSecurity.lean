import PauliConstructionAndProof.Construction
import PauliConstructionAndProof.PauliGamma
import PauliConstructionAndProof.GeneralSecurity

/-!
# Exact full-Pauli security

The protected repository attack is converted exactly to the abstract
reflection attack, including equality of ciphertext states, fixed-key scores,
and the genuine uniform-measure cloning success.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT MeasureTheory UE

noncomputable section

/-- The concrete Pauli state is definitionally the abstract reflection state
after the full-Pauli family is installed. -/
theorem pauliCiphertextState_eq_reflectionCiphertextState
    (q : ℕ) [Nonempty (PauliKey q)] (k : PauliKey q) (b : Bool) :
    pauliCiphertextState k b =
      reflectionCiphertextState (pauliReflectionFamily q) k b := by
  apply State.ext
  rw [pauliCiphertextState_matrix_explicit,
    reflectionCiphertextState_matrix_explicit]
  simp [pauliReflectionFamily]

/-- Forget the protected measurability fields (automatic on this finite key
space) and view a protected Pauli attack as an abstract reflection attack. -/
def pauliAttackAsReflection (n : ℕ)
    (attack : CloningAttack pauliBitEncryption n) :
    ReflectionCloningAttack (pauliReflectionFamily (n + 1))
      (Fin attack.bobDim) (Fin attack.charlieDim) where
  pirate := attack.pirate
  bobMeasure := attack.bobMeasure
  charlieMeasure := attack.charlieMeasure

theorem pauliAttackAsReflection_keyScore (n : ℕ)
    (attack : CloningAttack pauliBitEncryption n) (k : PauliKey (n + 1)) :
    (pauliAttackAsReflection n attack).keyScore k = attack.keyScore k := by
  unfold ReflectionCloningAttack.keyScore CloningAttack.keyScore
  apply congrArg ((2 : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro b _
  rw [← pauliCiphertextState_eq_reflectionCiphertextState (n + 1) k b]
  rfl

/-- Exact bridge between the abstract uniform sum and the protected key
integral. -/
theorem pauliAttackAsReflection_success (n : ℕ)
    (attack : CloningAttack pauliBitEncryption n) :
    (pauliAttackAsReflection n attack).success = cloningSuccess attack := by
  rw [ReflectionCloningAttack.success, cloningSuccess]
  change
    (Fintype.card (PauliKey (n + 1)) : ℝ)⁻¹ *
        ∑ k : PauliKey (n + 1), (pauliAttackAsReflection n attack).keyScore k =
      letI : MeasurableSpace (PauliKey (n + 1)) := ⊤
      ∫ k : PauliKey (n + 1), attack.keyScore k
        ∂(PMF.uniformOfFintype (PauliKey (n + 1))).toMeasure
  rw [integral_uniformKeyDistribution_eq_average]
  apply congrArg
    ((Fintype.card (PauliKey (n + 1)) : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro k _
  exact pauliAttackAsReflection_keyScore n attack k

/-- Every protected attack satisfies the exact finite-parameter Pauli bound.

The protected parameter starts at `n = 0`; the paper's positive qubit count is
translated honestly as `q = n + 1`. Thus `d = 2^(n+1)` and
`M = 4^(n+1)-1`.
-/
theorem cloningSuccess_le_exact
    (n : ℕ) (attack : CloningAttack pauliBitEncryption n) :
    cloningSuccess attack ≤
      (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1)) := by
  letI : Nonempty (Fin attack.bobDim) := ⟨⟨0, attack.bobDim_pos⟩⟩
  letI : Nonempty (Fin attack.charlieDim) := ⟨⟨0, attack.charlieDim_pos⟩⟩
  have h := reflectionCloningSuccess_le (pauliAttackAsReflection n attack)
  rw [pauliAttackAsReflection_success n attack] at h
  rw [pauliReflectionFamily_Gamma_ratio n] at h
  exact h

end

end UE.PauliConstructionAndProof
