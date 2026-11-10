import PauliConstructionAndProof.Construction
import PauliConstructionAndProof.PauliGamma
import PauliConstructionAndProof.PauliOrthogonality
import PauliConstructionAndProof.GeneralSecurity
import PauliConstructionAndProof.RagavanSecurity
import PauliConstructionAndProof.AnanthSahaiSecurity

/-!
# Theorem 4.1: security of the Pauli scheme

An attack in the fixed-message one-bit game becomes a reflection-family
attack with the same success probability. Both proofs of Lemma 4.4 specialise
to the nonidentity Pauli key set of Definition 4.2.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT MeasureTheory UE

noncomputable section

/-- The Pauli ciphertext of equation (15) agrees with the ciphertext of the
associated reflection family. -/
theorem pauliCiphertextState_eq_reflectionCiphertextState
    (q : ℕ) [Nonempty (PauliKey q)] (k : PauliKey q) (b : Bool) :
    pauliCiphertextState k b =
      reflectionCiphertextState (pauliReflectionFamily q) k b := by
  apply State.ext
  rw [pauliCiphertextState_matrix_explicit,
    reflectionCiphertextState_matrix_explicit]
  simp [pauliReflectionFamily]

/-- View a Pauli attack as a reflection-family attack on the finite key set
of Definition 4.2. -/
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

/-- The finite uniform key average equals the success probability in the
operational one-bit game. -/
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

/-- Equation (17) of Theorem 4.1 using Proof A of Lemma 4.4.

At Lean index `n`, Definition 4.2 gives `q = n + 1` qubits,
dimension `d = 2^q`, and `K = 4^q - 1` keys.
-/
theorem cloningSuccess_le_exact_ragavan
    (n : ℕ) (attack : CloningAttack pauliBitEncryption n) :
    cloningSuccess attack ≤
      (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1)) := by
  letI : Nonempty (Fin attack.bobDim) := ⟨⟨0, attack.bobDim_pos⟩⟩
  letI : Nonempty (Fin attack.charlieDim) := ⟨⟨0, attack.charlieDim_pos⟩⟩
  have h := reflectionCloningSuccess_le_ragavan
    (pauliRagavanData (n + 1)) (pauliAttackAsReflection n attack)
  rw [pauliAttackAsReflection_success n attack] at h
  rw [pauliRagavanData_Gamma_ratio n] at h
  exact h

/-- Equation (17) of Theorem 4.1 using Proof B of Lemma 4.4 for the same
nonidentity Pauli scheme. -/
theorem cloningSuccess_le_exact_ananthSahai
    (n : ℕ) (attack : CloningAttack pauliBitEncryption n) :
    cloningSuccess attack ≤
      (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1)) := by
  letI : Nonempty (Fin attack.bobDim) := ⟨⟨0, attack.bobDim_pos⟩⟩
  letI : Nonempty (Fin attack.charlieDim) := ⟨⟨0, attack.charlieDim_pos⟩⟩
  have h := reflectionCloningSuccess_le_ananthSahai
    (pauliAnanthSahaiData (n + 1)) (pauliAttackAsReflection n attack)
  rw [pauliAttackAsReflection_success n attack] at h
  rw [pauliAnanthSahai_ratio n] at h
  exact h

/-- The default endpoint for Theorem 4.1 uses Proof A of Lemma 4.4. -/
theorem cloningSuccess_le_exact
    (n : ℕ) (attack : CloningAttack pauliBitEncryption n) :
    cloningSuccess attack ≤
      (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1)) :=
  cloningSuccess_le_exact_ragavan n attack

end

end UE.PauliConstructionAndProof
