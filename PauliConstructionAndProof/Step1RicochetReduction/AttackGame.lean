import PauliConstructionAndProof.Step1RicochetReduction.PhysicalReduction
import PauliConstructionAndProof.GameOperator

/-!
# §4.1: winning probability in the ricochet reduction

The success probability is the expectation of the averaged winning operator
`Xi = (I + centeredGame)/2` on the dilated Choi state. This is the trace
identity in equation (22) for the reflection game.
-/

open scoped ComplexOrder MatrixOrder Kronecker

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh ub uc

variable {κ : Type uκ} {h : Type uh} {bob : Type ub} {charlie : Type uc}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype h] [DecidableEq h] [Nonempty h]
variable [Fintype bob] [DecidableEq bob] [Nonempty bob]
variable [Fintype charlie] [DecidableEq charlie] [Nonempty charlie]
variable {F : ReflectionFamily κ h}
variable (attack : ReflectionCloningAttack F bob charlie)

/-- The physical attack as generic common-space game data. -/
def reflectionAttackGameData :
    GameOperatorData κ (ReflectionAttackHilbert attack) where
  Q := reflectionAttackAlice attack
  b := reflectionAttackBob attack
  c := reflectionAttackCharlie attack
  Q_hermitian := reflectionAttackAlice_isHermitian attack
  b_hermitian := reflectionAttackBob_isHermitian attack
  c_hermitian := reflectionAttackCharlie_isHermitian attack
  Q_involution := reflectionAttackAlice_mul_self attack
  b_involution := reflectionAttackBob_mul_self attack
  c_involution := reflectionAttackCharlie_mul_self attack
  Q_comm_b := reflectionAttackAlice_commute_bob attack
  Q_comm_c := reflectionAttackAlice_commute_charlie attack
  b_comm_c := reflectionAttackBob_commute_charlie attack

private theorem lifted_spectator_factor_eq
    (A : CMatrix h)
    (D : CMatrix (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack))
    (s : ℂ) :
    Matrix.kronecker (1 + s • A) D =
      (1 + s • Matrix.kronecker A
        (1 : CMatrix
          (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack))) *
        Matrix.kronecker (1 : CMatrix h) D := by
  change
    ((1 + s • A) ⊗ₖ D) =
      (1 + s • (A ⊗ₖ (1 : CMatrix
        (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack)))) *
        ((1 : CMatrix h) ⊗ₖ D)
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul]
  simp [Matrix.add_kronecker, Matrix.smul_kronecker]

/-- The full dilated winning effect for a fixed plaintext bit. -/
theorem reflectionAttackDilatedFullEffect_eq (θ : κ) (bit : Bool) :
    Matrix.kronecker
        (Matrix.transpose (1 + bitSign bit • F.Q θ))
        (receiverFamilyProjector attack.bobMeasure attack.charlieMeasure
          θ bit bit) =
      (1 + bitSign bit • reflectionAttackAlice attack θ) *
        (((2 : ℂ)⁻¹ •
            (1 + bitSign bit • reflectionAttackBob attack θ)) *
          ((2 : ℂ)⁻¹ •
            (1 + bitSign bit • reflectionAttackCharlie attack θ))) := by
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul]
  rw [lifted_spectator_factor_eq attack]
  rw [reflectionAttackAlice]
  rw [reflectionAttackDilatedProductEffect_eq attack]

def reflectionAttackBitEffect (θ : κ) (bit : Bool) :
    CMatrix (ReflectionAttackHilbert attack) :=
  (1 + bitSign bit • reflectionAttackAlice attack θ) *
    (((2 : ℂ)⁻¹ • (1 + bitSign bit • reflectionAttackBob attack θ)) *
      ((2 : ℂ)⁻¹ • (1 + bitSign bit • reflectionAttackCharlie attack θ)))

/-- Uniform plaintext averaging is exactly the single-key winning projector. -/
theorem reflectionAttackBitEffect_average_eq_Pi (θ : κ) :
    (2 : ℂ)⁻¹ •
        (reflectionAttackBitEffect attack θ true +
          reflectionAttackBitEffect attack θ false) =
      (reflectionAttackGameData attack).Pi θ := by
  rw [(reflectionAttackGameData attack).Pi_expansion]
  simp only [reflectionAttackBitEffect, bitSign_true, bitSign_false,
    neg_smul, one_smul, reflectionAttackGameData,
    GameOperatorData.B, GameOperatorData.C]
  noncomm_ring
  module

/-- Equation (19) for a fixed key and plaintext, with the local dilations. -/
theorem reflectionAttackFixedBitProbability_eq (θ : κ) (bit : Bool) :
    ((jointPOVM (attack.bobMeasure θ) (attack.charlieMeasure θ)).prob
        (attack.pirate.applyState (reflectionCiphertextState F θ bit))
        (bit, bit) : ℝ) =
      Complex.re
        ((reflectionAttackDilationState attack).matrix *
          reflectionAttackBitEffect attack θ bit).trace := by
  rw [jointPOVM_prob_eq_trace_re]
  apply congrArg Complex.re
  let E : CMatrix (bob × charlie) :=
    Matrix.kronecker ((attack.bobMeasure θ).effects bit)
      ((attack.charlieMeasure θ).effects bit)
  let X : CMatrix h := 1 + bitSign bit • F.Q θ
  let omega : State (h × (bob × charlie)) := normalizedChoi attack.pirate
  calc
    (E * (attack.pirate.applyState
        (reflectionCiphertextState F θ bit)).matrix).trace =
        (attack.pirate.map
          (reflectionCiphertextState F θ bit).matrix * E).trace := by
      rw [Matrix.trace_mul_comm]
      rfl
    _ = (Matrix.kronecker X.transpose E * omega.matrix).trace := by
      rw [reflectionCiphertextState_matrix_explicit]
      exact trace_map_normalized_mul_eq_normalizedChoi attack.pirate X E
    _ = (omega.matrix * Matrix.kronecker X.transpose E).trace := by
      rw [Matrix.trace_mul_comm]
    _ = ((reflectionAttackDilationState attack).matrix *
        Matrix.kronecker X.transpose
          (receiverFamilyProjector attack.bobMeasure attack.charlieMeasure
            θ bit bit)).trace := by
      symm
      simpa [reflectionAttackDilationState, E] using
        spectatorReceiverLift_trace_projector_eq_with_spectator
          attack.bobMeasure attack.charlieMeasure omega X.transpose θ bit bit
    _ = ((reflectionAttackDilationState attack).matrix *
          reflectionAttackBitEffect attack θ bit).trace := by
      rw [show X = 1 + bitSign bit • F.Q θ by rfl]
      rw [reflectionAttackDilatedFullEffect_eq attack]
      rfl

/-- Exact fixed-key equality with `Pi_θ`. -/
theorem reflectionAttackKeyScore_eq_trace_Pi (θ : κ) :
    attack.keyScore θ =
      Complex.re (((reflectionAttackDilationState attack).matrix *
        (reflectionAttackGameData attack).Pi θ).trace) := by
  rw [ReflectionCloningAttack.keyScore, Fintype.sum_bool,
    reflectionAttackFixedBitProbability_eq attack θ true,
    reflectionAttackFixedBitProbability_eq attack θ false]
  have hmatrix := reflectionAttackBitEffect_average_eq_Pi attack θ
  have htrace := congrArg
    (fun A : CMatrix (ReflectionAttackHilbert attack) =>
      ((reflectionAttackDilationState attack).matrix * A).trace) hmatrix
  have hre := congrArg Complex.re htrace
  simp [Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add] at hre
  rw [mul_add]
  exact hre

/-- The trace identity in equation (22) with the averaged winning operator
`Xi` and the dilated Choi state. -/
theorem reflectionAttackSuccess_eq_trace_Xi :
    attack.success =
      Complex.re (((reflectionAttackDilationState attack).matrix *
        (reflectionAttackGameData attack).Xi).trace) := by
  rw [ReflectionCloningAttack.success]
  simp_rw [reflectionAttackKeyScore_eq_trace_Pi attack]
  rw [GameOperatorData.Xi, normalizedAverage]
  rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
  simp only [smul_eq_mul]
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp only [Complex.re_sum]

end


end UE.PauliConstructionAndProof
