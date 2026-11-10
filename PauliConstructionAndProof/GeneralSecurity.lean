import PauliConstructionAndProof.Step1RicochetReduction.AttackGame
import QIT.Util.SDP.HermitianPSDTraceDuality

/-!
# From the game operator to the winning probability

The trace bound in equation (22) converts the operator inequality from §4.4
into a success bound for the fixed-message one-bit game.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh ub uc

variable {κ : Type uκ} {h : Type uh}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype h] [DecidableEq h] [Nonempty h]
variable {bob : Type ub} {charlie : Type uc}
variable [Fintype bob] [DecidableEq bob] [Nonempty bob]
variable [Fintype charlie] [DecidableEq charlie] [Nonempty charlie]
variable {F : ReflectionFamily κ h}

/-- Convert a scalar operator bound on `Xi` into the same success bound. -/
theorem reflectionCloningSuccess_le_of_Xi_le
    (attack : ReflectionCloningAttack F bob charlie) (α : ℝ)
    (hXi : (reflectionAttackGameData attack).Xi ≤
      α • (1 : CMatrix (ReflectionAttackHilbert attack))) :
    attack.success ≤ α := by
  rw [reflectionAttackSuccess_eq_trace_Xi attack]
  have htrace := cMatrix_trace_mul_le_of_le_posSemidef_left
    (reflectionAttackDilationState attack).pos
    hXi
  calc
    Complex.re (((reflectionAttackDilationState attack).matrix *
        (reflectionAttackGameData attack).Xi).trace) ≤
      Complex.re (((reflectionAttackDilationState attack).matrix *
        (α • (1 : CMatrix (ReflectionAttackHilbert attack)))).trace) := htrace
    _ = α := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
        (reflectionAttackDilationState attack).trace_eq_one]
      simp [Complex.real_smul]

end

end UE.PauliConstructionAndProof
