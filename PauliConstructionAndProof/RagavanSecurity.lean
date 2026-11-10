import PauliConstructionAndProof.GeneralSecurity
import PauliConstructionAndProof.Step2CorrelationProduct.ProofA.GammaBound
import PauliConstructionAndProof.Step4Completion.Bound

/-!
# Reflection-family security from commutation data

Proof A of Lemma 4.4 (§4.2.1) feeds the shared completion in §4.4.
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

/-- The operator bound obtained from the commutation-sign matrix. -/
theorem reflectionAttackXi_le_ragavan
    (R : RagavanData F) (attack : ReflectionCloningAttack F bob charlie) :
    (reflectionAttackGameData attack).Xi ≤
      ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (‖R.Gamma‖ / (Fintype.card κ : ℝ))) •
          (1 : CMatrix (ReflectionAttackHilbert attack)) :=
  gameXi_le_of_product_bound _ (reflectionAttack_EB_mul_EC_norm_le R attack)

/-- The reflection-family generalisation of Theorem 4.1 via Proof A,
with product bound `‖Gamma‖ / K` for `K` uniform keys. -/
theorem reflectionCloningSuccess_le_ragavan
    (R : RagavanData F) (attack : ReflectionCloningAttack F bob charlie) :
    attack.success ≤
      (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (‖R.Gamma‖ / (Fintype.card κ : ℝ)) := by
  apply reflectionCloningSuccess_le_of_Xi_le attack
  exact reflectionAttackXi_le_ragavan R attack

end

end UE.PauliConstructionAndProof
