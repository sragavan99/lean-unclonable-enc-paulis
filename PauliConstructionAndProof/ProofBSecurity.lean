import PauliConstructionAndProof.GeneralSecurity
import PauliConstructionAndProof.Step2CorrelationProduct.ProofB.EndpointBound
import PauliConstructionAndProof.Step4Completion.Bound

/-!
# Reflection-family security from Hilbert--Schmidt orthogonality

Proof B of Lemma 4.4 (§4.2.2) feeds the shared completion in §4.4.
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

/-- The operator bound obtained from pairwise Hilbert--Schmidt orthogonality. -/
theorem reflectionAttackXi_le_ananthSahai
    (AS : AnanthSahaiData F) (attack : ReflectionCloningAttack F bob charlie) :
    (reflectionAttackGameData attack).Xi ≤
      ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        ((Fintype.card h : ℝ) / (Fintype.card κ : ℝ))) •
          (1 : CMatrix (ReflectionAttackHilbert attack)) :=
  gameXi_le_of_product_bound _ (reflectionAttack_EB_mul_EC_norm_le_ananthSahai AS attack)

/-- The reflection-family generalisation of Theorem 4.1 via Proof B,
with product bound `d / K` for `K` uniform keys in dimension `d`. -/
theorem reflectionCloningSuccess_le_ananthSahai
    (AS : AnanthSahaiData F)
    (attack : ReflectionCloningAttack F bob charlie) :
    attack.success ≤
      (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        ((Fintype.card h : ℝ) / (Fintype.card κ : ℝ)) := by
  apply reflectionCloningSuccess_le_of_Xi_le attack
  exact reflectionAttackXi_le_ananthSahai AS attack

end

end UE.PauliConstructionAndProof
