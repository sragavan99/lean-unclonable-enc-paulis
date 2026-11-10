import PauliConstructionAndProof.Step3Disagreement.WordMoments
import PauliConstructionAndProof.Step3Disagreement.Resolvent

/-!
# §4.3: accounting for disagreement

The normalized filter of Definition 4.7 preserves a bound on the correlation
product by Lemma 4.8.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh

variable {κ : Type uκ} {h : Type uh}
variable [Fintype κ] [Nonempty κ]
variable [Fintype h] [DecidableEq h]

/-- The disagreement filter F(t) of Definition 4.7, used at positive t. -/
def disagreementFilter (D : CMatrix h) (t : ℝ) : CMatrix h :=
  (2 * t) • (D + (2 * t) • (1 : CMatrix h))⁻¹

variable [Nonempty h]

theorem game_EBC_norm_le_one (G : GameOperatorData κ h) : ‖G.EBC‖ ≤ 1 := by
  classical
  unfold GameOperatorData.EBC
  apply normalizedAverage_norm_le zero_le_one
  intro θ
  have hunitary : G.b θ * G.c θ ∈ unitary (CMatrix h) := by
    simpa only [Unitary.mem_iff, Matrix.star_eq_conjTranspose, IsUnitaryMatrix] using
      isUnitaryMatrix_of_hermitian_involution (G.bc_isHermitian θ θ) (G.bc_mul_self θ)
  exact (CStarRing.norm_of_mem_unitary hunitary).le

/-- A uniform word-moment estimate controls the regularized mixed product. -/
theorem game_resolvent_sandwich_norm_le_of_word_moment_bound
    (G : GameOperatorData κ h) {ε δ : ℝ}
    (hδ : 0 < δ)
    (hpowers : ∀ ℓ : ℕ, ‖G.EB * G.EBC ^ ℓ * G.EC‖ ≤ ε) :
    ‖G.EB * (G.D + δ • (1 : CMatrix h))⁻¹ * G.EC‖ ≤ ε / δ :=
  resolvent_sandwich_l2OperatorNorm_le G.D G.EBC G.EB G.EC
    G.D_posSemidef (game_EBC_norm_le_one G) hδ rfl hpowers

/-- Lemma 4.8. Inserting the normalized filter preserves the product bound. -/
theorem game_filter_sandwich_norm_le_of_product_bound
    (G : GameOperatorData κ h) {γ t : ℝ}
    (ht : 0 < t) (hprod : ‖G.EB * G.EC‖ ≤ γ) :
    ‖G.EB * disagreementFilter G.D t * G.EC‖ ≤ γ := by
  classical
  have hγ : 0 ≤ γ := (norm_nonneg _).trans hprod
  have hshift : 0 < 2 * t := by positivity
  have h := game_resolvent_sandwich_norm_le_of_word_moment_bound
    G hshift (game_word_moment_norm_le G hγ hprod)
  rw [disagreementFilter, Matrix.mul_smul, Matrix.smul_mul, norm_smul,
    Real.norm_eq_abs, abs_of_pos hshift, mul_comm (2 * t)]
  exact (le_div_iff₀ hshift).mp h

end

end UE.PauliConstructionAndProof
