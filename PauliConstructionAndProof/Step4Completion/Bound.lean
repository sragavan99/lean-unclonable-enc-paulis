import PauliConstructionAndProof.Step3Disagreement.Filter
import PauliConstructionAndProof.MatrixOrderInfrastructure
import PauliConstructionAndProof.Step4Completion.TopEigenvector

/-!
# §4.4: completing the security proof

Proposition 4.11 and Corollary 4.12 control the filtered quadratic forms.
Lemma 4.9 then bounds the top eigenvalue of the centered game. A product
bound from either proof of Lemma 4.4 gives the final bound in Theorem 4.1.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh

variable {κ : Type uκ} {h : Type uh}
variable [Fintype κ] [Nonempty κ]
variable [Fintype h] [DecidableEq h]

/-- Proposition 4.11 of arXiv:2607.21551v4. The Schur complement bounds the
filtered difference by the disagreement operator scaled by 2t. -/
theorem game_difference_quadratic_sandwich
    (G : GameOperatorData κ h) {t : ℝ} (ht : 0 < t) :
    (G.EB - G.EC) * disagreementFilter G.D t * (G.EB - G.EC) ≤
      (2 * t) • G.D := by
  have hplus : (G.D + (G.EB - G.EC)).PosSemidef := by
    convert Matrix.le_iff.mp G.EC_sub_EB_le_D using 1
    abel
  have hminus : (G.D - (G.EB - G.EC)).PosSemidef :=
    Matrix.le_iff.mp G.EB_sub_EC_le_D
  have h := quadratic_sandwich_le_of_add_sub_posSemidef G.D (G.EB - G.EC)
    G.D_posSemidef (G.EB_isHermitian.sub G.EC_isHermitian)
    hplus hminus (show 0 < 2 * t by positivity)
  rw [disagreementFilter, Matrix.mul_smul, Matrix.smul_mul, Matrix.le_iff, ← smul_sub]
  exact (Matrix.le_iff.mp h).smul (by positivity)

/-- Corollary 4.12 of arXiv:2607.21551v4. Expand the filtered sum using
equation (37) and bound the filtered difference by Proposition 4.11. -/
theorem game_sum_quadratic_sandwich
    (G : GameOperatorData κ h) {t : ℝ} (ht : 0 < t) :
    let F := disagreementFilter G.D t
    (G.EB + G.EC) * F * (G.EB + G.EC) ≤
      (2 * t) • G.D + (2 : ℝ) • (G.EB * F * G.EC) +
        (2 : ℝ) • (G.EC * F * G.EB) := by
  have hexpand (B C F : CMatrix h) :
      (B + C) * F * (B + C) =
        (B - C) * F * (B - C) + (2 : ℝ) • (B * F * C) +
          (2 : ℝ) • (C * F * B) := by
    simp only [two_smul]
    noncomm_ring
  dsimp only
  rw [hexpand, Matrix.le_iff]
  convert Matrix.le_iff.mp (game_difference_quadratic_sandwich G ht) using 1
  abel

omit [DecidableEq h] in
private theorem dotProduct_sandwich
    (X F : CMatrix h) (hX : X.IsHermitian) (v : h → ℂ) :
    star (Matrix.mulVec X v) ⬝ᵥ Matrix.mulVec F (Matrix.mulVec X v) =
      star v ⬝ᵥ Matrix.mulVec (X * F * X) v := by
  rw [Matrix.star_mulVec, hX.eq, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

omit [DecidableEq h] in
private theorem dotProduct_conjTranspose
    (X : CMatrix h) (v : h → ℂ) :
    star v ⬝ᵥ Matrix.mulVec (Matrix.conjTranspose X) v =
      star (star v ⬝ᵥ Matrix.mulVec X v) := by
  rw [Matrix.mulVec_conjTranspose]
  rw [Matrix.dotProduct_star, star_star]
  rw [← Matrix.dotProduct_mulVec]

variable [Nonempty h]

omit [Nonempty κ] in
/-- Equation (41) is the centered game eigenvector equation rearranged. -/
private theorem game_topEigenvector_sum_equation
    (G : GameOperatorData κ h) (hG : G.centeredGame.IsHermitian) :
    let t := topEigenvalue hG
    let psi := topEigenvector hG
    Matrix.mulVec (G.EB + G.EC) psi =
      Matrix.mulVec (G.D + (2 * t) • (1 : CMatrix h)) psi := by
  dsimp only
  have heig :
      Matrix.mulVec ((2 : ℝ)⁻¹ • (G.EB + G.EC - G.D)) (topEigenvector hG) =
        (topEigenvalue hG : ℂ) • topEigenvector hG :=
    topEigenvector_eigen_equation hG
  funext i
  have hi := congrFun heig i
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at hi ⊢
  norm_num [Complex.real_smul] at hi ⊢
  linear_combination 2 * hi

/-- Equation (42) uses the eigenvector equation on both sides of the filter. -/
private theorem game_sum_quadratic_exact
    (G : GameOperatorData κ h) (hG : G.centeredGame.IsHermitian)
    (ht : 0 < topEigenvalue hG) :
    let t := topEigenvalue hG
    let psi := topEigenvector hG
    Complex.re (star psi ⬝ᵥ Matrix.mulVec
        ((G.EB + G.EC) * disagreementFilter G.D t * (G.EB + G.EC)) psi) =
      4 * t ^ 2 + 2 * t * Complex.re (star psi ⬝ᵥ Matrix.mulVec G.D psi) := by
  let t := topEigenvalue hG
  let psi := topEigenvector hG
  let A : CMatrix h := G.D + (2 * t) • (1 : CMatrix h)
  have hshift : 0 < 2 * t := mul_pos (by norm_num) ht
  have hA : A.PosDef :=
    Matrix.PosDef.posSemidef_add G.D_posSemidef (Matrix.PosDef.one.smul hshift)
  letI : Invertible A := hA.isUnit.invertible
  have hrelation : Matrix.mulVec (G.EB + G.EC) psi = Matrix.mulVec A psi :=
    game_topEigenvector_sum_equation G hG
  have hcancel : Matrix.mulVec A⁻¹ (Matrix.mulVec A psi) = psi := by
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  dsimp only
  rw [← dotProduct_sandwich _ _ (G.EB_isHermitian.add G.EC_isHermitian), hrelation]
  change Complex.re (star (Matrix.mulVec A psi) ⬝ᵥ
    Matrix.mulVec ((2 * t) • A⁻¹) (Matrix.mulVec A psi)) = _
  simp only [Matrix.smul_mulVec, hcancel, dotProduct_smul, Complex.real_smul,
    Complex.re_ofReal_mul]
  have hform :
      Complex.re (star (Matrix.mulVec A psi) ⬝ᵥ psi) =
        Complex.re (star psi ⬝ᵥ Matrix.mulVec A psi) := by
    have hstar := Matrix.star_dotProduct (Matrix.mulVec A psi) psi
    simpa [Complex.star_def] using congrArg Complex.re hstar
  rw [hform]
  simp only [A, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, Complex.add_re, Complex.real_smul,
    Complex.re_ofReal_mul]
  have hunit : Complex.re (star psi ⬝ᵥ psi) = 1 := topEigenvector_dot_self hG
  rw [hunit]
  ring

/-- Lemma 4.9. A positive top eigenvalue of the centered game has square at
most the norm of the mixed product through the filter. -/
theorem game_topEigenvalue_sq_le_filter_norm
    (G : GameOperatorData κ h) (hG : G.centeredGame.IsHermitian)
    (ht : 0 < topEigenvalue hG) :
    let t := topEigenvalue hG
    t ^ 2 ≤ ‖G.EB * disagreementFilter G.D t * G.EC‖ := by
  let t := topEigenvalue hG
  let psi := topEigenvector hG
  let F := disagreementFilter G.D t
  have hshift : 0 < 2 * t := mul_pos (by norm_num) ht
  have hA : (G.D + (2 * t) • (1 : CMatrix h)).PosDef :=
    Matrix.PosDef.posSemidef_add G.D_posSemidef (Matrix.PosDef.one.smul hshift)
  have hF : F.IsHermitian := hA.isHermitian.inv.smul (IsSelfAdjoint.of_nonneg hshift.le)
  have horder := game_sum_quadratic_sandwich G ht
  dsimp only at horder
  have hquad := (Matrix.le_iff.mp horder).re_dotProduct_nonneg psi
  change 0 ≤ Complex.re _ at hquad
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_add, dotProduct_smul, Complex.sub_re, Complex.add_re,
    Complex.real_smul, Complex.re_ofReal_mul, sub_nonneg] at hquad
  have hadjoint : G.EC * F * G.EB = Matrix.conjTranspose (G.EB * F * G.EC) := by
    simp only [Matrix.conjTranspose_mul, G.EB_isHermitian.eq, G.EC_isHermitian.eq,
      hF.eq, Matrix.mul_assoc]
  rw [hadjoint, dotProduct_conjTranspose] at hquad
  simp only [Complex.star_def, Complex.conj_re] at hquad
  have hsum := game_sum_quadratic_exact G hG ht
  dsimp only at hsum
  have hlower : t ^ 2 ≤ Complex.re (star psi ⬝ᵥ Matrix.mulVec (G.EB * F * G.EC) psi) := by
    dsimp [F, psi, t] at hquad ⊢
    linarith only [hsum, hquad]
  exact hlower.trans ((Complex.re_le_norm _).trans
    (topEigenvector_quadratic_norm_le hG (G.EB * F * G.EC)))

/-- The shared completion of Theorem 4.1 from an abstract product bound. -/
theorem gameXi_le_of_product_bound
    (G : GameOperatorData κ h) {γ : ℝ} (hprod : ‖G.EB * G.EC‖ ≤ γ) :
    G.Xi ≤ ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt γ) • (1 : CMatrix h) := by
  apply G.Xi_le_of_centeredGame_le
  apply le_smul_one_of_topEigenvalue_le G.centeredGame_isHermitian
  let t := topEigenvalue G.centeredGame_isHermitian
  change t ≤ Real.sqrt γ
  by_cases ht : 0 < t
  · have hsq : t ^ 2 ≤ γ :=
      (game_topEigenvalue_sq_le_filter_norm G G.centeredGame_isHermitian ht).trans
        (game_filter_sandwich_norm_le_of_product_bound G ht hprod)
    have hγ : 0 ≤ γ := (norm_nonneg _).trans hprod
    nlinarith [Real.sq_sqrt hγ, Real.sqrt_nonneg γ]
  · exact (le_of_not_gt ht).trans (Real.sqrt_nonneg γ)

end

end UE.PauliConstructionAndProof
