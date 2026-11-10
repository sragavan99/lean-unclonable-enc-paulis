import QIT.Util.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# §4.3: the resolvent expansion

The geometric series in equation (36) turns uniform bounds on
`EB * EBC^ℓ * EC` into a bound on `EB * (D + δ I)⁻¹ * EC`.
The filter in Definition 4.7 uses the shift `δ = 2t`.
-/

open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator Ring

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe u

variable {h : Type u} [Fintype h] [DecidableEq h]

-- Supplying these scoped matrix instances explicitly prevents typeclass search
-- from repeatedly reconstructing the L2-operator C-star structure.
local instance resolventCMatrixNonUnitalCStarAlgebra (n : Type*) [Fintype n]
    [DecidableEq n] : NonUnitalCStarAlgebra (Matrix n n ℂ) := ⟨⟩

local instance resolventCMatrixCStarAlgebra (n : Type*) [Fintype n]
    [DecidableEq n] : CStarAlgebra (Matrix n n ℂ) := ⟨⟩

/-- The scalar ratio used in the geometric expansion of the regularized
resolvent. -/
def resolventRatio (δ : ℝ) : ℝ := (1 + δ)⁻¹

theorem resolventRatio_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < resolventRatio δ := by
  unfold resolventRatio
  positivity

theorem resolventRatio_lt_one {δ : ℝ} (hδ : 0 < δ) :
    resolventRatio δ < 1 := by
  unfold resolventRatio
  rw [inv_lt_one₀ (by linarith)]
  linarith

/-- Operator-norm convergence of the exact geometric expansion

`(D + δ I)⁻¹ = c ∑ₗ (c EBC)^ℓ`, where
`D = I - EBC` and `c = (1 + δ)⁻¹`.
-/
theorem resolvent_geometric_hasSum
    (D EBC : CMatrix h) (hD : D.PosSemidef) (hEBC : ‖EBC‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hD_eq : D = 1 - EBC) :
    HasSum
      (fun ℓ : ℕ =>
        (((resolventRatio δ : ℝ) : ℂ) •
          ((((resolventRatio δ : ℝ) : ℂ) • EBC) ^ ℓ)))
      (D + δ • (1 : CMatrix h))⁻¹ := by
  let c : ℝ := resolventRatio δ
  let x : CMatrix h := ((c : ℂ) • EBC)
  let A : CMatrix h := D + δ • (1 : CMatrix h)
  let k : ℂ := (c : ℝ)
  have hc0 : 0 < c := resolventRatio_pos hδ
  have hc1 : c < 1 := resolventRatio_lt_one hδ
  have hxnorm : ‖x‖ < 1 := by
    calc
      ‖x‖ = c * ‖EBC‖ := by simp [x, norm_smul, abs_of_pos hc0]
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hEBC hc0.le
      _ < 1 := by simpa using hc1
  have hgeom : HasSum (fun ℓ : ℕ => x ^ ℓ) (1 - x)⁻¹ʳ :=
    hasSum_geom_series_inverse x hxnorm
  have hApos : A.PosDef := by
    simpa [A] using Matrix.PosDef.posSemidef_add hD (Matrix.PosDef.one.smul hδ)
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hApos.isUnit
  have hk0 : k ≠ 0 := by
    simp [k, ne_of_gt hc0]
  letI : Invertible k := invertibleOfNonzero hk0
  have hone_sub : 1 - x = k • A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [x, k, A, hD_eq, c, resolventRatio]
      field_simp
      ring
    · simp [x, k, A, hD_eq, c, resolventRatio, hij]
  have hinv : k • (1 - x)⁻¹ = A⁻¹ := by
    rw [hone_sub, Matrix.inv_smul A k hAdet, smul_smul]
    simp
  have hgeom' : HasSum (fun ℓ : ℕ => x ^ ℓ) (1 - x)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    exact hgeom
  have hscaled := hgeom'.const_smul k
  rw [hinv] at hscaled
  simpa [c, x, k, A] using hscaled

/-- A uniform `ε` bound on all power coefficients gives an `ε / δ` bound
on the regularized resolvent coefficient.

Positivity gives invertibility of `D + δ I` and the contraction bound
gives convergence of the geometric series.
-/
theorem resolvent_sandwich_l2OperatorNorm_le
    (D EBC EB EC : CMatrix h)
    (hD : D.PosSemidef) (hEBC : ‖EBC‖ ≤ 1)
    {ε δ : ℝ} (hδ : 0 < δ)
    (hD_eq : D = 1 - EBC)
    (hpowers : ∀ ℓ : ℕ, ‖EB * EBC ^ ℓ * EC‖ ≤ ε) :
    ‖EB * (D + δ • (1 : CMatrix h))⁻¹ * EC‖ ≤ ε / δ := by
  let c : ℝ := resolventRatio δ
  have hc0 : 0 < c := resolventRatio_pos hδ
  have hc1 : c < 1 := resolventRatio_lt_one hδ
  have hs := resolvent_geometric_hasSum D EBC hD hEBC hδ hD_eq
  have hsand := (hs.mul_left EB).mul_right EC
  have hrealgeom : HasSum (fun ℓ : ℕ => c ^ ℓ) (1 - c)⁻¹ :=
    hasSum_geometric_of_lt_one hc0.le hc1
  have hcoeff :
      HasSum (fun ℓ : ℕ => (c * ε) * c ^ ℓ) (ε / δ) := by
    have hscaled := hrealgeom.const_smul (c * ε)
    convert hscaled using 1
    dsimp [c, resolventRatio]
    have hd : δ ≠ 0 := ne_of_gt hδ
    have ha : 1 + δ ≠ 0 := by linarith
    field_simp [hd, ha]
    ring
  rw [← hsand.tsum_eq]
  apply tsum_of_norm_bounded hcoeff
  intro ℓ
  have hterm :
      EB * ((((resolventRatio δ : ℝ) : ℂ) •
          ((((resolventRatio δ : ℝ) : ℂ) • EBC) ^ ℓ))) * EC =
        (((c * c ^ ℓ : ℝ) : ℂ) • (EB * EBC ^ ℓ * EC)) := by
    rw [smul_pow, smul_smul]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    dsimp [c]
    push_cast
    ring
  rw [hterm, norm_smul]
  have hcoefnonneg : 0 ≤ c * c ^ ℓ := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoefnonneg]
  calc
    (c * c ^ ℓ) * ‖EB * EBC ^ ℓ * EC‖ ≤
        (c * c ^ ℓ) * ε :=
      mul_le_mul_of_nonneg_left (hpowers ℓ) hcoefnonneg
    _ = (c * ε) * c ^ ℓ := by ring

end

end UE.PauliConstructionAndProof
