import QIT.Util.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Abstract proof: resolvent estimates from power bounds

This module packages the analytic step which turns uniform bounds on the
matrix coefficients `S_B Z^ℓ S_C` into a bound for the regularized
resolvent `S_B (R + δ I)⁻¹ S_C`.  Every norm below is the matrix L2
operator norm.
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
def resolventRatio (δ : ℝ) : ℝ := (1 + 2 * δ)⁻¹

theorem resolventRatio_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < resolventRatio δ := by
  unfold resolventRatio
  positivity

theorem resolventRatio_lt_one {δ : ℝ} (hδ : 0 < δ) :
    resolventRatio δ < 1 := by
  unfold resolventRatio
  rw [inv_lt_one₀ (by linarith)]
  linarith

/-- A positive contraction satisfies `R - R² ≽ 0`. -/
theorem posSemidef_sub_square_of_posSemidef_le_one
    (R : CMatrix h) (hR0 : R.PosSemidef) (hR1 : R ≤ 1) :
    (R - R * R).PosSemidef := by
  have hRsa : IsSelfAdjoint R := hR0.isHermitian
  have hR0' : (algebraMap ℝ (CMatrix h)) 0 ≤ R := by
    simpa using hR0.nonneg
  have hspec0 : ∀ x ∈ spectrum ℝ R, (0 : ℝ) ≤ x := by
    simpa using (algebraMap_le_iff_le_spectrum
      (R := ℝ) (A := CMatrix h) (p := IsSelfAdjoint)
      (a := R) (r := (0 : ℝ)) (ha := hRsa)).mp hR0'
  have hspec1 : ∀ x ∈ spectrum ℝ R, x ≤ (1 : ℝ) := by
    simpa using (CFC.le_one_iff
      (R := ℝ) (A := CMatrix h) (p := IsSelfAdjoint)
      (a := R) (ha := hRsa)).mp hR1
  have hpos : 0 ≤ cfc (fun x : ℝ => x - x * x) R := by
    rw [cfc_nonneg_iff
      (R := ℝ) (A := CMatrix h) (p := IsSelfAdjoint)
      (a := R) (f := fun x : ℝ => x - x * x) (ha := hRsa)]
    intro x hx
    have hx0 := hspec0 x hx
    have hx1 := hspec1 x hx
    nlinarith
  have hcfceq : cfc (fun x : ℝ => x - x * x) R = R - R * R := by
    rw [cfc_sub
      (R := ℝ) (A := CMatrix h) (p := IsSelfAdjoint)
      (f := fun x : ℝ => x) (g := fun x : ℝ => x * x) (a := R)]
    rw [cfc_mul
      (R := ℝ) (A := CMatrix h) (p := IsSelfAdjoint)
      (f := fun x : ℝ => x) (g := fun x : ℝ => x) (a := R)]
    change cfc id R - cfc id R * cfc id R = R - R * R
    rw [cfc_id (R := ℝ) (A := CMatrix h) (p := IsSelfAdjoint) R]
  rw [← hcfceq]
  exact Matrix.nonneg_iff_posSemidef.mp hpos

/-- If `0 ≼ R ≼ I`, then `Z = I - 2R` is a contraction in the matrix L2
operator norm. -/
theorem one_sub_two_smul_l2OperatorNorm_le_one
    (R : CMatrix h) (hR0 : R.PosSemidef) (hR1 : R ≤ 1) :
    ‖1 - (2 : ℝ) • R‖ ≤ 1 := by
  let Z : CMatrix h := 1 - (2 : ℝ) • R
  have hquad : (1 - Zᴴ * Z).PosSemidef := by
    have hbase := posSemidef_sub_square_of_posSemidef_le_one R hR0 hR1
    have hscaled : ((4 : ℝ) • (R - R * R)).PosSemidef :=
      hbase.smul (by norm_num)
    have hZherm : Zᴴ = Z := by
      simp [Z, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        hR0.isHermitian.eq]
    have hid : 1 - Zᴴ * Z = (4 : ℝ) • (R - R * R) := by
      rw [hZherm]
      simp only [Z]
      noncomm_ring
      module
    rwa [hid]
  have hstar : (Zᴴ * Z).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self Z
  have hstar_le : Zᴴ * Z ≤ 1 := by
    rw [Matrix.le_iff]
    exact hquad
  have hnormstar : ‖Zᴴ * Z‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (Zᴴ * Z) hstar.nonneg).2 hstar_le
  have hsq : ‖Z‖ * ‖Z‖ ≤ 1 := by
    rw [← Matrix.star_eq_conjTranspose, CStarRing.norm_star_mul_self] at hnormstar
    exact hnormstar
  have hnormZ : ‖Z‖ ≤ 1 := by
    nlinarith [norm_nonneg Z]
  simpa [Z] using hnormZ

/-- Adding a positive scalar multiple of the identity to a positive
semidefinite matrix produces a unit. -/
theorem regularized_isUnit
    (R : CMatrix h) (hR0 : R.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    IsUnit (R + δ • (1 : CMatrix h)) := by
  exact (Matrix.PosDef.posSemidef_add hR0 (Matrix.PosDef.one.smul hδ)).isUnit

/-- Operator-norm convergence of the exact geometric expansion

`(R + δ I)⁻¹ = 2c ∑ₗ (c Z)^ℓ`, where
`Z = I - 2R` and `c = (1 + 2δ)⁻¹`.
-/
theorem resolvent_geometric_hasSum
    (R Z : CMatrix h) (hR0 : R.PosSemidef) (hR1 : R ≤ 1)
    { δ : ℝ } (hδ : 0 < δ)
    (hZ : Z = 1 - (2 : ℝ) • R) :
    HasSum
      (fun ℓ : ℕ =>
        (((2 * resolventRatio δ : ℝ) : ℂ) •
          ((((resolventRatio δ : ℝ) : ℂ) • Z) ^ ℓ)))
      (R + δ • (1 : CMatrix h))⁻¹ := by
  let c : ℝ := resolventRatio δ
  let x : CMatrix h := ((c : ℂ) • Z)
  let A : CMatrix h := R + δ • (1 : CMatrix h)
  let k : ℂ := (2 * c : ℝ)
  have hc0 : 0 < c := resolventRatio_pos hδ
  have hc1 : c < 1 := resolventRatio_lt_one hδ
  have hZnorm : ‖Z‖ ≤ 1 := by
    rw [hZ]
    exact one_sub_two_smul_l2OperatorNorm_le_one R hR0 hR1
  have hxnorm : ‖x‖ < 1 := by
    calc
      ‖x‖ = c * ‖Z‖ := by simp [x, norm_smul, abs_of_pos hc0]
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hZnorm hc0.le
      _ < 1 := by simpa using hc1
  have hgeom : HasSum (fun ℓ : ℕ => x ^ ℓ) (1 - x)⁻¹ʳ :=
    hasSum_geom_series_inverse x hxnorm
  have hApos : A.PosDef := by
    simpa [A] using Matrix.PosDef.posSemidef_add hR0 (Matrix.PosDef.one.smul hδ)
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hApos.isUnit
  have hk0 : k ≠ 0 := by
    simp [k, ne_of_gt hc0]
  letI : Invertible k := invertibleOfNonzero hk0
  have hone_sub : 1 - x = k • A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [x, k, A, hZ, c, resolventRatio]
      field_simp
      ring
    · simp [x, k, A, hZ, c, resolventRatio, hij]
      field_simp
  have hinv : k • (1 - x)⁻¹ = A⁻¹ := by
    rw [hone_sub, Matrix.inv_smul A k hAdet, smul_smul]
    simp
  have hgeom' : HasSum (fun ℓ : ℕ => x ^ ℓ) (1 - x)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    exact hgeom
  have hscaled := hgeom'.const_smul k
  rw [hinv] at hscaled
  simpa [c, x, k, A] using hscaled

/-- The reusable resolvent estimate. A uniform `ε` bound on all power
coefficients implies the paper's `ε / δ` bound on the regularized
resolvent coefficient.

The order assumptions imply both invertibility of `R + δ I` and convergence
of the displayed geometric series; no finite-dimensional spectral theorem is
hidden in this statement.
-/
theorem resolvent_sandwich_l2OperatorNorm_le
    (R Z SB SC : CMatrix h)
    (hR0 : R.PosSemidef) (hR1 : R ≤ 1)
    { ε δ : ℝ } (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hZ : Z = 1 - (2 : ℝ) • R)
    (hpowers : ∀ ℓ : ℕ, ‖SB * Z ^ ℓ * SC‖ ≤ ε) :
    ‖SB * (R + δ • (1 : CMatrix h))⁻¹ * SC‖ ≤ ε / δ := by
  let c : ℝ := resolventRatio δ
  let x : CMatrix h := ((c : ℂ) • Z)
  let k : ℂ := (2 * c : ℝ)
  have hc0 : 0 < c := resolventRatio_pos hδ
  have hc1 : c < 1 := resolventRatio_lt_one hδ
  have hs := resolvent_geometric_hasSum R Z hR0 hR1 hδ hZ
  have hsand := (hs.mul_left SB).mul_right SC
  have hrealgeom : HasSum (fun ℓ : ℕ => c ^ ℓ) (1 - c)⁻¹ :=
    hasSum_geometric_of_lt_one hc0.le hc1
  have hcoeff :
      HasSum (fun ℓ : ℕ => (2 * c * ε) * c ^ ℓ) (ε / δ) := by
    have hscaled := hrealgeom.const_smul (2 * c * ε)
    convert hscaled using 1
    dsimp [c, resolventRatio]
    have hd : δ ≠ 0 := ne_of_gt hδ
    have ha : 1 + 2 * δ ≠ 0 := by linarith
    field_simp
    ring
  rw [← hsand.tsum_eq]
  apply tsum_of_norm_bounded hcoeff
  intro ℓ
  have hterm :
      SB * ((((2 * resolventRatio δ : ℝ) : ℂ) •
          ((((resolventRatio δ : ℝ) : ℂ) • Z) ^ ℓ))) * SC =
        (((2 * c * c ^ ℓ : ℝ) : ℂ) • (SB * Z ^ ℓ * SC)) := by
    rw [smul_pow, smul_smul]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    dsimp [c]
    push_cast
    ring
  rw [hterm, norm_smul]
  have hcoefnonneg : 0 ≤ 2 * c * c ^ ℓ := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoefnonneg]
  calc
    (2 * c * c ^ ℓ) * ‖SB * Z ^ ℓ * SC‖ ≤
        (2 * c * c ^ ℓ) * ε :=
      mul_le_mul_of_nonneg_left (hpowers ℓ) hcoefnonneg
    _ = (2 * c * ε) * c ^ ℓ := by ring

end

end UE.PauliConstructionAndProof
