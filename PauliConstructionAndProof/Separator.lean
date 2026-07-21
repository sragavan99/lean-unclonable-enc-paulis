import QIT.Util.BlockMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Abstract proof: the current reflection-game separator

This is the block-matrix separator in the current paper, in the variables
`S_B`, `S_C`, and `D`. The proof uses two Schur complements, inverse
antitonicity, and diagonalization of a symmetric block matrix.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance separatorCMatrixNonUnitalCStarAlgebra (n : Type*) [Fintype n]
    [DecidableEq n] : NonUnitalCStarAlgebra (Matrix n n ℂ) := ⟨⟩

local instance separatorCMatrixCStarAlgebra (n : Type*) [Fintype n]
    [DecidableEq n] : CStarAlgebra (Matrix n n ℂ) := ⟨⟩

/-- The Hermitian part of an operator of norm at most `δ` is at most `δ I`. -/
theorem hermitianPart_le_smul_one_of_l2OperatorNorm_le
    (X : CMatrix ι) {δ : ℝ} (hX : ‖X‖ ≤ δ) :
    ((realPart X : selfAdjoint (CMatrix ι)) : CMatrix ι) ≤
      δ • (1 : CMatrix ι) := by
  classical
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    have hself :
        IsSelfAdjoint (((realPart X : selfAdjoint (CMatrix ι)) : CMatrix ι)) :=
      (realPart X).property
    have hnorm : ‖((realPart X : selfAdjoint (CMatrix ι)) : CMatrix ι)‖ ≤ δ :=
      (realPart.norm_le X).trans hX
    calc
      ((realPart X : selfAdjoint (CMatrix ι)) : CMatrix ι) ≤
          algebraMap ℝ (CMatrix ι)
            ‖((realPart X : selfAdjoint (CMatrix ι)) : CMatrix ι)‖ :=
        IsSelfAdjoint.le_algebraMap_norm_self (a :=
          ((realPart X : selfAdjoint (CMatrix ι)) : CMatrix ι)) (ha := hself)
      _ ≤ algebraMap ℝ (CMatrix ι) δ :=
        algebraMap_le_algebraMap.mpr hnorm
      _ = δ • (1 : CMatrix ι) := by
        rw [Algebra.algebraMap_eq_smul_one]
  · letI : IsEmpty ι := not_nonempty_iff.mp hι
    exact le_of_eq (Subsingleton.elim _ _)

/-- Positivity of `R ± T` gives positivity of `[[R,T],[T,R]]`. -/
theorem symmetricBlock_posSemidef
    (R T : CMatrix ι)
    (hplus : (R + T).PosSemidef)
    (hminus : (R - T).PosSemidef) :
    (Matrix.fromBlocks R T T R : CMatrix (Sum ι ι)).PosSemidef := by
  let D : CMatrix (Sum ι ι) := Matrix.fromBlocks (R + T) 0 0 (R - T)
  let U : CMatrix (Sum ι ι) := Matrix.fromBlocks 1 1 1 (-1)
  have hD : D.PosSemidef := by
    simpa [D] using Matrix.fromBlocks_diagonal_posSemidef hplus hminus
  have hcongr : (U * D * Matrix.conjTranspose U).PosSemidef :=
    hD.mul_mul_conjTranspose_same U
  have hscaled :
      ((2 : ℝ)⁻¹ • (U * D * Matrix.conjTranspose U)).PosSemidef :=
    hcongr.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
  have hfactor :
      (2 : ℝ)⁻¹ • (U * D * Matrix.conjTranspose U) =
        (Matrix.fromBlocks R T T R : CMatrix (Sum ι ι)) := by
    ext (i | i) (j | j) <;>
      simp [U, D, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] <;>
      ring
  rwa [hfactor] at hscaled

/-- The negative eigenspace of a positive symmetric block matrix is positive. -/
theorem sub_posSemidef_of_symmetricBlock_posSemidef
    (A T : CMatrix ι)
    (hblock : (Matrix.fromBlocks A T T A : CMatrix (Sum ι ι)).PosSemidef) :
    (A - T).PosSemidef := by
  let U : CMatrix (Sum ι ι) := Matrix.fromBlocks 1 1 1 (-1)
  have hcongr := hblock.mul_mul_conjTranspose_same U
  have hscaled := hcongr.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
  have hdiag :
      (Matrix.fromBlocks (A + T) 0 0 (A - T) :
        CMatrix (Sum ι ι)).PosSemidef := by
    have heq :
        (2 : ℝ)⁻¹ •
            (U * Matrix.fromBlocks A T T A * Matrix.conjTranspose U) =
          (Matrix.fromBlocks (A + T) 0 0 (A - T) :
            CMatrix (Sum ι ι)) := by
      ext (i | i) (j | j) <;>
        simp [U, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] <;>
        ring
    rwa [heq] at hscaled
  have hright := hdiag.submatrix (Sum.inr : ι → Sum ι ι)
  simpa using hright

set_option maxHeartbeats 2000000 in
/-- The current `S_B,S_C,D` separator theorem. -/
theorem reflectionGameSeparator
    (SB SC D : CMatrix ι)
    (hSB : SB.IsHermitian) (hSC : SC.IsHermitian) (hDherm : D.IsHermitian)
    (hminus : (D - (2 : ℝ)⁻¹ • (SB - SC)).PosSemidef)
    (hplus : (D - (2 : ℝ)⁻¹ • (SC - SB)).PosSemidef)
    {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ)
    (hnorm :
      ‖SB * (D + δ • (1 : CMatrix ι))⁻¹ * SC‖ ≤ γ) :
    (2 : ℝ)⁻¹ • (SB + SC) - D ≤
      max δ γ • (1 : CMatrix ι) := by
  let T : CMatrix ι := (2 : ℝ)⁻¹ • (SB - SC)
  let S : CMatrix ι := SB + SC
  let A : CMatrix ι := D + δ • (1 : CMatrix ι)
  let F : CMatrix ι := A⁻¹
  let α : ℝ := max δ γ
  let Aα : CMatrix ι := D + α • (1 : CMatrix ι)
  let Fα : CMatrix ι := Aα⁻¹

  have hD : D.PosSemidef := by
    have hsum := hminus.add hplus
    have hscaled := hsum.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    have heq :
        (2 : ℝ)⁻¹ •
            ((D - (2 : ℝ)⁻¹ • (SB - SC)) +
              (D - (2 : ℝ)⁻¹ • (SC - SB))) = D := by
      module
    rwa [heq] at hscaled

  have hA : A.PosDef := by
    simpa [A] using Matrix.PosDef.posSemidef_add hD (Matrix.PosDef.one.smul hδ)
  letI : Invertible A := hA.isUnit.invertible
  have hF : F.IsHermitian := by
    simpa [F] using hA.isHermitian.inv

  let K : CMatrix ι := SB * F * SC
  have hKnorm : ‖K‖ ≤ γ := by
    simpa [K, F, A] using hnorm
  have hreal :
      ((realPart K : selfAdjoint (CMatrix ι)) : CMatrix ι) ≤
        γ • (1 : CMatrix ι) :=
    hermitianPart_le_smul_one_of_l2OperatorNorm_le K hKnorm
  have hsumdiff :
      S * F * S ≤ (SB - SC) * F * (SB - SC) +
        (4 * γ) • (1 : CMatrix ι) := by
    rw [Matrix.le_iff] at hreal ⊢
    have hscaled := hreal.smul (by norm_num : (0 : ℝ) ≤ 4)
    convert hscaled using 1
    rw [realPart_apply_coe]
    simp only [K, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      hSB.eq, hSC.eq, hF.eq]
    dsimp [S]
    noncomm_ring
    module

  have hquarter :
      (4 : ℝ)⁻¹ • (S * F * S) ≤
        (4 : ℝ)⁻¹ • ((SB - SC) * F * (SB - SC)) +
          γ • (1 : CMatrix ι) := by
    rw [Matrix.le_iff] at hsumdiff ⊢
    have hscaled := hsumdiff.smul (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
    convert hscaled using 1
    module

  have hDplusT : (D + T).PosSemidef := by
    have heq : D - (2 : ℝ)⁻¹ • (SC - SB) = D + T := by
      dsimp [T]
      module
    rwa [heq] at hplus
  have hDminusT : (D - T).PosSemidef := by
    simpa [T] using hminus
  have hblock :
      (Matrix.fromBlocks D T T D : CMatrix (Sum ι ι)).PosSemidef :=
    symmetricBlock_posSemidef D T hDplusT hDminusT
  have hregularizedBlock :
      (Matrix.fromBlocks D T T A : CMatrix (Sum ι ι)).PosSemidef := by
    have hdiag :
        (Matrix.fromBlocks 0 0 0 (δ • (1 : CMatrix ι)) :
          CMatrix (Sum ι ι)).PosSemidef :=
      Matrix.fromBlocks_diagonal_posSemidef Matrix.PosSemidef.zero
        (Matrix.PosDef.one.smul hδ).posSemidef
    have hadd := hblock.add hdiag
    have heq :
        (Matrix.fromBlocks D T T D : CMatrix (Sum ι ι)) +
            Matrix.fromBlocks 0 0 0 (δ • (1 : CMatrix ι)) =
          Matrix.fromBlocks D T T A := by
      rw [Matrix.fromBlocks_add]
      simp [A]
    rwa [heq] at hadd
  have hT : T.IsHermitian := (hSB.sub hSC).smul (by simp)
  have hTFT : T * F * T ≤ D := by
    have hblock' :
        (Matrix.fromBlocks D T (Matrix.conjTranspose T) A :
          CMatrix (Sum ι ι)).PosSemidef := by
      simpa [hT.eq] using hregularizedBlock
    have hschur := Matrix.fromBlocks_posSemidef_schurComplement22
      (A := D) (B := T) (D := A) hA hblock'
    rw [Matrix.le_iff]
    simpa [F, hT.eq] using hschur
  have hdiffQuarter :
      (4 : ℝ)⁻¹ • ((SB - SC) * F * (SB - SC)) ≤ D := by
    calc
      (4 : ℝ)⁻¹ • ((SB - SC) * F * (SB - SC)) = T * F * T := by
        dsimp [T]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        norm_num
      _ ≤ D := hTFT
  have hSFA : (4 : ℝ)⁻¹ • (S * F * S) ≤
      D + γ • (1 : CMatrix ι) :=
    hquarter.trans (add_le_add hdiffQuarter (le_refl _))

  have hα : 0 < α := hδ.trans_le (le_max_left δ γ)
  have hAα : Aα.PosDef := by
    simpa [Aα] using Matrix.PosDef.posSemidef_add hD (Matrix.PosDef.one.smul hα)
  letI : Invertible Aα := hAα.isUnit.invertible
  have hA_le_Aα : A ≤ Aα := by
    dsimp [A, Aα, α]
    apply add_le_add (le_refl D)
    simpa [← Algebra.algebraMap_eq_smul_one] using
      (algebraMap_le_algebraMap.mpr (le_max_left δ γ) :
        algebraMap ℝ (CMatrix ι) δ ≤ algebraMap ℝ (CMatrix ι) (max δ γ))
  have hFinv : Fα ≤ F := by
    rw [show Fα = Aα⁻¹ by rfl, show F = A⁻¹ by rfl,
      Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse]
    exact CStarAlgebra.ringInverse_le_ringInverse hA_le_Aα
      ⟨hA.posSemidef.nonneg, hA.isUnit⟩
  have hSFS : S * Fα * S ≤ S * F * S := by
    have hcongr := (Matrix.le_iff.mp hFinv).mul_mul_conjTranspose_same S
    rw [Matrix.le_iff]
    have hS : S.IsHermitian := hSB.add hSC
    simp only [hS.eq] at hcongr
    convert hcongr using 1
    noncomm_ring
  have hquarterInv :
      (4 : ℝ)⁻¹ • (S * Fα * S) ≤
        (4 : ℝ)⁻¹ • (S * F * S) := by
    rw [Matrix.le_iff]
    have hscaled := (Matrix.le_iff.mp hSFS).smul
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
    convert hscaled using 1
    module
  have hγα : D + γ • (1 : CMatrix ι) ≤ Aα := by
    dsimp [Aα, α]
    apply add_le_add (le_refl D)
    simpa [← Algebra.algebraMap_eq_smul_one] using
      (algebraMap_le_algebraMap.mpr (le_max_right δ γ) :
        algebraMap ℝ (CMatrix ι) γ ≤ algebraMap ℝ (CMatrix ι) (max δ γ))
  have hA24 : (4 : ℝ)⁻¹ • (S * Fα * S) ≤ Aα :=
    hquarterInv.trans (hSFA.trans hγα)

  let P : CMatrix ι := (2 : ℝ)⁻¹ • S
  have hP : P.IsHermitian := (hSB.add hSC).smul (by simp)
  have hPFP : P * Fα * P ≤ Aα := by
    calc
      P * Fα * P = (4 : ℝ)⁻¹ • (S * Fα * S) := by
        dsimp [P]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        norm_num
      _ ≤ Aα := hA24
  have hfinalBlock :
      (Matrix.fromBlocks Aα P P Aα : CMatrix (Sum ι ι)).PosSemidef := by
    have hschur := Matrix.PosDef.fromBlocks₂₂ Aα P (D := Aα) hAα
    have hblock' :
        (Matrix.fromBlocks Aα P (Matrix.conjTranspose P) Aα :
          CMatrix (Sum ι ι)).PosSemidef := by
      apply hschur.mpr
      rw [Matrix.le_iff] at hPFP
      simpa [Fα, hP.eq] using hPFP
    simpa [hP.eq] using hblock'
  have hsub : (Aα - P).PosSemidef :=
    sub_posSemidef_of_symmetricBlock_posSemidef Aα P hfinalBlock
  have hPA : P ≤ Aα := Matrix.le_iff.mpr hsub
  change P - D ≤ α • (1 : CMatrix ι)
  rw [sub_le_iff_le_add]
  simpa [Aα, add_comm] using hPA

end

end UE.PauliConstructionAndProof
