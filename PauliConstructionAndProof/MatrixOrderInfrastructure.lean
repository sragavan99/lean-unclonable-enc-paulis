import QIT.Util.BlockMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# §2.2: positive semidefinite block matrices

The symmetric block diagonalization and Schur-complement estimate of
Lemma 2.8 give the matrix-order bound used in Proposition 4.11.
-/

open scoped ComplexOrder MatrixOrder

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Construct the positive symmetric block matrix from `D ± T` by the
sum and difference basis of Lemma 2.8(2). -/
theorem symmetricBlock_posSemidef_of_add_sub
    (D T : CMatrix ι)
    (hplus : (D + T).PosSemidef)
    (hminus : (D - T).PosSemidef) :
    (Matrix.fromBlocks D T T D : CMatrix (Sum ι ι)).PosSemidef := by
  let A : CMatrix (Sum ι ι) :=
    Matrix.fromBlocks (D + T) 0 0 (D - T)
  let U : CMatrix (Sum ι ι) := Matrix.fromBlocks 1 1 1 (-1)
  have hA : A.PosSemidef := by
    simpa [A] using Matrix.fromBlocks_diagonal_posSemidef hplus hminus
  have hcongr : (U * A * Matrix.conjTranspose U).PosSemidef :=
    hA.mul_mul_conjTranspose_same U
  have hscaled :
      ((2 : ℝ)⁻¹ • (U * A * Matrix.conjTranspose U)).PosSemidef :=
    hcongr.smul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
  have heq :
      (2 : ℝ)⁻¹ • (U * A * Matrix.conjTranspose U) =
        (Matrix.fromBlocks D T T D : CMatrix (Sum ι ι)) := by
    ext (i | i) (j | j) <;>
      simp [U, A, Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_conjTranspose] <;>
      ring
  rwa [heq] at hscaled

/-- Generic quadratic sandwich from the two-sided order `-D ≤ T ≤ D`.

For `δ > 0`, block positivity and the Schur complement give
`T (D + δI)⁻¹ T ≤ D`, the matrix-order estimate used in Proposition 4.11
of arXiv:2607.21551v4.
-/
theorem quadratic_sandwich_le_of_add_sub_posSemidef
    (D T : CMatrix ι)
    (hD : D.PosSemidef)
    (hT : T.IsHermitian)
    (hplus : (D + T).PosSemidef)
    (hminus : (D - T).PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) :
    T * (D + δ • (1 : CMatrix ι))⁻¹ * T ≤ D := by
  let A : CMatrix ι := D + δ • (1 : CMatrix ι)
  have hA : A.PosDef := by
    simpa [A] using
      Matrix.PosDef.posSemidef_add hD (Matrix.PosDef.one.smul hδ)
  letI : Invertible A := hA.isUnit.invertible
  have hblock :
      (Matrix.fromBlocks D T T D :
        CMatrix (Sum ι ι)).PosSemidef :=
    symmetricBlock_posSemidef_of_add_sub D T hplus hminus
  have hregularized :
      (Matrix.fromBlocks D T T A :
        CMatrix (Sum ι ι)).PosSemidef := by
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
  have hblock' :
      (Matrix.fromBlocks D T (Matrix.conjTranspose T) A :
        CMatrix (Sum ι ι)).PosSemidef := by
    simpa [hT.eq] using hregularized
  have hschur :=
    Matrix.fromBlocks_posSemidef_schurComplement22
      (A := D) (B := T) (D := A) hA hblock'
  rw [Matrix.le_iff]
  simpa [A, hT.eq] using hschur

end

end UE.PauliConstructionAndProof
