import QIT.Util.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# §4.4: a unit top eigenvector

This module supplies the unit eigenvector and quadratic-form norm bound
used in Lemma 4.9.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- An index at which the finite spectrum of a Hermitian matrix is maximal. -/
def topEigenvectorIndex {A : CMatrix ι} (hA : A.IsHermitian) : ι :=
  Classical.choose
    (Finset.exists_max_image Finset.univ hA.eigenvalues
      Finset.univ_nonempty)

theorem eigenvalue_le_topEigenvectorIndex {A : CMatrix ι}
    (hA : A.IsHermitian) (i : ι) :
    hA.eigenvalues i ≤ hA.eigenvalues (topEigenvectorIndex hA) := by
  exact (Classical.choose_spec
    (Finset.exists_max_image Finset.univ hA.eigenvalues
      Finset.univ_nonempty)).2 i (Finset.mem_univ i)

/-- The largest eigenvalue of a Hermitian matrix. -/
def topEigenvalue {A : CMatrix ι} (hA : A.IsHermitian) : ℝ :=
  hA.eigenvalues (topEigenvectorIndex hA)

/-- A unit eigenvector for `topEigenvalue`. -/
def topEigenvector {A : CMatrix ι} (hA : A.IsHermitian) : ι → ℂ :=
  ⇑(hA.eigenvectorBasis (topEigenvectorIndex hA))

theorem topEigenvector_eigen_equation {A : CMatrix ι}
    (hA : A.IsHermitian) :
    Matrix.mulVec A (topEigenvector hA) =
      (topEigenvalue hA : ℂ) • topEigenvector hA := by
  simpa [topEigenvector, topEigenvalue] using
    hA.mulVec_eigenvectorBasis (topEigenvectorIndex hA)

theorem topEigenvector_dot_self {A : CMatrix ι} (hA : A.IsHermitian) :
    Complex.re
      (star (topEigenvector hA) ⬝ᵥ topEigenvector hA) = 1 := by
  let e := hA.eigenvectorBasis (topEigenvectorIndex hA)
  change Complex.re (star e.ofLp ⬝ᵥ e.ofLp) = 1
  rw [dotProduct_comm]
  rw [← EuclideanSpace.inner_eq_star_dotProduct e e]
  rw [inner_self_eq_norm_sq_to_K]
  rw [hA.eigenvectorBasis.orthonormal.norm_eq_one]
  norm_num

/-- The chosen eigenvector has Euclidean norm one. -/
theorem topEigenvector_euclidean_norm {A : CMatrix ι}
    (hA : A.IsHermitian) :
    ‖(EuclideanSpace.equiv ι ℂ).symm (topEigenvector hA)‖ = 1 := by
  let e := hA.eigenvectorBasis (topEigenvectorIndex hA)
  change ‖e‖ = 1
  exact hA.eigenvectorBasis.orthonormal.norm_eq_one _

/-- The quadratic form on the chosen unit eigenvector is bounded by the
operator norm, as used after equation (43). -/
theorem topEigenvector_quadratic_norm_le {A : CMatrix ι}
    (hA : A.IsHermitian) (M : CMatrix ι) :
    ‖star (topEigenvector hA) ⬝ᵥ
        Matrix.mulVec M (topEigenvector hA)‖ ≤ ‖M‖ := by
  let v : EuclideanSpace ℂ ι :=
    (EuclideanSpace.equiv ι ℂ).symm (topEigenvector hA)
  have hv : ‖v‖ = 1 := topEigenvector_euclidean_norm hA
  have hinner :
      star (topEigenvector hA) ⬝ᵥ
          Matrix.mulVec M (topEigenvector hA) =
        inner ℂ v
          (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  rw [hinner]
  calc
    ‖inner ℂ v
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M v)‖ ≤
        ‖v‖ *
          ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M v‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖M‖ * ‖v‖) := by
      gcongr
      simpa [Matrix.l2_opNorm_toEuclideanCLM] using
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M).le_opNorm v
    _ = ‖M‖ := by rw [hv]; ring

/-- Evaluating an operator upper bound on the named top eigenvector bounds its
top eigenvalue. -/
theorem topEigenvalue_le_of_le_smul_one {A : CMatrix ι}
    (hA : A.IsHermitian) {α : ℝ}
    (hle : A ≤ α • (1 : CMatrix ι)) :
    topEigenvalue hA ≤ α := by
  let v : ι → ℂ := topEigenvector hA
  have hpos : (α • (1 : CMatrix ι) - A).PosSemidef :=
    Matrix.le_iff.mp hle
  have hquad := hpos.re_dotProduct_nonneg v
  have heigen :
      Matrix.mulVec A v = (topEigenvalue hA : ℂ) • v := by
    exact topEigenvector_eigen_equation hA
  have hvnorm :
      Complex.re (star v ⬝ᵥ v) = 1 :=
    topEigenvector_dot_self hA
  simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    heigen, dotProduct_sub, dotProduct_smul, hvnorm,
    ← EuclideanSpace.inner_eq_star_dotProduct] using hquad

/-- A scalar upper bound on the named top eigenvalue reconstructs the
operator-order bound. -/
theorem le_smul_one_of_topEigenvalue_le {A : CMatrix ι}
    (hA : A.IsHermitian) {α : ℝ}
    (htop : topEigenvalue hA ≤ α) :
    A ≤ α • (1 : CMatrix ι) := by
  let U : Matrix.unitaryGroup ι ℂ := hA.eigenvectorUnitary
  let Λ : CMatrix ι :=
    Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have heig_le : ∀ i, hA.eigenvalues i ≤ α := by
    intro i
    exact (eigenvalue_le_topEigenvectorIndex hA i).trans htop
  have hdiag :
      (Matrix.diagonal
        (fun i => ((α - hA.eigenvalues i : ℝ) : ℂ)) :
          CMatrix ι).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast sub_nonneg.mpr (heig_le i)
  have hcongr := hdiag.mul_mul_conjTranspose_same (U : CMatrix ι)
  rw [Matrix.le_iff]
  convert hcongr using 1
  have hgap :
      (Matrix.diagonal
        (fun i => ((α - hA.eigenvalues i : ℝ) : ℂ)) :
          CMatrix ι) =
        α • (1 : CMatrix ι) - Λ := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Λ, Matrix.diagonal_apply_eq]
    · simp [Λ, hij]
  rw [hgap, Matrix.mul_sub, Matrix.sub_mul]
  have hU : (U : CMatrix ι) * Matrix.conjTranspose (U : CMatrix ι) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self U
  have hspectral :
      (U : CMatrix ι) * Λ * Matrix.conjTranspose (U : CMatrix ι) = A := by
    symm
    simpa [U, Λ, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose] using hA.spectral_theorem
  have hscalar :
      (U : CMatrix ι) * (α • (1 : CMatrix ι)) *
          Matrix.conjTranspose (U : CMatrix ι) =
        α • (1 : CMatrix ι) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
  rw [hscalar, hspectral]

end

end UE.PauliConstructionAndProof
