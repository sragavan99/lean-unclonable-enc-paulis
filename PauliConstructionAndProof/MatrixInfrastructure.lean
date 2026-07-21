import QIT.Util.BlockMatrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# Abstract proof: matrix infrastructure for the reflection argument

Only the operator-norm, block-family, and finite-dimensional order lemmas used
by the current proof live here.  All norms are the matrix L2 operator norm.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh

/-- A square complex matrix is unitary. -/
def IsUnitaryMatrix {h : Type*} [Fintype h] [DecidableEq h]
    (A : CMatrix h) : Prop :=
  Matrix.conjTranspose A * A = 1 ∧ A * Matrix.conjTranspose A = 1

theorem isUnitaryMatrix_one {h : Type*} [Fintype h] [DecidableEq h] :
    IsUnitaryMatrix (1 : CMatrix h) := by
  simp [IsUnitaryMatrix]

theorem IsUnitaryMatrix.mul {h : Type*} [Fintype h] [DecidableEq h]
    {A B : CMatrix h} (hA : IsUnitaryMatrix A) (hB : IsUnitaryMatrix B) :
    IsUnitaryMatrix (A * B) := by
  constructor
  · rw [Matrix.conjTranspose_mul]
    calc
      Matrix.conjTranspose B * Matrix.conjTranspose A * (A * B) =
          Matrix.conjTranspose B * (Matrix.conjTranspose A * A) * B := by
            simp [Matrix.mul_assoc]
      _ = 1 := by rw [hA.1, Matrix.mul_one, hB.1]
  · rw [Matrix.conjTranspose_mul]
    calc
      (A * B) * (Matrix.conjTranspose B * Matrix.conjTranspose A) =
          A * (B * Matrix.conjTranspose B) * Matrix.conjTranspose A := by
            simp [Matrix.mul_assoc]
      _ = 1 := by rw [hB.2, Matrix.mul_one, hA.2]

theorem isUnitaryMatrix_of_hermitian_involution
    {h : Type*} [Fintype h] [DecidableEq h]
    {A : CMatrix h} (hA : A.IsHermitian) (hAA : A * A = 1) :
    IsUnitaryMatrix A := by
  rw [IsUnitaryMatrix, hA.eq]
  exact ⟨hAA, hAA⟩

/-- Horizontal block row whose `θ` block is `f θ`. -/
def matrixFamilyBlockRow
    {κ : Type uκ} {h : Type uh} [Fintype h] [DecidableEq h]
    (f : κ → CMatrix h) : Matrix h (κ × h) ℂ :=
  fun i θj => f θj.1 i θj.2

/-- Vertical block column whose `θ` block is `f θ`. -/
def matrixFamilyBlockColumn
    {κ : Type uκ} {h : Type uh} [Fintype h] [DecidableEq h]
    (f : κ → CMatrix h) : Matrix (κ × h) h ℂ :=
  fun θi j => f θi.1 θi.2 j

theorem matrixFamilyBlockRow_mul_conjTranspose
    {κ : Type uκ} {h : Type uh}
    [Fintype κ] [Fintype h] [DecidableEq h]
    (f : κ → CMatrix h) (hf : ∀ θ, IsUnitaryMatrix (f θ)) :
    matrixFamilyBlockRow f * Matrix.conjTranspose (matrixFamilyBlockRow f) =
      ((Fintype.card κ : ℕ) : ℂ) • (1 : CMatrix h) := by
  classical
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [matrixFamilyBlockRow, Matrix.conjTranspose_apply]
  calc
    (∑ θ, ∑ k, f θ i k * star (f θ j k)) =
        ∑ θ, (f θ * Matrix.conjTranspose (f θ)) i j := by
      apply Finset.sum_congr rfl
      intro θ _
      rw [Matrix.mul_apply]
      rfl
    _ = ∑ _θ : κ, (1 : CMatrix h) i j := by
      apply Finset.sum_congr rfl
      intro θ _
      rw [(hf θ).2]
    _ = (((Fintype.card κ : ℕ) : ℂ) • (1 : CMatrix h)) i j := by simp

theorem matrixFamilyBlockColumn_conjTranspose_mul
    {κ : Type uκ} {h : Type uh}
    [Fintype κ] [Fintype h] [DecidableEq h]
    (f : κ → CMatrix h) (hf : ∀ θ, IsUnitaryMatrix (f θ)) :
    Matrix.conjTranspose (matrixFamilyBlockColumn f) * matrixFamilyBlockColumn f =
      ((Fintype.card κ : ℕ) : ℂ) • (1 : CMatrix h) := by
  classical
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [matrixFamilyBlockColumn, Matrix.conjTranspose_apply]
  calc
    (∑ θ, ∑ k, star (f θ k i) * f θ k j) =
        ∑ θ, (Matrix.conjTranspose (f θ) * f θ) i j := by
      apply Finset.sum_congr rfl
      intro θ _
      rw [Matrix.mul_apply]
      rfl
    _ = ∑ _θ : κ, (1 : CMatrix h) i j := by
      apply Finset.sum_congr rfl
      intro θ _
      rw [(hf θ).1]
    _ = (((Fintype.card κ : ℕ) : ℂ) • (1 : CMatrix h)) i j := by simp

/-- Exact norm of a horizontal row of unitary blocks. -/
theorem matrixFamilyBlockRow_norm
    {κ : Type uκ} {h : Type uh}
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    [Fintype h] [DecidableEq h] [Nonempty h]
    (f : κ → CMatrix h) (hf : ∀ θ, IsUnitaryMatrix (f θ)) :
    ‖matrixFamilyBlockRow f‖ = Real.sqrt (Fintype.card κ : ℝ) := by
  have hsquare := Matrix.l2_opNorm_conjTranspose_mul_self
    (Matrix.conjTranspose (matrixFamilyBlockRow f))
  rw [Matrix.conjTranspose_conjTranspose,
    matrixFamilyBlockRow_mul_conjTranspose f hf,
    Matrix.l2_opNorm_conjTranspose] at hsquare
  have hscalar :
      ‖((Fintype.card κ : ℂ) • (1 : CMatrix h))‖ =
        (Fintype.card κ : ℝ) := by
    rw [norm_smul, norm_one]
    simp
  rw [hscalar] at hsquare
  have hsqrt := Real.sq_sqrt (show 0 ≤ (Fintype.card κ : ℝ) by positivity)
  nlinarith [norm_nonneg (matrixFamilyBlockRow f),
    Real.sqrt_nonneg (Fintype.card κ : ℝ)]

/-- Exact norm of a vertical column of unitary blocks. -/
theorem matrixFamilyBlockColumn_norm
    {κ : Type uκ} {h : Type uh}
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    [Fintype h] [DecidableEq h] [Nonempty h]
    (f : κ → CMatrix h) (hf : ∀ θ, IsUnitaryMatrix (f θ)) :
    ‖matrixFamilyBlockColumn f‖ = Real.sqrt (Fintype.card κ : ℝ) := by
  have hsquare := Matrix.l2_opNorm_conjTranspose_mul_self
    (matrixFamilyBlockColumn f)
  rw [matrixFamilyBlockColumn_conjTranspose_mul f hf] at hsquare
  have hscalar :
      ‖((Fintype.card κ : ℂ) • (1 : CMatrix h))‖ =
        (Fintype.card κ : ℝ) := by
    rw [norm_smul, norm_one]
    simp
  rw [hscalar] at hsquare
  have hsqrt := Real.sq_sqrt (show 0 ≤ (Fintype.card κ : ℝ) by positivity)
  nlinarith [norm_nonneg (matrixFamilyBlockColumn f),
    Real.sqrt_nonneg (Fintype.card κ : ℝ)]

/-- Amplification by the identity as a unital star-algebra homomorphism. -/
def matrixAmplificationStarAlgHom
    (κ : Type uκ) (h : Type uh)
    [Fintype κ] [DecidableEq κ] [Fintype h] [DecidableEq h] :
    CMatrix κ →⋆ₐ[ℂ] CMatrix (κ × h) where
  toFun A := Matrix.kronecker A (1 : CMatrix h)
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' A B := Matrix.add_kronecker A B 1
  map_mul' A B := by
    simpa using Matrix.mul_kronecker_mul A B
      (1 : CMatrix h) (1 : CMatrix h)
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    ext ⟨i, k⟩ ⟨j, l⟩
    by_cases hij : i = j <;> by_cases hkl : k = l <;>
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Matrix.smul_apply, hij, hkl]
  map_star' A := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
    ext ⟨i, k⟩ ⟨j, l⟩
    by_cases hkl : k = l
    · subst l
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.conjTranspose_apply, Matrix.one_apply]
    · simp [Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.conjTranspose_apply, Matrix.one_apply, hkl, Ne.symm hkl]

theorem matrixAmplificationStarAlgHom_injective
    (κ : Type uκ) (h : Type uh)
    [Fintype κ] [DecidableEq κ] [Fintype h] [DecidableEq h] [Nonempty h] :
    Function.Injective (matrixAmplificationStarAlgHom κ h) := by
  intro A B hAB
  let k : h := Classical.choice (inferInstance : Nonempty h)
  ext i j
  have hentry := congrArg (fun M : CMatrix (κ × h) => M (i, k) (j, k)) hAB
  simpa [matrixAmplificationStarAlgHom, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply] using hentry

local instance cMatrixNonUnitalCStarAlgebra (n : Type*) [Fintype n]
    [DecidableEq n] : NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩

local instance cMatrixCStarAlgebra (n : Type*) [Fintype n]
    [DecidableEq n] : CStarAlgebra (CMatrix n) := ⟨⟩

/-- Exact L2-operator-norm preservation under `A ↦ A ⊗ I`. -/
theorem matrixAmplification_norm
    (κ : Type uκ) (h : Type uh)
    [Fintype κ] [DecidableEq κ] [Fintype h] [DecidableEq h] [Nonempty h]
    (A : CMatrix κ) :
    ‖Matrix.kronecker A (1 : CMatrix h)‖ = ‖A‖ := by
  exact NonUnitalStarAlgHom.norm_map (matrixAmplificationStarAlgHom κ h)
    (matrixAmplificationStarAlgHom_injective κ h) A

end

end UE.PauliConstructionAndProof
