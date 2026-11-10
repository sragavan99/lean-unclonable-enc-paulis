import PauliConstructionAndProof.ReflectionConstruction

/-!
# §4.2.1: reflection-family commutation data

Proof A of Lemma 4.4 uses a matrix of pairwise commutation signs. For the Pauli
scheme this matrix is the restriction of `Ξ^Pauli` to the key set.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh

/-- Pairwise commute--anticommute data for the reflection-family form of Proof A. -/
structure RagavanData
    {κ : Type uκ} {h : Type uh}
    [Fintype κ] [DecidableEq κ] [Fintype h] [DecidableEq h]
    (F : ReflectionFamily κ h) where
  Gamma : CMatrix κ
  commutation : ∀ φ θ,
    F.Q φ * F.Q θ = Gamma φ θ • (F.Q θ * F.Q φ)

namespace RagavanData

variable {κ : Type uκ} {h : Type uh}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype h] [DecidableEq h] [Nonempty h]
variable {F : ReflectionFamily κ h}

/-- Every diagonal entry of the commutation matrix is derived to be `+1`. -/
@[simp]
theorem Gamma_diag (R : RagavanData F) (θ : κ) : R.Gamma θ θ = 1 := by
  have hcomm := R.commutation θ θ
  rw [F.Q_involution] at hcomm
  let i : h := Classical.choice (inferInstance : Nonempty h)
  have hij := congrArg (fun A : CMatrix h => A i i) hcomm
  simpa [Matrix.one_apply] using hij.symm

/-- The commutation scalar squares to one; this follows from invertibility. -/
theorem Gamma_mul_self (R : RagavanData F) (φ θ : κ) :
    R.Gamma φ θ * R.Gamma φ θ = 1 := by
  let γ : ℂ := R.Gamma φ θ
  have hcomm : F.Q φ * F.Q θ = γ • (F.Q θ * F.Q φ) :=
    R.commutation φ θ
  have hsquare :
      (F.Q φ * F.Q θ) * (F.Q φ * F.Q θ) =
        γ • (1 : CMatrix h) := by
    calc
      (F.Q φ * F.Q θ) * (F.Q φ * F.Q θ) =
          (γ • (F.Q θ * F.Q φ)) * (F.Q φ * F.Q θ) := by
            rw [hcomm]
      _ = γ • ((F.Q θ * F.Q φ) * (F.Q φ * F.Q θ)) := by
            rw [Matrix.smul_mul]
      _ = γ • (1 : CMatrix h) := by
            congr 1
            calc
              (F.Q θ * F.Q φ) * (F.Q φ * F.Q θ) =
                  F.Q θ * (F.Q φ * F.Q φ) * F.Q θ := by
                    simp [Matrix.mul_assoc]
              _ = 1 := by rw [F.Q_involution, Matrix.mul_one, F.Q_involution]
  have hmat : (1 : CMatrix h) = (γ * γ) • (1 : CMatrix h) := by
    calc
      (1 : CMatrix h) = F.Q φ * (F.Q φ * F.Q θ) * F.Q θ := by
        simp [Matrix.mul_assoc, F.Q_involution]
      _ = F.Q φ * (γ • (F.Q θ * F.Q φ)) * F.Q θ := by rw [hcomm]
      _ = γ • ((F.Q φ * F.Q θ) * (F.Q φ * F.Q θ)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        simp [Matrix.mul_assoc]
      _ = γ • (γ • (1 : CMatrix h)) := by rw [hsquare]
      _ = (γ * γ) • (1 : CMatrix h) := by rw [smul_smul]
  let i : h := Classical.choice (inferInstance : Nonempty h)
  have hij := congrArg (fun A : CMatrix h => A i i) hmat
  simpa [Matrix.one_apply, γ] using hij.symm

/-- Every entry of `Gamma` is a sign, derived from the reflection relations. -/
theorem Gamma_eq_one_or_neg_one (R : RagavanData F) (φ θ : κ) :
    R.Gamma φ θ = 1 ∨ R.Gamma φ θ = -1 := by
  have hfactor :
      (R.Gamma φ θ - 1) * (R.Gamma φ θ + 1) = 0 := by
    rw [mul_add, sub_mul]
    simp [R.Gamma_mul_self φ θ]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)

/-- The commutation matrix has strictly positive L2 operator norm. -/
theorem Gamma_norm_pos (R : RagavanData F) : 0 < ‖R.Gamma‖ := by
  rw [norm_pos_iff]
  intro hzero
  let θ : κ := Classical.choice (inferInstance : Nonempty κ)
  have hentry := congrArg (fun A : CMatrix κ => A θ θ) hzero
  simpa [R.Gamma_diag θ] using hentry

end RagavanData

end

end UE.PauliConstructionAndProof
