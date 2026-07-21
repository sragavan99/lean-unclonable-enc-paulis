import QIT.Util.Matrix
import Mathlib.Tactic

/-!
# Abstract proof: the reusable game-operator and disagreement layer

This file isolates the algebraic part of the monogamy game.  It assumes three
families of Hermitian reflections on one finite Hilbert space.  The `Q`
reflection commutes with every receiver reflection, and Bob's reflections
commute with Charlie's reflections.  There is deliberately no assumption that
two Bob reflections, or two Charlie reflections, commute.
-/

open scoped ComplexOrder MatrixOrder

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

set_option linter.unusedSectionVars false

universe uκ uh

variable {κ : Type uκ} {h : Type uh}
variable [Fintype κ] [Nonempty κ] [Fintype h] [DecidableEq h]

/-- The normalized uniform average of a finite nonempty matrix family. -/
def normalizedAverage (f : κ → CMatrix h) : CMatrix h :=
  ((Fintype.card κ : ℝ)⁻¹) • ∑ θ, f θ

@[simp]
theorem normalizedAverage_const (A : CMatrix h) :
    normalizedAverage (fun _ : κ => A) = A := by
  classical
  have hcard : (Fintype.card κ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [normalizedAverage, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hcard]

@[simp]
theorem normalizedAverage_zero :
    normalizedAverage (fun _ : κ => (0 : CMatrix h)) = 0 := by
  simp [normalizedAverage]

theorem normalizedAverage_add (f g : κ → CMatrix h) :
    normalizedAverage (fun θ => f θ + g θ) =
      normalizedAverage f + normalizedAverage g := by
  classical
  simp [normalizedAverage, Finset.sum_add_distrib, smul_add]

theorem normalizedAverage_sub (f g : κ → CMatrix h) :
    normalizedAverage (fun θ => f θ - g θ) =
      normalizedAverage f - normalizedAverage g := by
  classical
  simp [normalizedAverage, Finset.sum_sub_distrib, smul_sub]

theorem normalizedAverage_smul (r : ℝ) (f : κ → CMatrix h) :
    normalizedAverage (fun θ => r • f θ) = r • normalizedAverage f := by
  classical
  simp [normalizedAverage, Finset.smul_sum, smul_smul, mul_comm]

theorem normalizedAverage_isHermitian (f : κ → CMatrix h)
    (hf : ∀ θ, (f θ).IsHermitian) :
    (normalizedAverage f).IsHermitian := by
  classical
  rw [Matrix.IsHermitian]
  simp [normalizedAverage, Matrix.conjTranspose_sum, fun θ => (hf θ).eq]

theorem normalizedAverage_posSemidef (f : κ → CMatrix h)
    (hf : ∀ θ, (f θ).PosSemidef) :
    (normalizedAverage f).PosSemidef := by
  classical
  apply (Matrix.posSemidef_sum Finset.univ fun θ _ => hf θ).smul
  positivity

theorem one_sub_normalizedAverage (f : κ → CMatrix h) :
    1 - normalizedAverage f = normalizedAverage (fun θ => 1 - f θ) := by
  rw [normalizedAverage_sub, normalizedAverage_const]

/-- A Hermitian idempotent matrix is positive semidefinite. -/
theorem posSemidef_of_isHermitian_idempotent
    (A : CMatrix h) (hA : A.IsHermitian) (hAA : A * A = A) :
    A.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rw [hA.eq, hAA] at h
  exact h

/-- A Hermitian idempotent matrix is bounded above by the identity. -/
theorem le_one_of_isHermitian_idempotent
    (A : CMatrix h) (hA : A.IsHermitian) (hAA : A * A = A) :
    A ≤ 1 := by
  rw [Matrix.le_iff]
  apply posSemidef_of_isHermitian_idempotent (1 - A)
  · exact Matrix.isHermitian_one.sub hA
  · noncomm_ring [hAA]

/-- The positive-eigenspace projector of a Hermitian reflection. -/
def reflectionProjector (A : CMatrix h) : CMatrix h :=
  ((2 : ℝ)⁻¹) • (1 + A)

private theorem matrix_two_eq_two_smul_one :
    (2 : CMatrix h) = (2 : ℝ) • (1 : CMatrix h) := by
  ext i j
  rw [Matrix.ofNat_apply]
  simp [Matrix.one_apply, Matrix.smul_apply]

theorem reflectionProjector_isHermitian (A : CMatrix h)
    (hA : A.IsHermitian) :
    (reflectionProjector A).IsHermitian := by
  apply (Matrix.isHermitian_one.add hA).smul
  exact IsSelfAdjoint.of_nonneg (by positivity)

theorem reflectionProjector_idempotent (A : CMatrix h)
    (hAA : A * A = 1) :
    reflectionProjector A * reflectionProjector A =
      reflectionProjector A := by
  simp only [reflectionProjector, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  noncomm_ring [hAA]
  norm_num
  rw [matrix_two_eq_two_smul_one]
  simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  module

theorem reflectionProjector_posSemidef (A : CMatrix h)
    (hA : A.IsHermitian) (hAA : A * A = 1) :
    (reflectionProjector A).PosSemidef :=
  posSemidef_of_isHermitian_idempotent _
    (reflectionProjector_isHermitian A hA)
    (reflectionProjector_idempotent A hAA)

theorem reflectionProjector_commute
    (A C : CMatrix h) (hcomm : A * C = C * A) :
    reflectionProjector A * reflectionProjector C =
      reflectionProjector C * reflectionProjector A := by
  simp only [reflectionProjector, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  noncomm_ring [hcomm]

/-- The product of the two commuting positive-eigenspace projectors. -/
def jointReflectionProjector (A C : CMatrix h) : CMatrix h :=
  reflectionProjector A * reflectionProjector C

theorem jointReflectionProjector_expansion (A C : CMatrix h) :
    jointReflectionProjector A C =
      ((4 : ℝ)⁻¹) • ((1 + A) * (1 + C)) := by
  simp only [jointReflectionProjector, reflectionProjector,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num

theorem jointReflectionProjector_isHermitian
    (A C : CMatrix h) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hcomm : A * C = C * A) :
    (jointReflectionProjector A C).IsHermitian := by
  rw [Matrix.IsHermitian, jointReflectionProjector,
    Matrix.conjTranspose_mul,
    (reflectionProjector_isHermitian A hA).eq,
    (reflectionProjector_isHermitian C hC).eq]
  exact (reflectionProjector_commute A C hcomm).symm

theorem jointReflectionProjector_idempotent
    (A C : CMatrix h) (hAA : A * A = 1) (hCC : C * C = 1)
    (hcomm : A * C = C * A) :
    jointReflectionProjector A C * jointReflectionProjector A C =
      jointReflectionProjector A C := by
  let EA := reflectionProjector A
  let EC := reflectionProjector C
  have hEA : EA * EA = EA := reflectionProjector_idempotent A hAA
  have hEC : EC * EC = EC := reflectionProjector_idempotent C hCC
  have hcomm' : EA * EC = EC * EA :=
    reflectionProjector_commute A C hcomm
  change (EA * EC) * (EA * EC) = EA * EC
  calc
    (EA * EC) * (EA * EC) = EA * (EC * EA) * EC := by
      simp [Matrix.mul_assoc]
    _ = EA * (EA * EC) * EC := by rw [← hcomm']
    _ = (EA * EA) * (EC * EC) := by simp [Matrix.mul_assoc]
    _ = EA * EC := by rw [hEA, hEC]

theorem jointReflectionProjector_posSemidef
    (A C : CMatrix h) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hAA : A * A = 1) (hCC : C * C = 1)
    (hcomm : A * C = C * A) :
    (jointReflectionProjector A C).PosSemidef :=
  posSemidef_of_isHermitian_idempotent _
    (jointReflectionProjector_isHermitian A C hA hC hcomm)
    (jointReflectionProjector_idempotent A C hAA hCC hcomm)

theorem jointReflectionProjector_le_one
    (A C : CMatrix h) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hAA : A * A = 1) (hCC : C * C = 1)
    (hcomm : A * C = C * A) :
    jointReflectionProjector A C ≤ 1 :=
  le_one_of_isHermitian_idempotent _
    (jointReflectionProjector_isHermitian A C hA hC hcomm)
    (jointReflectionProjector_idempotent A C hAA hCC hcomm)

/-- Abstract reflection data arising after the common local Naimark dilation. -/
structure GameOperatorData (κ : Type uκ) (h : Type uh)
    [Fintype h] [DecidableEq h] where
  Q : κ → CMatrix h
  b : κ → CMatrix h
  c : κ → CMatrix h
  Q_hermitian : ∀ θ, (Q θ).IsHermitian
  b_hermitian : ∀ θ, (b θ).IsHermitian
  c_hermitian : ∀ θ, (c θ).IsHermitian
  Q_involution : ∀ θ, Q θ * Q θ = 1
  b_involution : ∀ θ, b θ * b θ = 1
  c_involution : ∀ θ, c θ * c θ = 1
  Q_comm_b : ∀ θ φ, Q θ * b φ = b φ * Q θ
  Q_comm_c : ∀ θ φ, Q θ * c φ = c φ * Q θ
  b_comm_c : ∀ θ φ, b θ * c φ = c φ * b θ

namespace GameOperatorData

variable (G : GameOperatorData κ h)

/-- Alice--Bob product reflection. -/
def B (θ : κ) : CMatrix h := G.Q θ * G.b θ

/-- Alice--Charlie product reflection. -/
def C (θ : κ) : CMatrix h := G.Q θ * G.c θ

/-- The single-key half-difference of the two correctness reflections. -/
def keyDifference (θ : κ) : CMatrix h :=
  ((2 : ℝ)⁻¹) • (G.B θ - G.C θ)

/-- The single-key winning projector. -/
def Pi (θ : κ) : CMatrix h :=
  ((4 : ℝ)⁻¹) • ((1 + G.B θ) * (1 + G.C θ))

/-- The averaged game operator. -/
def Xi : CMatrix h := normalizedAverage G.Pi

/-- The averaged Alice--Bob correlator. -/
def SB : CMatrix h := normalizedAverage G.B

/-- The averaged Alice--Charlie correlator. -/
def SC : CMatrix h := normalizedAverage G.C

/-- The averaged Bob--Charlie correlator. -/
def Z : CMatrix h := normalizedAverage (fun θ => G.b θ * G.c θ)

/-- The disagreement operator. -/
def D : CMatrix h :=
  normalizedAverage (fun θ => ((2 : ℝ)⁻¹) • (1 - G.b θ * G.c θ))

theorem B_isHermitian (θ : κ) : (G.B θ).IsHermitian := by
  rw [Matrix.IsHermitian, B, Matrix.conjTranspose_mul,
    (G.Q_hermitian θ).eq, (G.b_hermitian θ).eq]
  exact (G.Q_comm_b θ θ).symm

theorem C_isHermitian (θ : κ) : (G.C θ).IsHermitian := by
  rw [Matrix.IsHermitian, C, Matrix.conjTranspose_mul,
    (G.Q_hermitian θ).eq, (G.c_hermitian θ).eq]
  exact (G.Q_comm_c θ θ).symm

@[simp]
theorem B_mul_self (θ : κ) : G.B θ * G.B θ = 1 := by
  calc
    G.B θ * G.B θ = G.Q θ * (G.b θ * G.Q θ) * G.b θ := by
      simp [B, Matrix.mul_assoc]
    _ = G.Q θ * (G.Q θ * G.b θ) * G.b θ := by
      rw [← G.Q_comm_b θ θ]
    _ = (G.Q θ * G.Q θ) * (G.b θ * G.b θ) := by
      simp [Matrix.mul_assoc]
    _ = 1 := by rw [G.Q_involution, G.b_involution, Matrix.one_mul]

@[simp]
theorem C_mul_self (θ : κ) : G.C θ * G.C θ = 1 := by
  calc
    G.C θ * G.C θ = G.Q θ * (G.c θ * G.Q θ) * G.c θ := by
      simp [C, Matrix.mul_assoc]
    _ = G.Q θ * (G.Q θ * G.c θ) * G.c θ := by
      rw [← G.Q_comm_c θ θ]
    _ = (G.Q θ * G.Q θ) * (G.c θ * G.c θ) := by
      simp [Matrix.mul_assoc]
    _ = 1 := by rw [G.Q_involution, G.c_involution, Matrix.one_mul]

theorem B_mul_C (θ : κ) : G.B θ * G.C θ = G.b θ * G.c θ := by
  calc
    G.B θ * G.C θ = G.Q θ * (G.b θ * G.Q θ) * G.c θ := by
      simp [B, C, Matrix.mul_assoc]
    _ = G.Q θ * (G.Q θ * G.b θ) * G.c θ := by
      rw [← G.Q_comm_b θ θ]
    _ = (G.Q θ * G.Q θ) * (G.b θ * G.c θ) := by
      simp [Matrix.mul_assoc]
    _ = G.b θ * G.c θ := by rw [G.Q_involution, Matrix.one_mul]

theorem C_mul_B (θ : κ) : G.C θ * G.B θ = G.c θ * G.b θ := by
  calc
    G.C θ * G.B θ = G.Q θ * (G.c θ * G.Q θ) * G.b θ := by
      simp [B, C, Matrix.mul_assoc]
    _ = G.Q θ * (G.Q θ * G.c θ) * G.b θ := by
      rw [← G.Q_comm_c θ θ]
    _ = (G.Q θ * G.Q θ) * (G.c θ * G.b θ) := by
      simp [Matrix.mul_assoc]
    _ = G.c θ * G.b θ := by rw [G.Q_involution, Matrix.one_mul]

theorem B_comm_C (θ : κ) : G.B θ * G.C θ = G.C θ * G.B θ := by
  rw [G.B_mul_C, G.C_mul_B, G.b_comm_c]

theorem bc_isHermitian (θ φ : κ) :
    (G.b θ * G.c φ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul,
    (G.b_hermitian θ).eq, (G.c_hermitian φ).eq]
  exact (G.b_comm_c θ φ).symm

theorem bc_mul_self (θ : κ) :
    (G.b θ * G.c θ) * (G.b θ * G.c θ) = 1 := by
  calc
    (G.b θ * G.c θ) * (G.b θ * G.c θ) =
        G.b θ * (G.c θ * G.b θ) * G.c θ := by
      simp [Matrix.mul_assoc]
    _ = G.b θ * (G.b θ * G.c θ) * G.c θ := by
      rw [← G.b_comm_c θ θ]
    _ = (G.b θ * G.b θ) * (G.c θ * G.c θ) := by
      simp [Matrix.mul_assoc]
    _ = 1 := by rw [G.b_involution, G.c_involution, Matrix.one_mul]

theorem keyDifference_isHermitian (θ : κ) : (G.keyDifference θ).IsHermitian := by
  apply ((G.B_isHermitian θ).sub (G.C_isHermitian θ)).smul
  exact IsSelfAdjoint.of_nonneg (by positivity)

theorem Pi_eq_jointReflectionProjector (θ : κ) :
    G.Pi θ = jointReflectionProjector (G.B θ) (G.C θ) := by
  simp only [Pi, jointReflectionProjector, reflectionProjector,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  module

theorem Pi_isHermitian (θ : κ) : (G.Pi θ).IsHermitian := by
  rw [G.Pi_eq_jointReflectionProjector]
  exact jointReflectionProjector_isHermitian _ _
    (G.B_isHermitian θ) (G.C_isHermitian θ) (G.B_comm_C θ)

@[simp]
theorem Pi_idempotent (θ : κ) : G.Pi θ * G.Pi θ = G.Pi θ := by
  rw [G.Pi_eq_jointReflectionProjector]
  exact jointReflectionProjector_idempotent _ _
    (G.B_mul_self θ) (G.C_mul_self θ) (G.B_comm_C θ)

theorem Pi_posSemidef (θ : κ) : (G.Pi θ).PosSemidef :=
  posSemidef_of_isHermitian_idempotent _
    (G.Pi_isHermitian θ) (G.Pi_idempotent θ)

theorem Pi_le_one (θ : κ) : G.Pi θ ≤ 1 :=
  le_one_of_isHermitian_idempotent _
    (G.Pi_isHermitian θ) (G.Pi_idempotent θ)

theorem Xi_posSemidef : G.Xi.PosSemidef := by
  exact normalizedAverage_posSemidef G.Pi G.Pi_posSemidef

theorem Xi_nonneg : 0 ≤ G.Xi := G.Xi_posSemidef.nonneg

theorem Xi_le_one : G.Xi ≤ 1 := by
  rw [Xi, Matrix.le_iff, one_sub_normalizedAverage]
  apply normalizedAverage_posSemidef
  intro θ
  exact Matrix.le_iff.mp (G.Pi_le_one θ)

theorem SB_isHermitian : G.SB.IsHermitian :=
  normalizedAverage_isHermitian G.B G.B_isHermitian

theorem SC_isHermitian : G.SC.IsHermitian :=
  normalizedAverage_isHermitian G.C G.C_isHermitian

theorem Z_isHermitian : G.Z.IsHermitian :=
  normalizedAverage_isHermitian _ fun θ => G.bc_isHermitian θ θ

theorem D_isHermitian : G.D.IsHermitian := by
  apply normalizedAverage_isHermitian
  intro θ
  apply (Matrix.isHermitian_one.sub (G.bc_isHermitian θ θ)).smul
  exact IsSelfAdjoint.of_nonneg (by positivity)

theorem Pi_expansion (θ : κ) :
    G.Pi θ = ((4 : ℝ)⁻¹) •
      (1 + G.B θ + G.C θ + G.b θ * G.c θ) := by
  rw [Pi]
  noncomm_ring [G.B_mul_C θ]

/-- Exact current-paper decomposition of the averaged winning operator. -/
theorem Xi_decomposition :
    G.Xi = ((2 : ℝ)⁻¹) • (1 : CMatrix h) +
      ((4 : ℝ)⁻¹) • (G.SB + G.SC) - ((2 : ℝ)⁻¹) • G.D := by
  calc
    G.Xi = normalizedAverage (fun θ => ((4 : ℝ)⁻¹) •
        (1 + G.B θ + G.C θ + G.b θ * G.c θ)) := by
      apply congrArg normalizedAverage
      funext θ
      exact G.Pi_expansion θ
    _ = ((4 : ℝ)⁻¹) • ((1 : CMatrix h) + G.SB + G.SC + G.Z) := by
      rw [normalizedAverage_smul]
      rw [normalizedAverage_add, normalizedAverage_add,
        normalizedAverage_add, normalizedAverage_const]
      simp only [SB, SC, Z]
    _ = ((2 : ℝ)⁻¹) • (1 : CMatrix h) +
        ((4 : ℝ)⁻¹) • (G.SB + G.SC) - ((2 : ℝ)⁻¹) • G.D := by
      simp only [D, normalizedAverage_smul, normalizedAverage_sub,
        normalizedAverage_const, Z]
      module

@[simp]
theorem keyDifference_sq (θ : κ) :
    G.keyDifference θ ^ 2 = ((2 : ℝ)⁻¹) • (1 - G.b θ * G.c θ) := by
  rw [pow_two, keyDifference]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  noncomm_ring [G.B_mul_self θ, G.C_mul_self θ,
    G.B_mul_C θ, G.C_mul_B θ, ← G.b_comm_c θ θ]
  norm_num
  rw [matrix_two_eq_two_smul_one]
  simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  module

/-- `D` is the average quadratic disagreement. -/
theorem D_eq_normalizedAverage_keyDifference_sq :
    G.D = normalizedAverage (fun θ => G.keyDifference θ ^ 2) := by
  rw [show (fun θ => G.keyDifference θ ^ 2) =
      (fun θ => ((2 : ℝ)⁻¹) • (1 - G.b θ * G.c θ)) by
    funext θ
    exact G.keyDifference_sq θ]
  rfl

/-- The average key difference is exactly `(S_B-S_C)/2`. -/
theorem normalizedAverage_keyDifference :
    normalizedAverage G.keyDifference = ((2 : ℝ)⁻¹) • (G.SB - G.SC) := by
  rw [show G.keyDifference =
      (fun θ => ((2 : ℝ)⁻¹) • (G.B θ - G.C θ)) by
    rfl]
  rw [normalizedAverage_smul, normalizedAverage_sub]
  rfl

/-- The word-moment correlator is `I-2D`. -/
theorem Z_eq_one_sub_two_D :
    G.Z = 1 - (2 : ℝ) • G.D := by
  simp only [D, normalizedAverage_smul, normalizedAverage_sub,
    normalizedAverage_const, Z]
  module

theorem keyDifference_sq_posSemidef (θ : κ) :
    (G.keyDifference θ ^ 2).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (G.keyDifference θ)
  simpa [pow_two, (G.keyDifference_isHermitian θ).eq] using h

theorem keyDifference_sq_le_one (θ : κ) : G.keyDifference θ ^ 2 ≤ 1 := by
  rw [Matrix.le_iff, G.keyDifference_sq]
  have hproj := reflectionProjector_posSemidef
    (G.b θ * G.c θ) (G.bc_isHermitian θ θ) (G.bc_mul_self θ)
  have heq : 1 - ((2 : ℝ)⁻¹) • (1 - G.b θ * G.c θ) =
      reflectionProjector (G.b θ * G.c θ) := by
    simp only [reflectionProjector]
    module
  rwa [heq]

theorem D_posSemidef : G.D.PosSemidef := by
  rw [G.D_eq_normalizedAverage_keyDifference_sq]
  exact normalizedAverage_posSemidef _ G.keyDifference_sq_posSemidef

theorem D_nonneg : 0 ≤ G.D := G.D_posSemidef.nonneg

theorem D_le_one : G.D ≤ 1 := by
  rw [G.D_eq_normalizedAverage_keyDifference_sq, Matrix.le_iff,
    one_sub_normalizedAverage]
  apply normalizedAverage_posSemidef
  intro θ
  exact Matrix.le_iff.mp (G.keyDifference_sq_le_one θ)

/-- Positive product witnessing the first disagreement order constraint. -/
theorem keyDifference_sq_add_factorization (θ : κ) :
    G.keyDifference θ ^ 2 + G.keyDifference θ = ((2 : ℝ)⁻¹) •
      ((1 + G.B θ) * (1 - G.C θ)) := by
  rw [pow_two, keyDifference]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  noncomm_ring [G.B_mul_self θ, G.C_mul_self θ,
    G.B_comm_C θ]
  norm_num
  rw [matrix_two_eq_two_smul_one]
  simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  module

/-- Positive product witnessing the second disagreement order constraint. -/
theorem keyDifference_sq_sub_factorization (θ : κ) :
    G.keyDifference θ ^ 2 - G.keyDifference θ = ((2 : ℝ)⁻¹) •
      ((1 - G.B θ) * (1 + G.C θ)) := by
  rw [pow_two, keyDifference]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  noncomm_ring [G.B_mul_self θ, G.C_mul_self θ,
    G.B_comm_C θ]
  norm_num
  rw [matrix_two_eq_two_smul_one]
  simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  module

private theorem neg_reflection_isHermitian (A : CMatrix h)
    (hA : A.IsHermitian) : (-A).IsHermitian := hA.neg

private theorem neg_reflection_mul_self (A : CMatrix h)
    (hAA : A * A = 1) : (-A) * (-A) = 1 := by
  noncomm_ring [hAA]

private theorem commute_neg_right (A C : CMatrix h)
    (hcomm : A * C = C * A) : A * (-C) = (-C) * A := by
  noncomm_ring [hcomm]

private theorem commute_neg_left (A C : CMatrix h)
    (hcomm : A * C = C * A) : (-A) * C = C * (-A) := by
  noncomm_ring [hcomm]

theorem keyDifference_sq_add_posSemidef (θ : κ) :
    (G.keyDifference θ ^ 2 + G.keyDifference θ).PosSemidef := by
  have hjoint := jointReflectionProjector_posSemidef
    (G.B θ) (-G.C θ)
    (G.B_isHermitian θ) (neg_reflection_isHermitian _ (G.C_isHermitian θ))
    (G.B_mul_self θ) (neg_reflection_mul_self _ (G.C_mul_self θ))
    (commute_neg_right _ _ (G.B_comm_C θ))
  have hscaled := hjoint.smul (show (0 : ℝ) ≤ 2 by norm_num)
  rw [G.keyDifference_sq_add_factorization]
  have heq :
      (2 : ℝ) • jointReflectionProjector (G.B θ) (-G.C θ) =
        ((2 : ℝ)⁻¹) • ((1 + G.B θ) * (1 - G.C θ)) := by
    rw [jointReflectionProjector_expansion]
    have hminus : (1 : CMatrix h) + -G.C θ = 1 - G.C θ := by abel
    rw [hminus, smul_smul]
    norm_num
  rwa [← heq]

theorem keyDifference_sq_sub_posSemidef (θ : κ) :
    (G.keyDifference θ ^ 2 - G.keyDifference θ).PosSemidef := by
  have hjoint := jointReflectionProjector_posSemidef
    (-G.B θ) (G.C θ)
    (neg_reflection_isHermitian _ (G.B_isHermitian θ)) (G.C_isHermitian θ)
    (neg_reflection_mul_self _ (G.B_mul_self θ)) (G.C_mul_self θ)
    (commute_neg_left _ _ (G.B_comm_C θ))
  have hscaled := hjoint.smul (show (0 : ℝ) ≤ 2 by norm_num)
  rw [G.keyDifference_sq_sub_factorization]
  have heq :
      (2 : ℝ) • jointReflectionProjector (-G.B θ) (G.C θ) =
        ((2 : ℝ)⁻¹) • ((1 - G.B θ) * (1 + G.C θ)) := by
    rw [jointReflectionProjector_expansion]
    have hminus : (1 : CMatrix h) + -G.B θ = 1 - G.B θ := by abel
    rw [hminus, smul_smul]
    norm_num
  rwa [← heq]

/-- `D ≽ (S_B-S_C)/2`, obtained by averaging commuting positive
projector products key by key. -/
theorem half_SB_sub_SC_le_D :
    ((2 : ℝ)⁻¹) • (G.SB - G.SC) ≤ G.D := by
  rw [← G.normalizedAverage_keyDifference,
    G.D_eq_normalizedAverage_keyDifference_sq, Matrix.le_iff,
    ← normalizedAverage_sub]
  exact normalizedAverage_posSemidef _ G.keyDifference_sq_sub_posSemidef

/-- `D ≽ (S_C-S_B)/2`, with no same-receiver commutation assumption. -/
theorem half_SC_sub_SB_le_D :
    ((2 : ℝ)⁻¹) • (G.SC - G.SB) ≤ G.D := by
  rw [show ((2 : ℝ)⁻¹) • (G.SC - G.SB) =
      -normalizedAverage G.keyDifference by
        rw [G.normalizedAverage_keyDifference]
        module,
    G.D_eq_normalizedAverage_keyDifference_sq, Matrix.le_iff]
  rw [sub_neg_eq_add, ← normalizedAverage_add]
  exact normalizedAverage_posSemidef _ G.keyDifference_sq_add_posSemidef

end GameOperatorData

end

end UE.PauliConstructionAndProof
