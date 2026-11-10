import UE.Definitions
import QIT.Measurements.Naimark
import QIT.Nonlocality.ProjectiveRealization

/-!
# §4.1: normalized Choi states and simultaneous local Naimark dilation

Theorem 2.1 is expressed in Lean-QIT's Choi convention. The product of the
two local Naimark embeddings preserves the joint measurement probabilities
in the ricochet reduction.
-/

open scoped ComplexOrder MatrixOrder Kronecker

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe u v w x

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- With Lean-QIT's Choi convention, a trace-preserving map has Choi trace
equal to the input dimension. -/
theorem trace_choi_of_tracePreserving (Φ : MatrixMap a b)
    (hΦ : MatrixMap.IsTracePreserving Φ) :
    (MatrixMap.choi Φ).trace = (Fintype.card a : ℂ) := by
  rw [Matrix.trace]
  change (∑ ib : a × b,
      Φ (Matrix.single ib.1 ib.1 (1 : ℂ)) ib.2 ib.2) = _
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : a, ∑ j : b,
        Φ (Matrix.single i i (1 : ℂ)) j j) =
        ∑ i : a, (Φ (Matrix.single i i (1 : ℂ))).trace := by
          simp [Matrix.trace]
    _ = ∑ i : a, (Matrix.single i i (1 : ℂ)).trace := by
          apply Finset.sum_congr rfl
          intro i _
          exact hΦ (Matrix.single i i (1 : ℂ))
    _ = (Fintype.card a : ℂ) := by simp

/-- Exact Choi Born-rule identity for Lean-QIT's convention. -/
theorem trace_map_mul_eq_trace_transpose_kronecker_choi
    (Φ : MatrixMap a b) (X : CMatrix a) (E : CMatrix b) :
    ((Φ X) * E).trace =
      (Matrix.kronecker X.transpose E * MatrixMap.choi Φ).trace := by
  classical
  have hsingle (i j : a) :
      (Matrix.kronecker (Matrix.single j i (1 : ℂ)) E *
          MatrixMap.choi Φ).trace =
        (Φ (Matrix.single i j (1 : ℂ)) * E).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, MatrixMap.choi, Fintype.sum_prod_type,
      Matrix.single_apply]
    rw [Finset.sum_eq_single j]
    · simp only [true_and]
      calc
        (∑ r : b, ∑ k : a, ∑ s : b,
            (if i = k then 1 else 0) * E r s *
              Φ (Matrix.single k j (1 : ℂ)) s r) =
            ∑ r : b, ∑ s : b,
              E r s * Φ (Matrix.single i j (1 : ℂ)) s r := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_eq_single i]
          · simp
          · intro k _ hki
            have hik : i ≠ k := Ne.symm hki
            simp [hik]
          · simp
        _ = ∑ r : b, ∑ s : b,
              Φ (Matrix.single i j (1 : ℂ)) r s * E s r := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro s _
          ring
    · intro k _ hkj
      have hjk : j ≠ k := Ne.symm hkj
      simp [hjk]
    · simp
  have htranspose :
      X.transpose = ∑ i : a, ∑ j : a,
        X i j • Matrix.single j i (1 : ℂ) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        simp [hki]
      · simp
    · intro k _ hkj
      simp [hkj]
    · simp
  have hkronecker :
      Matrix.kronecker X.transpose E =
        ∑ i : a, ∑ j : a,
          X i j • Matrix.kronecker (Matrix.single j i (1 : ℂ)) E := by
    calc
      Matrix.kronecker X.transpose E =
          Matrix.kronecker (∑ i : a, ∑ j : a,
            X i j • Matrix.single j i (1 : ℂ)) E := by rw [htranspose]
      _ = _ := by
        ext p q
        simp only [Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
  calc
    ((Φ X) * E).trace =
        ∑ i : a, ∑ j : a,
          X i j * (Φ (Matrix.single i j (1 : ℂ)) * E).trace := by
      rw [MatrixMap.map_eq_sum_single]
      simp [Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul]
    _ = ∑ i : a, ∑ j : a,
          X i j *
            (Matrix.kronecker (Matrix.single j i (1 : ℂ)) E *
              MatrixMap.choi Φ).trace := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsingle]
    _ = (Matrix.kronecker X.transpose E * MatrixMap.choi Φ).trace := by
      rw [hkronecker]
      simp [Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul]

/-- The normalized Choi state of a channel as in Theorem 2.1. -/
def normalizedChoi [Nonempty a] (Φ : Channel a b) : State (a × b) where
  matrix := ((Fintype.card a : ℝ)⁻¹ : ℂ) • MatrixMap.choi Φ.map
  pos := Matrix.PosSemidef.smul Φ.completelyPositive (by positivity)
  trace_eq_one := by
    rw [Matrix.trace_smul, trace_choi_of_tracePreserving Φ.map Φ.tracePreserving]
    have hcard : (Fintype.card a : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card a ≠ 0)
    simp [hcard]

@[simp]
theorem normalizedChoi_matrix [Nonempty a] (Φ : Channel a b) :
    (normalizedChoi Φ).matrix =
      ((Fintype.card a : ℝ)⁻¹ : ℂ) • MatrixMap.choi Φ.map :=
  rfl

/-- The normalized Choi identity of Theorem 2.1 applied to the input
scaled by the inverse dimension, as in equation (19). -/
theorem trace_map_normalized_mul_eq_normalizedChoi
    [Nonempty a] (Φ : Channel a b) (X : CMatrix a) (E : CMatrix b) :
    (Φ.map (((Fintype.card a : ℝ)⁻¹ : ℂ) • X) * E).trace =
      (Matrix.kronecker X.transpose E * (normalizedChoi Φ).matrix).trace := by
  let dInv : ℂ := ((Fintype.card a : ℝ)⁻¹ : ℂ)
  calc
    (Φ.map (dInv • X) * E).trace =
        dInv * ((Φ.map X) * E).trace := by
      rw [map_smul, Matrix.smul_mul, Matrix.trace_smul]
      rfl
    _ = dInv *
        (Matrix.kronecker X.transpose E * MatrixMap.choi Φ.map).trace := by
      rw [trace_map_mul_eq_trace_transpose_kronecker_choi]
    _ = (Matrix.kronecker X.transpose E * (normalizedChoi Φ).matrix).trace := by
      rw [normalizedChoi_matrix]
      rw [Matrix.mul_smul, Matrix.trace_smul]
      rfl

section ProductFamilyDilation

variable {κ : Type x} {c : Type w}
variable [Fintype c] [DecidableEq c]

/-- The common tensor-product embedding for Bob's and Charlie's complete
families of binary POVMs. -/
def receiverFamilyEmbedding
    (B : κ → POVM Bool b) (C : κ → POVM Bool c) :
    Matrix (POVM.FamilyNaimarkSpace B × POVM.FamilyNaimarkSpace C) (b × c) ℂ :=
  Matrix.kronecker (POVM.familyNaimarkEmbedding B)
    (POVM.familyNaimarkEmbedding C)

theorem receiverFamilyEmbedding_isometry
    (B : κ → POVM Bool b) (C : κ → POVM Bool c) :
    Matrix.conjTranspose (receiverFamilyEmbedding B C) *
        receiverFamilyEmbedding B C = 1 := by
  unfold receiverFamilyEmbedding
  change Matrix.conjTranspose
      ((POVM.familyNaimarkEmbedding B) ⊗ₖ (POVM.familyNaimarkEmbedding C)) *
      ((POVM.familyNaimarkEmbedding B) ⊗ₖ (POVM.familyNaimarkEmbedding C)) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    POVM.familyNaimarkEmbedding_isometry B,
    POVM.familyNaimarkEmbedding_isometry C,
    Matrix.one_kronecker_one]

/-- The common receiver dilation, with an untouched spectator register. -/
def spectatorReceiverEmbedding
    (B : κ → POVM Bool b) (C : κ → POVM Bool c) :
    Matrix (a × (POVM.FamilyNaimarkSpace B × POVM.FamilyNaimarkSpace C))
      (a × (b × c)) ℂ :=
  Matrix.kronecker (1 : CMatrix a) (receiverFamilyEmbedding B C)

theorem spectatorReceiverEmbedding_isometry
    (B : κ → POVM Bool b) (C : κ → POVM Bool c) :
    Matrix.conjTranspose (spectatorReceiverEmbedding (a := a) B C) *
        spectatorReceiverEmbedding (a := a) B C = 1 := by
  unfold spectatorReceiverEmbedding
  change Matrix.conjTranspose
      ((1 : CMatrix a) ⊗ₖ receiverFamilyEmbedding B C) *
      ((1 : CMatrix a) ⊗ₖ receiverFamilyEmbedding B C) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simp [receiverFamilyEmbedding_isometry B C]

/-- Lift a state while applying the common local dilations only to the two
receiver registers. -/
def spectatorReceiverLift
    (B : κ → POVM Bool b) (C : κ → POVM Bool c)
    (ρ : State (a × (b × c))) :
    State (a × (POVM.FamilyNaimarkSpace B × POVM.FamilyNaimarkSpace C)) where
  matrix := spectatorReceiverEmbedding B C * ρ.matrix *
    Matrix.conjTranspose (spectatorReceiverEmbedding B C)
  pos := ρ.pos.mul_mul_conjTranspose_same (spectatorReceiverEmbedding B C)
  trace_eq_one := by
    rw [Matrix.trace_mul_cycle, spectatorReceiverEmbedding_isometry (a := a) B C,
      Matrix.one_mul, ρ.trace_eq_one]

/-- The product projector on the two common local dilation spaces. -/
def receiverFamilyProjector
    (B : κ → POVM Bool b) (C : κ → POVM Bool c)
    (key : κ) (outB outC : Bool) :
    CMatrix (POVM.FamilyNaimarkSpace B × POVM.FamilyNaimarkSpace C) :=
  Matrix.kronecker
    ((POVM.familyNaimarkProjectiveMeasurement B key).effects outB)
    ((POVM.familyNaimarkProjectiveMeasurement C key).effects outC)

/-- The simultaneous local dilation preserves the product effect even with an
arbitrary operator on the untouched spectator.  This is the form needed after
the Choi reduction, where the spectator carries a transposed Pauli. -/
theorem spectatorReceiverLift_trace_projector_eq_with_spectator
    (B : κ → POVM Bool b) (C : κ → POVM Bool c)
    (ρ : State (a × (b × c))) (A : CMatrix a)
    (key : κ) (outB outC : Bool) :
    ((spectatorReceiverLift B C ρ).matrix *
        Matrix.kronecker A
          (receiverFamilyProjector B C key outB outC)).trace =
      (ρ.matrix * Matrix.kronecker A
        (Matrix.kronecker ((B key).effects outB) ((C key).effects outC))).trace := by
  let J : Matrix
      (a × (POVM.FamilyNaimarkSpace B × POVM.FamilyNaimarkSpace C))
      (a × (b × c)) ℂ := spectatorReceiverEmbedding (a := a) B C
  let P : CMatrix
      (a × (POVM.FamilyNaimarkSpace B × POVM.FamilyNaimarkSpace C)) :=
    Matrix.kronecker A (receiverFamilyProjector B C key outB outC)
  have hcompression :
      Matrix.conjTranspose J * P * J =
        Matrix.kronecker A
          (Matrix.kronecker ((B key).effects outB) ((C key).effects outC)) := by
    unfold J P spectatorReceiverEmbedding receiverFamilyEmbedding receiverFamilyProjector
    change Matrix.conjTranspose
        ((1 : CMatrix a) ⊗ₖ
          ((POVM.familyNaimarkEmbedding B) ⊗ₖ (POVM.familyNaimarkEmbedding C))) *
        (A ⊗ₖ
          (((POVM.familyNaimarkProjectiveMeasurement B key).effects outB) ⊗ₖ
            ((POVM.familyNaimarkProjectiveMeasurement C key).effects outC))) *
        ((1 : CMatrix a) ⊗ₖ
          ((POVM.familyNaimarkEmbedding B) ⊗ₖ (POVM.familyNaimarkEmbedding C))) =
      A ⊗ₖ (((B key).effects outB) ⊗ₖ ((C key).effects outC))
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [POVM.familyNaimark_compression_projector B key outB,
      POVM.familyNaimark_compression_projector C key outC]
    simp
  change ((J * ρ.matrix * Matrix.conjTranspose J) * P).trace = _
  calc
    ((J * ρ.matrix * Matrix.conjTranspose J) * P).trace =
        (ρ.matrix * (Matrix.conjTranspose J * P * J)).trace := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [hcompression]

/-- Applying both common local Naimark dilations preserves the joint product
effect, including when the receivers are entangled with a spectator. -/
theorem spectatorReceiverLift_trace_projector_eq
    (B : κ → POVM Bool b) (C : κ → POVM Bool c)
    (ρ : State (a × (b × c))) (key : κ) (outB outC : Bool) :
    ((spectatorReceiverLift B C ρ).matrix *
        Matrix.kronecker (1 : CMatrix a)
          (receiverFamilyProjector B C key outB outC)).trace =
      (ρ.matrix * Matrix.kronecker (1 : CMatrix a)
        (Matrix.kronecker ((B key).effects outB) ((C key).effects outC))).trace :=
  spectatorReceiverLift_trace_projector_eq_with_spectator
    B C ρ (1 : CMatrix a) key outB outC

end ProductFamilyDilation

end

end UE.PauliConstructionAndProof
