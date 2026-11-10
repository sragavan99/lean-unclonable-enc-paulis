import PauliConstructionAndProof.Step1RicochetReduction.AttackGame
import PauliConstructionAndProof.Step2CorrelationProduct.ProofB.ConditionalOverlap
import PauliConstructionAndProof.Step2CorrelationProduct.ProofB.OrthogonalityData

/-!
# §4.2.2: Proof B of the correlation-product bound

With orthogonal encoding reflections and projective decoding, both
conditional Gram matrices equal `(d / K) I`, where `d` is the reference
dimension and `K` is the key count. Lemma 4.5 gives the product bound
in Lemma 4.4.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ ua ub uc

set_option maxRecDepth 10000
set_option maxHeartbeats 400000

variable {κ : Type uκ} {a : Type ua} {b : Type ub} {c : Type uc}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Nonempty b]
variable [Fintype c] [DecidableEq c] [Nonempty c]

/-- Reference-indexed blocks of an averaged correlation operator in Proof B. -/
def orthogonalCorrelationBlocks
    (Theta : κ → CMatrix a) (R : κ → CMatrix b) (i j : a) : CMatrix b :=
  ((Fintype.card κ : ℝ)⁻¹ : ℂ) •
    ∑ θ, (Theta θ i j) • R θ

omit [Nonempty a] [Nonempty b] [Nonempty c] in
theorem trace_conjTranspose_mul_eq_entry_sum (X Y : CMatrix a) :
    (Matrix.conjTranspose X * Y).trace =
      ∑ i, ∑ j, star (X j i) * Y j i := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [Nonempty a] [Nonempty b] [Nonempty c] in
private theorem sum_five_reorder
    {α β γ δ ε : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    {M : Type*} [AddCommMonoid M]
    (f : α → β → γ → δ → ε → M) :
    (∑ i, ∑ j, ∑ x, ∑ φ, ∑ θ, f i j x φ θ) =
      ∑ φ, ∑ θ, ∑ i, ∑ j, ∑ x, f i j x φ θ := by
  calc
    (∑ i, ∑ j, ∑ x, ∑ φ, ∑ θ, f i j x φ θ) =
        ∑ i, ∑ j, ∑ φ, ∑ x, ∑ θ, f i j x φ θ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ φ, ∑ j, ∑ x, ∑ θ, f i j x φ θ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ φ, ∑ i, ∑ j, ∑ x, ∑ θ, f i j x φ θ := by
      rw [Finset.sum_comm]
    _ = ∑ φ, ∑ i, ∑ j, ∑ θ, ∑ x, f i j x φ θ := by
      apply Finset.sum_congr rfl
      intro φ _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ φ, ∑ i, ∑ θ, ∑ j, ∑ x, f i j x φ θ := by
      apply Finset.sum_congr rfl
      intro φ _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ φ, ∑ θ, ∑ i, ∑ j, ∑ x, f i j x φ θ := by
      apply Finset.sum_congr rfl
      intro φ _
      rw [Finset.sum_comm]

omit [Nonempty a] [Nonempty b] [Nonempty c] in
private theorem distribute_five
    {α β γ δ ε : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    {R : Type*} [CommSemiring R]
    (d : R) (A : α → β → γ → δ → R) (B : α → β → ε → R) :
    d * ∑ φ, ∑ θ, (∑ i, ∑ j, A φ θ i j) * (∑ x, B φ θ x) =
      ∑ φ, ∑ θ, ∑ i, ∑ j, ∑ x, d * A φ θ i j * B φ θ x := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro φ _
  apply Finset.sum_congr rfl
  intro θ _
  calc
    (∑ x, d * ∑ i, ∑ j, A φ θ i j * B φ θ x) =
        ∑ x, ∑ i, ∑ j, d * A φ θ i j * B φ θ x := by
      apply Finset.sum_congr rfl
      intro x _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, ∑ x, d * A φ θ i j * B φ θ x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]

omit [Nonempty a] [Nonempty b] [Nonempty c] in
private theorem diagonal_double_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    {R : Type*} [Semiring R] (d : R) (f : α → α → R) :
    (∑ x, ∑ y, (if y = x then d else 0) * f y x) =
      ∑ x, d * f x x := by
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

omit [Nonempty c] in
/-- Orthogonality evaluates the left conditional Gram exactly. -/
theorem orthogonalCorrelationBlocks_leftGram
    (Theta : κ → CMatrix a) (R : κ → CMatrix b)
    (hThetaHermitian : ∀ θ, (Theta θ).IsHermitian)
    (horth : ∀ θ φ,
      (Theta θ * Theta φ).trace =
        if θ = φ then (Fintype.card a : ℂ) else 0)
    (hR : ∀ θ, IsUnitaryMatrix (R θ)) :
    conditionalLeftGram (orthogonalCorrelationBlocks Theta R) =
      ((Fintype.card a : ℝ) / (Fintype.card κ : ℝ)) •
        (1 : CMatrix b) := by
  classical
  let m : ℝ := Fintype.card κ
  have hm : m ≠ 0 := by
    apply ne_of_gt
    dsimp [m]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hstar (i j : a) (x q : b) :
      star ((orthogonalCorrelationBlocks Theta R i j) x q) =
        (m⁻¹ : ℂ) * ∑ θ, star (Theta θ i j * R θ x q) := by
    simp [orthogonalCorrelationBlocks, Matrix.sum_apply, Matrix.smul_apply,
      m, star_sum, star_mul, mul_comm]
  ext p q
  simp only [conditionalLeftGram, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  simp_rw [hstar]
  simp only [orthogonalCorrelationBlocks, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
      (∑ i, ∑ j, ∑ x, ∑ φ, ∑ θ,
        (m⁻¹ : ℂ) * star (Theta θ i j * R θ x p) *
          (((Fintype.card κ : ℝ)⁻¹ : ℂ) *
            (Theta φ i j * R φ x q))) =
      ∑ φ, ∑ θ, ∑ i, ∑ j, ∑ x,
        (m⁻¹ : ℂ) ^ 2 *
          (star (Theta θ i j) * Theta φ i j) *
          (star (R θ x p) * R φ x q) := by
        rw [sum_five_reorder]
        apply Finset.sum_congr rfl
        intro φ _
        apply Finset.sum_congr rfl
        intro θ _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro x _
        simp only [star_mul]
        dsimp [m]
        ring
    _ =
        (m⁻¹ : ℂ) ^ 2 *
        ∑ φ, ∑ θ,
          (∑ i, ∑ j, star (Theta θ i j) * Theta φ i j) *
            (Matrix.conjTranspose (R θ) * R φ) p q := by
      simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
      exact (distribute_five
        ((m⁻¹ : ℂ) ^ 2)
        (fun φ θ i j => star (Theta θ i j) * Theta φ i j)
        (fun φ θ x => star (R θ x p) * R φ x q)).symm
  have htrace : ∀ θ φ,
      (∑ i, ∑ j, star (Theta θ i j) * Theta φ i j) =
        if θ = φ then (Fintype.card a : ℂ) else 0 := by
    intro θ φ
    rw [Finset.sum_comm]
    rw [← trace_conjTranspose_mul_eq_entry_sum]
    rw [(hThetaHermitian θ).eq]
    exact horth θ φ
  simp_rw [htrace]
  rw [diagonal_double_sum]
  simp_rw [(hR _).1]
  simp [m, Matrix.one_apply]
  split <;> field_simp

omit [Nonempty b] in
/-- Orthogonality evaluates the right conditional Gram exactly. -/
theorem orthogonalCorrelationBlocks_rightGram
    (Theta : κ → CMatrix a) (R : κ → CMatrix c)
    (hThetaHermitian : ∀ θ, (Theta θ).IsHermitian)
    (horth : ∀ θ φ,
      (Theta θ * Theta φ).trace =
        if θ = φ then (Fintype.card a : ℂ) else 0)
    (hR : ∀ θ, IsUnitaryMatrix (R θ)) :
    conditionalRightGram (orthogonalCorrelationBlocks Theta R) =
      ((Fintype.card a : ℝ) / (Fintype.card κ : ℝ)) •
        (1 : CMatrix c) := by
  classical
  let m : ℝ := Fintype.card κ
  have hm : m ≠ 0 := by
    apply ne_of_gt
    dsimp [m]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hstar (i j : a) (q x : c) :
      star ((orthogonalCorrelationBlocks Theta R i j) q x) =
        (m⁻¹ : ℂ) * ∑ θ, star (Theta θ i j * R θ q x) := by
    simp [orthogonalCorrelationBlocks, Matrix.sum_apply, Matrix.smul_apply,
      m, star_sum, star_mul, mul_comm]
  ext p q
  simp only [conditionalRightGram, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  simp_rw [hstar]
  simp only [orthogonalCorrelationBlocks, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
      (∑ i, ∑ j, ∑ x, ∑ φ, ∑ θ,
        (m⁻¹ : ℂ) * (Theta θ i j * R θ p x) *
          ((m⁻¹ : ℂ) * star (Theta φ i j * R φ q x))) =
      ∑ φ, ∑ θ, ∑ i, ∑ j, ∑ x,
        (m⁻¹ : ℂ) ^ 2 *
          (star (Theta φ i j) * Theta θ i j) *
          (R θ p x * star (R φ q x)) := by
        rw [sum_five_reorder]
        apply Finset.sum_congr rfl
        intro φ _
        apply Finset.sum_congr rfl
        intro θ _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro x _
        simp only [star_mul]
        ring
    _ =
        (m⁻¹ : ℂ) ^ 2 *
        ∑ φ, ∑ θ,
          (∑ i, ∑ j, star (Theta φ i j) * Theta θ i j) *
            (R θ * Matrix.conjTranspose (R φ)) p q := by
      simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
      exact (distribute_five
        ((m⁻¹ : ℂ) ^ 2)
        (fun φ θ i j => star (Theta φ i j) * Theta θ i j)
        (fun φ θ x => R θ p x * star (R φ q x))).symm
  have htrace : ∀ θ φ,
      (∑ i, ∑ j, star (Theta φ i j) * Theta θ i j) =
        if θ = φ then (Fintype.card a : ℂ) else 0 := by
    intro θ φ
    rw [Finset.sum_comm]
    rw [← trace_conjTranspose_mul_eq_entry_sum]
    rw [(hThetaHermitian φ).eq]
    simpa [eq_comm] using horth φ θ
  simp_rw [htrace]
  rw [diagonal_double_sum]
  simp_rw [(hR _).2]
  simp [m, Matrix.one_apply]
  split <;> field_simp

section PhysicalAttack

universe uh ubob ucharlie

variable {h : Type uh} {bob : Type ubob} {charlie : Type ucharlie}
variable [Fintype h] [DecidableEq h] [Nonempty h]
variable [Fintype bob] [DecidableEq bob] [Nonempty bob]
variable [Fintype charlie] [DecidableEq charlie] [Nonempty charlie]
variable {F : ReflectionFamily κ h}

/-- Bob's decoding reflection on his dilated register. -/
def reflectionAttackBobLocal
    (attack : ReflectionCloningAttack F bob charlie) (θ : κ) :
    CMatrix (ReflectionAttackBobSpace attack) :=
  binaryProjectiveReflection (reflectionAttackBobProjective attack θ)

/-- Charlie's decoding reflection on his dilated register. -/
def reflectionAttackCharlieLocal
    (attack : ReflectionCloningAttack F bob charlie) (θ : κ) :
    CMatrix (ReflectionAttackCharlieSpace attack) :=
  binaryProjectiveReflection (reflectionAttackCharlieProjective attack θ)

theorem reflectionAttackBobLocal_unitary
    (attack : ReflectionCloningAttack F bob charlie) (θ : κ) :
    IsUnitaryMatrix (reflectionAttackBobLocal attack θ) :=
  isUnitaryMatrix_of_hermitian_involution
    (binaryProjectiveReflection_isHermitian
      (reflectionAttackBobProjective attack θ))
    (binaryProjectiveReflection_mul_self
      (reflectionAttackBobProjective attack θ))

theorem reflectionAttackCharlieLocal_unitary
    (attack : ReflectionCloningAttack F bob charlie) (θ : κ) :
    IsUnitaryMatrix (reflectionAttackCharlieLocal attack θ) :=
  isUnitaryMatrix_of_hermitian_involution
    (binaryProjectiveReflection_isHermitian
      (reflectionAttackCharlieProjective attack θ))
    (binaryProjectiveReflection_mul_self
      (reflectionAttackCharlieProjective attack θ))

/-- Tensor-factor form of the fixed-key reference--Bob correlation operator. -/
theorem reflectionAttackGameData_B_eq_local
    (attack : ReflectionCloningAttack F bob charlie) (θ : κ) :
    (reflectionAttackGameData attack).B θ =
      Matrix.transpose (F.Q θ) ⊗ₖ
        (reflectionAttackBobLocal attack θ ⊗ₖ
          (1 : CMatrix (ReflectionAttackCharlieSpace attack))) := by
  change
    ((Matrix.transpose (F.Q θ)) ⊗ₖ
        (1 : CMatrix
          (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack))) *
      ((1 : CMatrix h) ⊗ₖ
        (reflectionAttackBobLocal attack θ ⊗ₖ
          (1 : CMatrix (ReflectionAttackCharlieSpace attack)))) = _
  rw [← Matrix.mul_kronecker_mul]
  simp

/-- Tensor-factor form of the fixed-key reference--Charlie correlation operator. -/
theorem reflectionAttackGameData_C_eq_local
    (attack : ReflectionCloningAttack F bob charlie) (θ : κ) :
    (reflectionAttackGameData attack).C θ =
      Matrix.transpose (F.Q θ) ⊗ₖ
        ((1 : CMatrix (ReflectionAttackBobSpace attack)) ⊗ₖ
          reflectionAttackCharlieLocal attack θ) := by
  change
    ((Matrix.transpose (F.Q θ)) ⊗ₖ
        (1 : CMatrix
          (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack))) *
      ((1 : CMatrix h) ⊗ₖ
        ((1 : CMatrix (ReflectionAttackBobSpace attack)) ⊗ₖ
          reflectionAttackCharlieLocal attack θ)) = _
  rw [← Matrix.mul_kronecker_mul]
  simp

/-- The left conditional lift is exactly the abstract `E_B`. -/
theorem reflectionAttack_conditionalLeftLift_eq_EB
    (attack : ReflectionCloningAttack F bob charlie) :
    conditionalLeftLift
        (orthogonalCorrelationBlocks
          (fun θ => Matrix.transpose (F.Q θ))
          (reflectionAttackBobLocal attack)) =
      (reflectionAttackGameData attack).EB := by
  classical
  ext ⟨i, ⟨p, r⟩⟩ ⟨j, ⟨q, s⟩⟩
  simp [conditionalLeftLift, orthogonalCorrelationBlocks,
    reflectionAttackBobLocal, GameOperatorData.EB, normalizedAverage,
    reflectionAttackGameData_B_eq_local, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- The right conditional lift is exactly the abstract `E_C`. -/
theorem reflectionAttack_conditionalRightLift_eq_EC
    (attack : ReflectionCloningAttack F bob charlie) :
    conditionalRightLift
        (orthogonalCorrelationBlocks
          (fun θ => Matrix.transpose (F.Q θ))
          (reflectionAttackCharlieLocal attack)) =
      (reflectionAttackGameData attack).EC := by
  classical
  ext ⟨i, ⟨p, r⟩⟩ ⟨j, ⟨q, s⟩⟩
  simp [conditionalRightLift, orthogonalCorrelationBlocks,
    reflectionAttackCharlieLocal, GameOperatorData.EC, normalizedAverage,
    reflectionAttackGameData_C_eq_local, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Proof B of Lemma 4.4 for a reflection-family attack. -/
theorem reflectionAttack_EB_mul_EC_norm_le_ananthSahai
    (AS : AnanthSahaiData F)
    (attack : ReflectionCloningAttack F bob charlie) :
    ‖(reflectionAttackGameData attack).EB *
        (reflectionAttackGameData attack).EC‖ ≤
      (Fintype.card h : ℝ) / (Fintype.card κ : ℝ) := by
  let Theta : κ → CMatrix h := fun θ => Matrix.transpose (F.Q θ)
  let U := orthogonalCorrelationBlocks Theta
    (reflectionAttackBobLocal attack)
  let V := orthogonalCorrelationBlocks Theta
    (reflectionAttackCharlieLocal attack)
  have hTheta : ∀ θ, (Theta θ).IsHermitian :=
    fun θ => (F.Q_hermitian θ).transpose
  have hleft :
      conditionalLeftGram U =
        ((Fintype.card h : ℝ) / (Fintype.card κ : ℝ)) •
          (1 : CMatrix (ReflectionAttackBobSpace attack)) :=
    orthogonalCorrelationBlocks_leftGram Theta
      (reflectionAttackBobLocal attack) hTheta AS.orthogonality
      (reflectionAttackBobLocal_unitary attack)
  have hright :
      conditionalRightGram V =
        ((Fintype.card h : ℝ) / (Fintype.card κ : ℝ)) •
          (1 : CMatrix (ReflectionAttackCharlieSpace attack)) :=
    orthogonalCorrelationBlocks_rightGram Theta
      (reflectionAttackCharlieLocal attack) hTheta AS.orthogonality
      (reflectionAttackCharlieLocal_unitary attack)
  have hoverlap := conditionalOverlap
    (c := ReflectionAttackCharlieSpace attack) U V
  rw [reflectionAttack_conditionalLeftLift_eq_EB,
    reflectionAttack_conditionalRightLift_eq_EC, hleft, hright] at hoverlap
  have hratio :
      0 ≤ (Fintype.card h : ℝ) / (Fintype.card κ : ℝ) := by positivity
  have hleftNorm :
      ‖((Fintype.card h : ℝ) / (Fintype.card κ : ℝ)) •
          (1 : CMatrix (ReflectionAttackBobSpace attack))‖ =
        (Fintype.card h : ℝ) / (Fintype.card κ : ℝ) := by
    simp [norm_smul]
  have hrightNorm :
      ‖((Fintype.card h : ℝ) / (Fintype.card κ : ℝ)) •
          (1 : CMatrix (ReflectionAttackCharlieSpace attack))‖ =
        (Fintype.card h : ℝ) / (Fintype.card κ : ℝ) := by
    simp [norm_smul]
  rw [hleftNorm, hrightNorm] at hoverlap
  calc
    ‖(reflectionAttackGameData attack).EB *
        (reflectionAttackGameData attack).EC‖ ≤
        Real.sqrt ((Fintype.card h : ℝ) / (Fintype.card κ : ℝ)) *
          Real.sqrt ((Fintype.card h : ℝ) / (Fintype.card κ : ℝ)) :=
      hoverlap
    _ = (Fintype.card h : ℝ) / (Fintype.card κ : ℝ) :=
      Real.mul_self_sqrt hratio

end PhysicalAttack

end

end UE.PauliConstructionAndProof
