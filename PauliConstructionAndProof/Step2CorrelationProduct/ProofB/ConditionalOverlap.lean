import PauliConstructionAndProof.MatrixInfrastructure

/-!
# §4.2.2: conditional overlap

Lemma 4.5 uses the reference-indexed blocks of operators on `A ⊗ B`
and `A ⊗ C`.
The matrices `conditionalLeftGram` and `conditionalRightGram` are exactly the
partial traces over `A` of `U†U` and `VV†`, respectively.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe ua ub uc

variable {a : Type ua} {b : Type ub} {c : Type uc}
variable [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Nonempty b]
variable [Fintype c] [DecidableEq c] [Nonempty c]

/-- Canonical embedding of an operator on `B` into `A ⊗ B ⊗ C`. -/
def conditionalLiftB (X : CMatrix b) : CMatrix (a × (b × c)) :=
  (1 : CMatrix a) ⊗ₖ (X ⊗ₖ (1 : CMatrix c))

/-- Canonical embedding of an operator on `C` into `A ⊗ B ⊗ C`. -/
def conditionalLiftC (X : CMatrix c) : CMatrix (a × (b × c)) :=
  (1 : CMatrix a) ⊗ₖ ((1 : CMatrix b) ⊗ₖ X)

/-- Lift the reference-indexed blocks of an operator on `A ⊗ B`. -/
def conditionalLeftLift (U : a → a → CMatrix b) :
    CMatrix (a × (b × c)) :=
  fun ⟨i, ⟨p, r⟩⟩ ⟨j, ⟨q, s⟩⟩ =>
    U i j p q * if r = s then 1 else 0

/-- Lift the reference-indexed blocks of an operator on `A ⊗ C`. -/
def conditionalRightLift (V : a → a → CMatrix c) :
    CMatrix (a × (b × c)) :=
  fun ⟨i, ⟨p, r⟩⟩ ⟨j, ⟨q, s⟩⟩ =>
    (if p = q then 1 else 0) * V i j r s

/-- Partial trace over `A` of `U†U`, expressed in blocks. -/
def conditionalLeftGram (U : a → a → CMatrix b) : CMatrix b :=
  ∑ i, ∑ j, Matrix.conjTranspose (U i j) * U i j

/-- Partial trace over `A` of `VV†`, expressed in blocks. -/
def conditionalRightGram (V : a → a → CMatrix c) : CMatrix c :=
  ∑ j, ∑ k, V j k * Matrix.conjTranspose (V j k)

/-- The regrouped `T_{j,k}` blocks from the conditional-overlap proof. -/
def conditionalT (U : a → a → CMatrix b) (j k : a) :
    CMatrix (a × (b × c)) :=
  fun ⟨i, ⟨p, r⟩⟩ ⟨l, ⟨q, s⟩⟩ =>
    (if l = k then 1 else 0) * U i j p q * if r = s then 1 else 0

omit [Nonempty a] [Nonempty b] [Nonempty c] in
theorem conditionalLiftC_mul_conditionalT_comm
    (U : a → a → CMatrix b) (V : a → a → CMatrix c) (j k : a) :
    conditionalLiftC (V j k) * conditionalT U j k =
      conditionalT U j k * conditionalLiftC (V j k) := by
  classical
  ext ⟨i, ⟨p, r⟩⟩ ⟨l, ⟨q, s⟩⟩
  simp [conditionalLiftC, conditionalT, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_comm]

omit [Nonempty a] [Nonempty b] [Nonempty c] in
/-- Exact block regrouping of the product of the two canonical lifts. -/
theorem conditionalLift_product_eq
    (U : a → a → CMatrix b) (V : a → a → CMatrix c) :
    conditionalLeftLift U * conditionalRightLift V =
      ∑ jk : a × a,
        conditionalT U jk.1 jk.2 * conditionalLiftC (V jk.1 jk.2) := by
  classical
  ext ⟨i, ⟨p, r⟩⟩ ⟨k, ⟨q, s⟩⟩
  simp [conditionalLeftLift, conditionalRightLift, conditionalT,
    conditionalLiftC, Matrix.sum_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]

omit [Nonempty a] [Nonempty b] [Nonempty c] in
/-- The `T`-column Gram matrix is the lifted left partial-trace Gram. -/
theorem conditionalT_gram_sum
    (U : a → a → CMatrix b) :
    ∑ jk : a × a,
        Matrix.conjTranspose
            (conditionalT (a := a) (c := c) U jk.1 jk.2) *
          conditionalT (a := a) (c := c) U jk.1 jk.2 =
      conditionalLiftB (a := a) (c := c) (conditionalLeftGram U) := by
  classical
  ext ⟨k, ⟨p, r⟩⟩ ⟨l, ⟨q, s⟩⟩
  simp only [conditionalT, conditionalLiftB, conditionalLeftGram,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  by_cases hkl : k = l <;> by_cases hrs : r = s
  · subst l
    subst s
    simp
    rw [Finset.sum_comm]
  · simp [hkl, hrs, eq_comm]
  · simp [hkl, hrs, eq_comm]
  · simp [hkl, hrs, eq_comm]

omit [Nonempty a] [Nonempty b] [Nonempty c] in
theorem conditionalLiftC_conjTranspose (X : CMatrix c) :
    Matrix.conjTranspose (conditionalLiftC (a := a) (b := b) X) =
      conditionalLiftC (a := a) (b := b) (Matrix.conjTranspose X) := by
  unfold conditionalLiftC
  calc
    Matrix.conjTranspose
        ((1 : CMatrix a) ⊗ₖ ((1 : CMatrix b) ⊗ₖ X)) =
      Matrix.conjTranspose (1 : CMatrix a) ⊗ₖ
        Matrix.conjTranspose ((1 : CMatrix b) ⊗ₖ X) :=
      Matrix.conjTranspose_kronecker _ _
    _ = (1 : CMatrix a) ⊗ₖ
        (Matrix.conjTranspose (1 : CMatrix b) ⊗ₖ
          Matrix.conjTranspose X) := by
      rw [Matrix.conjTranspose_one, Matrix.conjTranspose_kronecker]
    _ = (1 : CMatrix a) ⊗ₖ ((1 : CMatrix b) ⊗ₖ
        Matrix.conjTranspose X) := by rw [Matrix.conjTranspose_one]

omit [Nonempty a] [Nonempty b] [Nonempty c] in
theorem conditionalLiftC_mul (X Y : CMatrix c) :
    conditionalLiftC (a := a) (b := b) X *
        conditionalLiftC (a := a) (b := b) Y =
      conditionalLiftC (a := a) (b := b) (X * Y) := by
  simp [conditionalLiftC, ← Matrix.mul_kronecker_mul]

omit [Nonempty a] [Nonempty b] [Nonempty c] in
theorem conditionalLiftC_sum (f : a × a → CMatrix c) :
    (∑ jk, conditionalLiftC (a := a) (b := b) (f jk)) =
      conditionalLiftC (a := a) (b := b) (∑ jk, f jk) := by
  classical
  ext ⟨i, ⟨p, r⟩⟩ ⟨j, ⟨q, s⟩⟩
  simp [conditionalLiftC, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply]

omit [Nonempty a] [Nonempty b] [Nonempty c] in
/-- The column made from `V†` has the lifted right partial-trace Gram. -/
theorem conditionalCColumn_gram_sum
    (V : a → a → CMatrix c) :
    ∑ jk : a × a,
        Matrix.conjTranspose
            (conditionalLiftC (a := a) (b := b)
              (Matrix.conjTranspose (V jk.1 jk.2))) *
          conditionalLiftC (a := a) (b := b)
            (Matrix.conjTranspose (V jk.1 jk.2)) =
      conditionalLiftC (a := a) (b := b) (conditionalRightGram V) := by
  classical
  simp_rw [conditionalLiftC_conjTranspose,
    Matrix.conjTranspose_conjTranspose, conditionalLiftC_mul]
  rw [conditionalLiftC_sum]
  simp [conditionalRightGram, Fintype.sum_prod_type]

/-- Amplifying a `B`-operator by both spectator identities preserves norm. -/
theorem conditionalLiftB_norm (X : CMatrix b) :
    ‖conditionalLiftB (a := a) (c := c) X‖ = ‖X‖ := by
  change ‖(1 : CMatrix a) ⊗ₖ (X ⊗ₖ (1 : CMatrix c))‖ = ‖X‖
  calc
    ‖(1 : CMatrix a) ⊗ₖ (X ⊗ₖ (1 : CMatrix c))‖ =
        ‖X ⊗ₖ (1 : CMatrix c)‖ :=
      matrixIdentityTensor_norm a (b × c) _
    _ = ‖X‖ := matrixAmplification_norm b c X

/-- Amplifying a `C`-operator by both spectator identities preserves norm. -/
theorem conditionalLiftC_norm (X : CMatrix c) :
    ‖conditionalLiftC (a := a) (b := b) X‖ = ‖X‖ := by
  change ‖(1 : CMatrix a) ⊗ₖ ((1 : CMatrix b) ⊗ₖ X)‖ = ‖X‖
  calc
    ‖(1 : CMatrix a) ⊗ₖ ((1 : CMatrix b) ⊗ₖ X)‖ =
        ‖(1 : CMatrix b) ⊗ₖ X‖ :=
      matrixIdentityTensor_norm a (b × c) _
    _ = ‖X‖ := matrixIdentityTensor_norm b c X

/-- Lemma 4.5 in block form, with the conditional Grams as partial traces. -/
theorem conditionalOverlap
    (U : a → a → CMatrix b) (V : a → a → CMatrix c) :
    ‖conditionalLeftLift U * conditionalRightLift V‖ ≤
      Real.sqrt ‖conditionalLeftGram U‖ *
        Real.sqrt ‖conditionalRightGram V‖ := by
  let A : a × a → CMatrix (a × (b × c)) := fun jk =>
    conditionalLiftC (Matrix.conjTranspose (V jk.1 jk.2))
  let B : a × a → CMatrix (a × (b × c)) := fun jk =>
    conditionalT U jk.1 jk.2
  have hfactor :
      conditionalLeftLift U * conditionalRightLift V =
        Matrix.conjTranspose (matrixFamilyBlockColumn A) *
          matrixFamilyBlockColumn B := by
    rw [conditionalLift_product_eq]
    rw [matrixFamilyBlockColumn_conjTranspose_mul_cross]
    apply Finset.sum_congr rfl
    intro jk _
    change
      conditionalT U jk.1 jk.2 * conditionalLiftC (V jk.1 jk.2) =
        Matrix.conjTranspose
            (conditionalLiftC (Matrix.conjTranspose (V jk.1 jk.2))) *
          conditionalT U jk.1 jk.2
    rw [conditionalLiftC_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact (conditionalLiftC_mul_conditionalT_comm U V jk.1 jk.2).symm
  rw [hfactor]
  calc
    ‖Matrix.conjTranspose (matrixFamilyBlockColumn A) *
        matrixFamilyBlockColumn B‖ ≤
      ‖Matrix.conjTranspose (matrixFamilyBlockColumn A)‖ *
        ‖matrixFamilyBlockColumn B‖ :=
      Matrix.l2_opNorm_mul _ _
    _ = ‖matrixFamilyBlockColumn A‖ * ‖matrixFamilyBlockColumn B‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]
    _ = Real.sqrt ‖conditionalRightGram V‖ *
        Real.sqrt ‖conditionalLeftGram U‖ := by
      rw [matrixFamilyBlockColumn_norm_general A,
        matrixFamilyBlockColumn_norm_general B]
      change
        Real.sqrt ‖∑ jk : a × a,
            Matrix.conjTranspose
                (conditionalLiftC (Matrix.conjTranspose (V jk.1 jk.2))) *
              conditionalLiftC (Matrix.conjTranspose (V jk.1 jk.2))‖ *
          Real.sqrt ‖∑ jk : a × a,
            Matrix.conjTranspose (conditionalT U jk.1 jk.2) *
              conditionalT U jk.1 jk.2‖ =
        _
      rw [conditionalCColumn_gram_sum, conditionalT_gram_sum,
        conditionalLiftC_norm, conditionalLiftB_norm]
    _ = Real.sqrt ‖conditionalLeftGram U‖ *
        Real.sqrt ‖conditionalRightGram V‖ := mul_comm _ _

end

end UE.PauliConstructionAndProof
