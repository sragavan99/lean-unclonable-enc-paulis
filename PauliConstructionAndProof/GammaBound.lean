import PauliConstructionAndProof.AttackGame
import PauliConstructionAndProof.MatrixInfrastructure

/-!
# The generic Gamma block-factorization bound

The proof is the dimension-free block factorization
`S_B S_C = M⁻² M_C (Gamma ⊗ I) M_B`.  The amplification norm is exact,
and both outer block matrices have norm `sqrt M`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh ub uc

/-- Exact block factorization of a signed double sum.  The row index of
`Gamma` is `φ` and its column index is `θ`. -/
theorem signedDoubleSum_eq_blockFactorization
    {κ : Type uκ} {h : Type uh}
    [Fintype κ] [Fintype h] [DecidableEq h]
    (Gamma : CMatrix κ) (U V : κ → CMatrix h)
    (hcomm : ∀ θ φ, U θ * V φ = Gamma φ θ • (V φ * U θ)) :
    (∑ θ, ∑ φ, U θ * V φ) =
      (matrixFamilyBlockRow V * Matrix.kronecker Gamma (1 : CMatrix h)) *
        matrixFamilyBlockColumn U := by
  classical
  calc
    (∑ θ, ∑ φ, U θ * V φ) =
        ∑ θ, ∑ φ, Gamma φ θ • (V φ * U θ) := by
      apply Finset.sum_congr rfl
      intro θ _
      apply Finset.sum_congr rfl
      intro φ _
      exact hcomm θ φ
    _ = ∑ φ, ∑ θ, Gamma φ θ • (V φ * U θ) := by
      rw [Finset.sum_comm]
    _ = (matrixFamilyBlockRow V * Matrix.kronecker Gamma (1 : CMatrix h)) *
        matrixFamilyBlockColumn U := by
      ext i j
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
        matrixFamilyBlockRow, matrixFamilyBlockColumn, Fintype.sum_prod_type,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
        smul_eq_mul]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_pos]
      calc
        (∑ φ, ∑ θ, Gamma φ θ * ∑ k, V φ i k * U θ k j) =
            ∑ φ, ∑ θ, ∑ k,
              Gamma φ θ * (V φ i k * U θ k j) := by
          simp_rw [Finset.mul_sum]
        _ = ∑ θ, ∑ k, ∑ φ,
              (V φ i k * Gamma φ θ) * U θ k j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro θ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro φ _
          ring
        _ = ∑ θ, ∑ k,
              (∑ φ, V φ i k * Gamma φ θ) * U θ k j := by
          simp_rw [Finset.sum_mul]

variable {κ : Type uκ} {h : Type uh}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype h] [DecidableEq h] [Nonempty h]

/-- Norm bound obtained from the exact generic block factorization. -/
theorem normalizedSignedDoubleSum_norm_le
    (Gamma : CMatrix κ) (U V : κ → CMatrix h)
    (hU : ∀ θ, IsUnitaryMatrix (U θ))
    (hV : ∀ θ, IsUnitaryMatrix (V θ))
    (hcomm : ∀ θ φ, U θ * V φ = Gamma φ θ • (V φ * U θ)) :
    ‖((Fintype.card κ : ℝ)⁻¹ ^ 2) •
        ∑ θ, ∑ φ, U θ * V φ‖ ≤
      ‖Gamma‖ / (Fintype.card κ : ℝ) := by
  classical
  let m : ℝ := Fintype.card κ
  have hmpos : 0 < m := by
    dsimp [m]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hmne : m ≠ 0 := ne_of_gt hmpos
  rw [signedDoubleSum_eq_blockFactorization Gamma U V hcomm, norm_smul]
  have hscalar : ‖m⁻¹ ^ 2‖ = m⁻¹ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hscalar]
  calc
    m⁻¹ ^ 2 *
        ‖(matrixFamilyBlockRow V * Matrix.kronecker Gamma (1 : CMatrix h)) *
          matrixFamilyBlockColumn U‖ ≤
      m⁻¹ ^ 2 *
        (‖matrixFamilyBlockRow V * Matrix.kronecker Gamma (1 : CMatrix h)‖ *
          ‖matrixFamilyBlockColumn U‖) := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
    _ ≤ m⁻¹ ^ 2 *
        ((‖matrixFamilyBlockRow V‖ *
          ‖Matrix.kronecker Gamma (1 : CMatrix h)‖) *
          ‖matrixFamilyBlockColumn U‖) := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
    _ = m⁻¹ ^ 2 *
        ((Real.sqrt m * ‖Gamma‖) * Real.sqrt m) := by
      rw [matrixFamilyBlockRow_norm V hV,
        matrixFamilyBlockColumn_norm U hU,
        matrixAmplification_norm κ h Gamma]
    _ = ‖Gamma‖ / m := by
      have hsqrt : Real.sqrt m * Real.sqrt m = m := by
        nlinarith [Real.sq_sqrt hmpos.le]
      rw [show (Real.sqrt m * ‖Gamma‖) * Real.sqrt m =
          ‖Gamma‖ * (Real.sqrt m * Real.sqrt m) by ring, hsqrt]
      field_simp

variable (G : GameOperatorData κ h) (Gamma : CMatrix κ)

/-- The `B_θ,C_φ` product inherits the reversed-index Gamma relation. -/
theorem game_B_mul_C_commutation
    (hQQ : ∀ θ φ, G.Q θ * G.Q φ = Gamma φ θ • (G.Q φ * G.Q θ))
    (θ φ : κ) :
    G.B θ * G.C φ = Gamma φ θ • (G.C φ * G.B θ) := by
  simp only [GameOperatorData.B, GameOperatorData.C]
  calc
    (G.Q θ * G.b θ) * (G.Q φ * G.c φ) =
        (G.Q θ * G.Q φ) * (G.b θ * G.c φ) := by
      calc
        (G.Q θ * G.b θ) * (G.Q φ * G.c φ) =
            G.Q θ * (G.b θ * G.Q φ) * G.c φ := by
              simp [Matrix.mul_assoc]
        _ = G.Q θ * (G.Q φ * G.b θ) * G.c φ := by
              rw [← G.Q_comm_b φ θ]
        _ = (G.Q θ * G.Q φ) * (G.b θ * G.c φ) := by
              simp [Matrix.mul_assoc]
    _ = (Gamma φ θ • (G.Q φ * G.Q θ)) *
        (G.b θ * G.c φ) := by rw [hQQ]
    _ = Gamma φ θ •
        ((G.Q φ * G.c φ) * (G.Q θ * G.b θ)) := by
      rw [Matrix.smul_mul]
      congr 1
      calc
        (G.Q φ * G.Q θ) * (G.b θ * G.c φ) =
            G.Q φ * (G.Q θ * G.b θ) * G.c φ := by
              simp [Matrix.mul_assoc]
        _ = G.Q φ * (G.b θ * G.Q θ) * G.c φ := by
              rw [G.Q_comm_b θ θ]
        _ = G.Q φ * G.b θ * (G.Q θ * G.c φ) := by
              simp [Matrix.mul_assoc]
        _ = G.Q φ * G.b θ * (G.c φ * G.Q θ) := by
              rw [G.Q_comm_c θ φ]
        _ = G.Q φ * (G.b θ * G.c φ) * G.Q θ := by
              simp [Matrix.mul_assoc]
        _ = G.Q φ * (G.c φ * G.b θ) * G.Q θ := by
              rw [G.b_comm_c θ φ]
        _ = (G.Q φ * G.c φ) * (G.b θ * G.Q θ) := by
              simp [Matrix.mul_assoc]
        _ = (G.Q φ * G.c φ) * (G.Q θ * G.b θ) := by
              rw [← G.Q_comm_b θ θ]

/-- Abstract `S_B S_C` estimate with no dimension-losing triangle bound. -/
theorem game_SB_mul_SC_norm_le
    (hQQ : ∀ θ φ, G.Q θ * G.Q φ = Gamma φ θ • (G.Q φ * G.Q θ)) :
    ‖G.SB * G.SC‖ ≤ ‖Gamma‖ / (Fintype.card κ : ℝ) := by
  have hB : ∀ θ, IsUnitaryMatrix (G.B θ) := fun θ =>
    isUnitaryMatrix_of_hermitian_involution (G.B_isHermitian θ) (G.B_mul_self θ)
  have hC : ∀ θ, IsUnitaryMatrix (G.C θ) := fun θ =>
    isUnitaryMatrix_of_hermitian_involution (G.C_isHermitian θ) (G.C_mul_self θ)
  have hbound := normalizedSignedDoubleSum_norm_le Gamma G.B G.C hB hC
    (game_B_mul_C_commutation G Gamma hQQ)
  have heq :
      G.SB * G.SC =
        ((Fintype.card κ : ℝ)⁻¹ ^ 2) •
          ∑ θ, ∑ φ, G.B θ * G.C φ := by
    simp only [GameOperatorData.SB, GameOperatorData.SC, normalizedAverage,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Matrix.sum_mul]
    simp_rw [Matrix.mul_sum]
    rw [pow_two]
  rw [heq]
  exact hbound

variable {bob : Type ub} {charlie : Type uc}
variable [Fintype bob] [DecidableEq bob] [Nonempty bob]
variable [Fintype charlie] [DecidableEq charlie] [Nonempty charlie]
variable {F : ReflectionFamily κ h}

/-- Concrete generic-attack instance of the abstract Gamma estimate. -/
theorem reflectionAttack_SB_mul_SC_norm_le
    (attack : ReflectionCloningAttack F bob charlie) :
    ‖(reflectionAttackGameData attack).SB * (reflectionAttackGameData attack).SC‖ ≤
      ‖F.Gamma‖ / (Fintype.card κ : ℝ) := by
  apply game_SB_mul_SC_norm_le (reflectionAttackGameData attack) F.Gamma
  exact reflectionAttackAlice_commutation attack

end

end UE.PauliConstructionAndProof
