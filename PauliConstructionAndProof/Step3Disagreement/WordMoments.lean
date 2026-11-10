import PauliConstructionAndProof.GameOperator
import PauliConstructionAndProof.MatrixInfrastructure

/-!
# §4.3: inserting powers of the agreement operator

The proof of Proposition 4.6 expands powers of `EBC` as finite averages of
ordered words.
Moving the factors on disjoint registers preserves each receiver's order.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh

/-- Matrix product in exactly the displayed list order. -/
def orderedMatrixProduct {κ : Type uκ} {h : Type uh}
    [Fintype h] [DecidableEq h] (f : κ → CMatrix h) : List κ → CMatrix h
  | [] => 1
  | θ :: word => f θ * orderedMatrixProduct f word

@[simp]
theorem orderedMatrixProduct_nil
    {κ : Type uκ} {h : Type uh} [Fintype h] [DecidableEq h]
    (f : κ → CMatrix h) : orderedMatrixProduct f [] = 1 := rfl

@[simp]
theorem orderedMatrixProduct_cons
    {κ : Type uκ} {h : Type uh} [Fintype h] [DecidableEq h]
    (f : κ → CMatrix h) (θ : κ) (word : List κ) :
    orderedMatrixProduct f (θ :: word) = f θ * orderedMatrixProduct f word := rfl

theorem orderedMatrixProduct_unitary
    {κ : Type uκ} {h : Type uh} [Fintype h] [DecidableEq h]
    (f : κ → CMatrix h) (hf : ∀ θ, IsUnitaryMatrix (f θ))
    (word : List κ) : IsUnitaryMatrix (orderedMatrixProduct f word) := by
  induction word with
  | nil => exact isUnitaryMatrix_one
  | cons θ word ih => exact (hf θ).mul ih

/-- A left-family element commutes through a right-family ordered word when
all cross-family pairs commute. -/
theorem commute_orderedMatrixProduct_right
    {κ : Type uκ} {h : Type uh} [Fintype h] [DecidableEq h]
    (f g : κ → CMatrix h)
    (hfg : ∀ θ φ, f θ * g φ = g φ * f θ)
    (θ : κ) (word : List κ) :
    f θ * orderedMatrixProduct g word = orderedMatrixProduct g word * f θ := by
  induction word with
  | nil => simp
  | cons φ word ih =>
      calc
        f θ * (g φ * orderedMatrixProduct g word) =
            (f θ * g φ) * orderedMatrixProduct g word := by
              simp [Matrix.mul_assoc]
        _ = (g φ * f θ) * orderedMatrixProduct g word := by rw [hfg]
        _ = g φ * (orderedMatrixProduct g word * f θ) := by
              rw [← ih]
              simp [Matrix.mul_assoc]
        _ = orderedMatrixProduct g (φ :: word) * f θ := by
              simp only [orderedMatrixProduct_cons, Matrix.mul_assoc]

/-- Two ordered words commute using cross-family commutation only. -/
theorem orderedMatrixProducts_commute
    {κ : Type uκ} {h : Type uh} [Fintype h] [DecidableEq h]
    (f g : κ → CMatrix h)
    (hfg : ∀ θ φ, f θ * g φ = g φ * f θ)
    (left right : List κ) :
    orderedMatrixProduct f left * orderedMatrixProduct g right =
      orderedMatrixProduct g right * orderedMatrixProduct f left := by
  induction left with
  | nil => simp
  | cons θ left ih =>
      have hθ := commute_orderedMatrixProduct_right f g hfg θ right
      calc
        (f θ * orderedMatrixProduct f left) * orderedMatrixProduct g right =
            f θ * (orderedMatrixProduct g right * orderedMatrixProduct f left) := by
              rw [← ih]
              simp [Matrix.mul_assoc]
        _ = (orderedMatrixProduct g right * f θ) *
            orderedMatrixProduct f left := by rw [← Matrix.mul_assoc, hθ]
        _ = orderedMatrixProduct g right *
            (f θ * orderedMatrixProduct f left) := by simp [Matrix.mul_assoc]

/-- Ordered products of pointwise products split without changing either
receiver's internal order. -/
theorem orderedMatrixProduct_pointwise_mul
    {κ : Type uκ} {h : Type uh} [Fintype h] [DecidableEq h]
    (f g : κ → CMatrix h)
    (hfg : ∀ θ φ, f θ * g φ = g φ * f θ)
    (word : List κ) :
    orderedMatrixProduct (fun θ => f θ * g θ) word =
      orderedMatrixProduct f word * orderedMatrixProduct g word := by
  induction word with
  | nil => simp
  | cons θ word ih =>
      have hcross := commute_orderedMatrixProduct_right g f
        (fun φ ψ => (hfg ψ φ).symm) θ word
      rw [orderedMatrixProduct_cons, ih, orderedMatrixProduct_cons,
        orderedMatrixProduct_cons]
      calc
        (f θ * g θ) *
            (orderedMatrixProduct f word * orderedMatrixProduct g word) =
          f θ * (g θ * orderedMatrixProduct f word) *
            orderedMatrixProduct g word := by simp [Matrix.mul_assoc]
        _ = f θ * (orderedMatrixProduct f word * g θ) *
            orderedMatrixProduct g word := by rw [hcross]
        _ = (f θ * orderedMatrixProduct f word) *
            (g θ * orderedMatrixProduct g word) := by simp [Matrix.mul_assoc]

variable {κ : Type uκ} {h : Type uh}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype h] [DecidableEq h] [Nonempty h]
variable (G : GameOperatorData κ h)

def gameBobWord (word : List κ) : CMatrix h := orderedMatrixProduct G.b word
def gameCharlieWord (word : List κ) : CMatrix h := orderedMatrixProduct G.c word
def gameAgreementWord (word : List κ) : CMatrix h :=
  orderedMatrixProduct (fun θ => G.b θ * G.c θ) word

theorem gameAgreementWord_eq_bobWord_mul_charlieWord (word : List κ) :
    gameAgreementWord G word = gameBobWord G word * gameCharlieWord G word :=
  orderedMatrixProduct_pointwise_mul G.b G.c G.b_comm_c word

theorem gameBobWord_unitary (word : List κ) :
    IsUnitaryMatrix (gameBobWord G word) :=
  orderedMatrixProduct_unitary G.b
    (fun θ => isUnitaryMatrix_of_hermitian_involution
      (G.b_hermitian θ) (G.b_involution θ)) word

theorem gameCharlieWord_unitary (word : List κ) :
    IsUnitaryMatrix (gameCharlieWord G word) :=
  orderedMatrixProduct_unitary G.c
    (fun θ => isUnitaryMatrix_of_hermitian_involution
      (G.c_hermitian θ) (G.c_involution θ)) word

theorem game_B_comm_c (θ φ : κ) : G.B θ * G.c φ = G.c φ * G.B θ := by
  simp only [GameOperatorData.B]
  calc
    (G.Q θ * G.b θ) * G.c φ = G.Q θ * (G.b θ * G.c φ) := by
      simp [Matrix.mul_assoc]
    _ = G.Q θ * (G.c φ * G.b θ) := by rw [G.b_comm_c]
    _ = (G.Q θ * G.c φ) * G.b θ := by simp [Matrix.mul_assoc]
    _ = (G.c φ * G.Q θ) * G.b θ := by rw [G.Q_comm_c]
    _ = G.c φ * (G.Q θ * G.b θ) := by simp [Matrix.mul_assoc]

theorem game_b_comm_C (θ φ : κ) : G.b θ * G.C φ = G.C φ * G.b θ := by
  simp only [GameOperatorData.C]
  calc
    G.b θ * (G.Q φ * G.c φ) = (G.b θ * G.Q φ) * G.c φ := by
      simp [Matrix.mul_assoc]
    _ = (G.Q φ * G.b θ) * G.c φ := by rw [← G.Q_comm_b]
    _ = G.Q φ * (G.b θ * G.c φ) := by simp [Matrix.mul_assoc]
    _ = G.Q φ * (G.c φ * G.b θ) := by rw [G.b_comm_c]
    _ = (G.Q φ * G.c φ) * G.b θ := by simp [Matrix.mul_assoc]

theorem game_EB_comm_charlieWord (word : List κ) :
    G.EB * gameCharlieWord G word = gameCharlieWord G word * G.EB := by
  rw [GameOperatorData.EB, normalizedAverage]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  exact commute_orderedMatrixProduct_right G.B G.c (game_B_comm_c G) θ word

theorem game_bobWord_comm_EC (word : List κ) :
    gameBobWord G word * G.EC = G.EC * gameBobWord G word := by
  rw [GameOperatorData.EC, normalizedAverage]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro φ _
  exact (commute_orderedMatrixProduct_right G.C G.b
    (fun φ θ => (game_b_comm_C G θ φ).symm) φ word).symm

/-- The ordered-word identity in the expansion of equation (32). -/
theorem game_word_sandwich_identity (word : List κ) :
    G.EB * gameBobWord G word * gameCharlieWord G word * G.EC =
      gameCharlieWord G word * (G.EB * G.EC) * gameBobWord G word := by
  have hBC := orderedMatrixProducts_commute G.b G.c G.b_comm_c word word
  have hSB := game_EB_comm_charlieWord G word
  have hSC := game_bobWord_comm_EC G word
  have hBC' : gameBobWord G word * gameCharlieWord G word =
      gameCharlieWord G word * gameBobWord G word := by
    simpa [gameBobWord, gameCharlieWord] using hBC
  calc
    G.EB * gameBobWord G word * gameCharlieWord G word * G.EC =
        G.EB * (gameBobWord G word * gameCharlieWord G word) * G.EC := by
          simp [Matrix.mul_assoc]
    _ = G.EB * (gameCharlieWord G word * gameBobWord G word) * G.EC := by
          rw [hBC']
    _ = (G.EB * gameCharlieWord G word) * gameBobWord G word * G.EC := by
          simp [Matrix.mul_assoc]
    _ = (gameCharlieWord G word * G.EB) * gameBobWord G word * G.EC := by
          rw [hSB]
    _ = gameCharlieWord G word * G.EB * (gameBobWord G word * G.EC) := by
          simp [Matrix.mul_assoc]
    _ = gameCharlieWord G word * G.EB * (G.EC * gameBobWord G word) := by
          rw [hSC]
    _ = gameCharlieWord G word * (G.EB * G.EC) * gameBobWord G word := by
          simp [Matrix.mul_assoc]

/-- Every ordered word has the same norm bound as `E_B E_C`. -/
theorem game_word_sandwich_norm_le {epsilon : ℝ}
    (hbase : ‖G.EB * G.EC‖ ≤ epsilon) (word : List κ) :
    ‖G.EB * gameBobWord G word * gameCharlieWord G word * G.EC‖ ≤ epsilon := by
  rw [game_word_sandwich_identity G word]
  have hB := gameBobWord_unitary G word
  have hC := gameCharlieWord_unitary G word
  have hBmem : gameBobWord G word ∈ unitary (CMatrix h) := by
    simpa [Unitary.mem_iff, Matrix.star_eq_conjTranspose] using hB
  have hCmem : gameCharlieWord G word ∈ unitary (CMatrix h) := by
    simpa [Unitary.mem_iff, Matrix.star_eq_conjTranspose] using hC
  rw [CStarRing.norm_mul_mem_unitary _ hBmem,
    CStarRing.norm_mem_unitary_mul _ hCmem]
  exact hbase

/-! ## Finite word averages and powers -/

def normalizedWordAverage (f : κ → CMatrix h) : ℕ → CMatrix h
  | 0 => 1
  | ℓ + 1 => normalizedAverage (fun θ => f θ * normalizedWordAverage f ℓ)

theorem normalizedAverage_mul_right (f : κ → CMatrix h) (A : CMatrix h) :
    normalizedAverage (fun θ => f θ * A) = normalizedAverage f * A := by
  classical
  simp [normalizedAverage, Finset.sum_mul]

theorem mul_normalizedAverage (A : CMatrix h) (f : κ → CMatrix h) :
    A * normalizedAverage f = normalizedAverage (fun θ => A * f θ) := by
  classical
  simp [normalizedAverage, Matrix.mul_sum]

theorem normalizedAverage_norm_le {A : κ → CMatrix h} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hA : ∀ θ, ‖A θ‖ ≤ epsilon) :
    ‖normalizedAverage A‖ ≤ epsilon := by
  classical
  have hcard : (0 : ℝ) < Fintype.card κ := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hsum : ‖∑ θ, A θ‖ ≤ ∑ _θ : κ, epsilon := by
    simpa using norm_sum_le_of_le (Finset.univ : Finset κ) (fun θ _ => hA θ)
  rw [normalizedAverage, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hcard)]
  calc
    (Fintype.card κ : ℝ)⁻¹ * ‖∑ θ, A θ‖ ≤
        (Fintype.card κ : ℝ)⁻¹ * ∑ _θ : κ, epsilon :=
      mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hcard).le
    _ = epsilon := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

theorem normalizedWordAverage_eq_pow (f : κ → CMatrix h) (ℓ : ℕ) :
    normalizedWordAverage f ℓ = (normalizedAverage f) ^ ℓ := by
  induction ℓ with
  | zero => simp [normalizedWordAverage]
  | succ ℓ ih =>
      rw [normalizedWordAverage, ih, normalizedAverage_mul_right, pow_succ']

theorem orderedMatrixProduct_append_singleton
    (f : κ → CMatrix h) (acc : List κ) (θ : κ) :
    orderedMatrixProduct f (acc ++ [θ]) = orderedMatrixProduct f acc * f θ := by
  induction acc with
  | nil => simp
  | cons φ acc ih =>
      simp only [List.cons_append, orderedMatrixProduct_cons, ih, Matrix.mul_assoc]

theorem orderedWord_normalizedWordAverage_norm_le
    (f : κ → CMatrix h) (L R : CMatrix h) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hword : ∀ word : List κ, ‖L * orderedMatrixProduct f word * R‖ ≤ epsilon)
    (acc : List κ) (ℓ : ℕ) :
    ‖L * (orderedMatrixProduct f acc * normalizedWordAverage f ℓ) * R‖ ≤ epsilon := by
  induction ℓ generalizing acc with
  | zero => simpa [normalizedWordAverage, Matrix.mul_assoc] using hword acc
  | succ ℓ ih =>
      rw [normalizedWordAverage]
      have havg :
          L * (orderedMatrixProduct f acc *
              normalizedAverage (fun θ => f θ * normalizedWordAverage f ℓ)) * R =
            normalizedAverage (fun θ =>
              L * (orderedMatrixProduct f (acc ++ [θ]) *
                normalizedWordAverage f ℓ) * R) := by
        rw [mul_normalizedAverage (orderedMatrixProduct f acc),
          mul_normalizedAverage L, ← normalizedAverage_mul_right]
        apply congrArg normalizedAverage
        funext θ
        rw [orderedMatrixProduct_append_singleton]
        simp [Matrix.mul_assoc]
      rw [havg]
      apply normalizedAverage_norm_le hepsilon
      intro θ
      exact ih (acc ++ [θ])

/-- An ordered-word bound passes to every power of the normalized average. -/
theorem normalizedAverage_pow_sandwich_norm_le
    (f : κ → CMatrix h) (L R : CMatrix h) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hword : ∀ word : List κ, ‖L * orderedMatrixProduct f word * R‖ ≤ epsilon)
    (ℓ : ℕ) :
    ‖L * (normalizedAverage f) ^ ℓ * R‖ ≤ epsilon := by
  rw [← normalizedWordAverage_eq_pow]
  simpa [Matrix.mul_assoc] using
    orderedWord_normalizedWordAverage_norm_le f L R hepsilon hword [] ℓ

/-- Proposition 4.6 of arXiv:2607.21551v4 for generic game data. -/
theorem game_word_moment_norm_le {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hbase : ‖G.EB * G.EC‖ ≤ epsilon) (ℓ : ℕ) :
    ‖G.EB * G.EBC ^ ℓ * G.EC‖ ≤ epsilon := by
  let f : κ → CMatrix h := fun θ => G.b θ * G.c θ
  have hword : ∀ word : List κ,
      ‖G.EB * orderedMatrixProduct f word * G.EC‖ ≤ epsilon := by
    intro word
    change ‖G.EB * gameAgreementWord G word * G.EC‖ ≤ epsilon
    rw [gameAgreementWord_eq_bobWord_mul_charlieWord G]
    simpa [Matrix.mul_assoc] using game_word_sandwich_norm_le G hbase word
  have hpowers := normalizedAverage_pow_sandwich_norm_le
    f G.EB G.EC hepsilon hword ℓ
  simpa [f, GameOperatorData.EBC] using hpowers

end

end UE.PauliConstructionAndProof
