import PauliConstructionAndProof.Pauli
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# §2.1: the Pauli symplectic character matrix

Character orthogonality gives the norm in Lemma 2.7. Restricting to the
nonidentity key set gives the principal-submatrix estimate used in Proof A
of Lemma 4.4.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

noncomputable section

/-- The full symplectic character matrix `Ξ^Pauli` of Definition 2.6. -/
def symplecticSignMatrix (q : ℕ) : Matrix (PauliLabel q) (PauliLabel q) ℂ :=
  fun v w => commutationSign (symplectic q v w)

/-- The restriction of `Ξ^Pauli` to the nonidentity keys used in §4.2.1. -/
def nonzeroSymplecticSignMatrix (q : ℕ) : Matrix (PauliKey q) (PauliKey q) ℂ :=
  fun v w => commutationSign (symplectic q v.1 w.1)

@[simp]
theorem symplecticSignMatrix_apply (q : ℕ) (v w : PauliLabel q) :
    symplecticSignMatrix q v w = commutationSign (symplectic q v w) :=
  rfl

@[simp]
theorem nonzeroSymplecticSignMatrix_apply (q : ℕ) (v w : PauliKey q) :
    nonzeroSymplecticSignMatrix q v w =
      commutationSign (symplectic q v.1 w.1) :=
  rfl

/-- One-qubit character orthogonality, proved by exhaustive Boolean cases. -/
theorem singleSymplectic_character_orthogonality (v u : SingleLabel) :
    ∑ w : SingleLabel,
        commutationSign (singleSymplectic v w) *
          commutationSign (singleSymplectic u w) =
      if v = u then (4 : ℂ) else 0 := by
  rcases v with ⟨vx, vz⟩
  rcases u with ⟨ux, uz⟩
  cases vx <;> cases vz <;> cases ux <;> cases uz <;>
    norm_num [singleSymplectic, commutationSign, Fintype.sum_prod_type]

/-- Orthogonality of the full family of binary symplectic characters. -/
theorem symplectic_character_orthogonality (q : ℕ) (v u : PauliLabel q) :
    ∑ w : PauliLabel q,
        commutationSign (symplectic q v w) *
          commutationSign (symplectic q u w) =
      if v = u then ((4 ^ q : ℕ) : ℂ) else 0 := by
  induction q with
  | zero =>
      rcases v with ⟨⟩
      rcases u with ⟨⟩
      simp [symplectic]
  | succ q ih =>
      rcases v with ⟨v₀, v'⟩
      rcases u with ⟨u₀, u'⟩
      simp only [symplectic, commutationSign_xor]
      change
        (∑ w : SingleLabel × PauliLabel q,
          (commutationSign (singleSymplectic v₀ w.1) *
              commutationSign (symplectic q v' w.2)) *
            (commutationSign (singleSymplectic u₀ w.1) *
              commutationSign (symplectic q u' w.2))) = _
      calc
        _ = ∑ x : SingleLabel, ∑ y : PauliLabel q,
              (commutationSign (singleSymplectic v₀ x) *
                commutationSign (singleSymplectic u₀ x)) *
              (commutationSign (symplectic q v' y) *
                commutationSign (symplectic q u' y)) := by
              rw [Fintype.sum_prod_type]
              congr with x
              congr with y
              ring
        _ = (∑ x : SingleLabel,
                commutationSign (singleSymplectic v₀ x) *
                  commutationSign (singleSymplectic u₀ x)) *
              (∑ y : PauliLabel q,
                commutationSign (symplectic q v' y) *
                  commutationSign (symplectic q u' y)) := by
              rw [Fintype.sum_mul_sum]
        _ = (if v₀ = u₀ then (4 : ℂ) else 0) *
              (if v' = u' then ((4 ^ q : ℕ) : ℂ) else 0) := by
              rw [singleSymplectic_character_orthogonality, ih]
        _ = _ := by
          by_cases h₀ : v₀ = u₀
          · subst u₀
            by_cases h' : v' = u'
            · subst u'
              rw [if_pos rfl, if_pos rfl, if_pos rfl]
              push_cast
              rw [pow_succ]
              ring
            · have hp : (v₀, v') ≠ (v₀, u') := by
                intro h
                exact h' (congrArg Prod.snd h)
              rw [if_pos rfl, if_neg h']
              simp only [mul_zero]
              split_ifs with hpair
              · exact (hp hpair).elim
              · rfl
          · have hne : (v₀, v') ≠ (u₀, u') := by
              intro h
              exact h₀ (congrArg Prod.fst h)
            rw [if_neg h₀, zero_mul]
            split_ifs with hpair
            · exact (hne hpair).elim
            · rfl

/-- Matrix form of symplectic character orthogonality. -/
theorem symplecticSignMatrix_mul_self (q : ℕ) :
    symplecticSignMatrix q * symplecticSignMatrix q =
      (((4 ^ q : ℕ) : ℂ) • (1 : Matrix (PauliLabel q) (PauliLabel q) ℂ)) := by
  classical
  ext v u
  rw [Matrix.mul_apply]
  simp only [symplecticSignMatrix_apply]
  have hsum :
      (∑ j : PauliLabel q,
          commutationSign (symplectic q v j) *
            commutationSign (symplectic q j u)) =
        ∑ j : PauliLabel q,
          commutationSign (symplectic q v j) *
            commutationSign (symplectic q u j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [symplectic_comm q j u]
  rw [hsum, symplectic_character_orthogonality]
  by_cases h : v = u
  · subst u
    simp
  · simp [h]

@[simp]
theorem symplecticSignMatrix_conjTranspose (q : ℕ) :
    Matrix.conjTranspose (symplecticSignMatrix q) = symplecticSignMatrix q := by
  ext v w
  rw [Matrix.conjTranspose_apply, symplecticSignMatrix_apply,
    symplecticSignMatrix_apply, symplectic_comm q w v]
  cases symplectic q v w <;> simp [commutationSign]

/-- Lemma 2.7. The full symplectic character matrix has operator norm `2^q`. -/
theorem symplecticSignMatrix_norm (q : ℕ) :
    ‖symplecticSignMatrix q‖ = ((2 ^ q : ℕ) : ℝ) := by
  classical
  letI : Nonempty (PauliLabel q) := ⟨zeroLabel q⟩
  have hsquare :=
    Matrix.l2_opNorm_conjTranspose_mul_self (symplecticSignMatrix q)
  rw [symplecticSignMatrix_conjTranspose, symplecticSignMatrix_mul_self] at hsquare
  have hscalar :
      ‖(((4 ^ q : ℕ) : ℂ) •
          (1 : Matrix (PauliLabel q) (PauliLabel q) ℂ))‖ =
        ((4 ^ q : ℕ) : ℝ) := by
    rw [norm_smul, norm_one]
    simp
  rw [hscalar] at hsquare
  have hpow :
      ((4 ^ q : ℕ) : ℝ) =
        ((2 ^ q : ℕ) : ℝ) * ((2 ^ q : ℕ) : ℝ) := by
    norm_cast
    rw [← Nat.mul_pow]
  have hnonneg : 0 ≤ ((2 ^ q : ℕ) : ℝ) := by positivity
  nlinarith [norm_nonneg (symplecticSignMatrix q),
    hnonneg]

/-- The coordinate inclusion from nonzero labels into all labels. -/
def pauliKeyInclusion (q : ℕ) : Matrix (PauliLabel q) (PauliKey q) ℂ :=
  fun v k => if v = k.1 then 1 else 0

@[simp]
theorem pauliKeyInclusion_apply (q : ℕ) (v : PauliLabel q) (k : PauliKey q) :
    pauliKeyInclusion q v k = if v = k.1 then 1 else 0 :=
  rfl

/-- The coordinate inclusion is an isometry on its (possibly empty) source. -/
theorem pauliKeyInclusion_conjTranspose_mul (q : ℕ) :
    Matrix.conjTranspose (pauliKeyInclusion q) * pauliKeyInclusion q =
      (1 : Matrix (PauliKey q) (PauliKey q) ℂ) := by
  classical
  ext k l
  simp [Matrix.mul_apply, pauliKeyInclusion, Matrix.conjTranspose_apply,
    Matrix.one_apply, Subtype.coe_inj, eq_comm]

/-- The deleted sign matrix is the compression of the full Fourier matrix. -/
theorem nonzeroSymplecticSignMatrix_eq_compression (q : ℕ) :
    nonzeroSymplecticSignMatrix q =
      (Matrix.conjTranspose (pauliKeyInclusion q) * symplecticSignMatrix q) *
        pauliKeyInclusion q := by
  classical
  ext k l
  simp [Matrix.mul_apply, pauliKeyInclusion, Matrix.conjTranspose_apply,
    symplecticSignMatrix, nonzeroSymplecticSignMatrix]

/-- The coordinate inclusion has L2 operator norm at most one. -/
theorem pauliKeyInclusion_norm_le_one (q : ℕ) :
    ‖pauliKeyInclusion q‖ ≤ 1 := by
  classical
  have hsquare :=
    Matrix.l2_opNorm_conjTranspose_mul_self (pauliKeyInclusion q)
  rw [pauliKeyInclusion_conjTranspose_mul] at hsquare
  have hone :
      ‖(1 : Matrix (PauliKey q) (PauliKey q) ℂ)‖ ≤ 1 :=
    by
      cases isEmpty_or_nonempty (PauliKey q) with
      | inl hempty =>
          letI := hempty
          have hsub :
              (1 : Matrix (PauliKey q) (PauliKey q) ℂ) = 0 :=
            Subsingleton.elim _ _
          rw [hsub, norm_zero]
          norm_num
      | inr hnonempty =>
          letI := hnonempty
          rw [norm_one]
  nlinarith [norm_nonneg (pauliKeyInclusion q)]

/-- The principal-submatrix norm bound used in Proof A of Lemma 4.4. -/
theorem nonzeroSymplecticSignMatrix_norm_le (q : ℕ) :
    ‖nonzeroSymplecticSignMatrix q‖ ≤ ((2 ^ q : ℕ) : ℝ) := by
  classical
  rw [nonzeroSymplecticSignMatrix_eq_compression]
  calc
    ‖(Matrix.conjTranspose (pauliKeyInclusion q) * symplecticSignMatrix q) *
        pauliKeyInclusion q‖ ≤
        ‖Matrix.conjTranspose (pauliKeyInclusion q) * symplecticSignMatrix q‖ *
          ‖pauliKeyInclusion q‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Matrix.conjTranspose (pauliKeyInclusion q)‖ *
          ‖symplecticSignMatrix q‖) * ‖pauliKeyInclusion q‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ = (‖pauliKeyInclusion q‖ * ((2 ^ q : ℕ) : ℝ)) *
          ‖pauliKeyInclusion q‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, symplecticSignMatrix_norm]
    _ ≤ ((2 ^ q : ℕ) : ℝ) := by
      have hJ := pauliKeyInclusion_norm_le_one q
      have hJnonneg := norm_nonneg (pauliKeyInclusion q)
      have hpow : 0 ≤ ((2 ^ q : ℕ) : ℝ) := by positivity
      calc
        (‖pauliKeyInclusion q‖ * ((2 ^ q : ℕ) : ℝ)) *
            ‖pauliKeyInclusion q‖ ≤
            (1 * ((2 ^ q : ℕ) : ℝ)) * ‖pauliKeyInclusion q‖ := by
          gcongr
        _ ≤ (1 * ((2 ^ q : ℕ) : ℝ)) * 1 := by
          gcongr
        _ = ((2 ^ q : ℕ) : ℝ) := by ring

/-- The deleted label set has exactly `4^q - 1` elements, in complex scalars. -/
theorem pauliKey_card_cast_complex (q : ℕ) :
    ((Fintype.card (PauliKey q) : ℕ) : ℂ) = ((4 ^ q - 1 : ℕ) : ℂ) := by
  simp

/-- The full label set has exactly `4^q` elements, in complex scalars. -/
theorem pauliLabel_card_cast_complex (q : ℕ) :
    ((Fintype.card (PauliLabel q) : ℕ) : ℂ) = (((4 ^ q : ℕ) : ℂ)) := by
  simp

/-- The deleted label cardinality, coerced to the real scalars used in bounds. -/
theorem pauliKey_card_cast_real (q : ℕ) :
    ((Fintype.card (PauliKey q) : ℕ) : ℝ) = ((4 ^ q - 1 : ℕ) : ℝ) := by
  simp

/-- The full label cardinality, coerced to real scalars. -/
theorem pauliLabel_card_cast_real (q : ℕ) :
    ((Fintype.card (PauliLabel q) : ℕ) : ℝ) = ((4 ^ q : ℕ) : ℝ) := by
  simp

/-- There is at least one nonidentity label on `q+1` qubits. -/
theorem pauliKey_card_succ_pos (q : ℕ) :
    0 < Fintype.card (PauliKey (q + 1)) :=
  Fintype.card_pos_iff.mpr ⟨firstPauliKey q⟩

/-- Real positivity of the key-count denominator at the parameters used by the construction. -/
theorem pauliKey_card_succ_cast_real_pos (q : ℕ) :
    (0 : ℝ) < Fintype.card (PauliKey (q + 1)) := by
  exact_mod_cast pauliKey_card_succ_pos q

end

end UE.PauliConstructionAndProof
