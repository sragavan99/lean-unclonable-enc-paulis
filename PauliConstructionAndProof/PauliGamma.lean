import PauliConstructionAndProof.Fourier
import PauliConstructionAndProof.ReflectionConstruction

/-!
# The full-Pauli reflection family and exact Gamma norm

The deleted symplectic character matrix satisfies the paper's identity
`4^q I = 11ᵀ + Gamma²`.  Evaluating it on the difference of two explicit
nonidentity labels supplies the lower norm bound matching the compression
upper bound.
-/

open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

/-- The square all-ones matrix. -/
def constantOneMatrix (a : Type*) : Matrix a a ℂ := fun _ _ => 1

/-- The paper's exact identity on the nonzero-label space. -/
theorem nonzeroSymplecticSignMatrix_square_identity (q : ℕ) :
    (((4 ^ q : ℕ) : ℂ) • (1 : CMatrix (PauliKey q))) =
      constantOneMatrix (PauliKey q) +
        nonzeroSymplecticSignMatrix q * nonzeroSymplecticSignMatrix q := by
  classical
  ext v u
  simp only [Matrix.smul_apply, Matrix.add_apply, constantOneMatrix]
  rw [Matrix.mul_apply]
  simp only [nonzeroSymplecticSignMatrix_apply]
  let f : PauliLabel q → ℂ := fun w =>
    commutationSign (symplectic q v.1 w) *
      commutationSign (symplectic q w u.1)
  have hpartition := Fintype.sum_subtype_add_sum_subtype
    (fun w : PauliLabel q => w ≠ zeroLabel q) f
  letI : Unique {w : PauliLabel q // ¬ w ≠ zeroLabel q} := {
    default := ⟨zeroLabel q, by simp⟩
    uniq w := Subtype.ext (not_ne_iff.mp w.2) }
  have hzero :
      (∑ w : {w : PauliLabel q // ¬ w ≠ zeroLabel q}, f w.1) = 1 := by
    simp only [Fintype.sum_unique]
    have hw : (default : {w : PauliLabel q // ¬ w ≠ zeroLabel q}).1 =
        zeroLabel q := not_ne_iff.mp
          (default : {w : PauliLabel q // ¬ w ≠ zeroLabel q}).2
    rw [hw]
    simp [f]
  have hsum :
      (1 : ℂ) + ∑ w : PauliKey q,
          commutationSign (symplectic q v.1 w.1) *
            commutationSign (symplectic q w.1 u.1) =
        ∑ w : PauliLabel q,
          commutationSign (symplectic q v.1 w) *
            commutationSign (symplectic q w u.1) := by
    rw [hzero] at hpartition
    simpa [f, add_comm] using hpartition
  rw [hsum]
  have hfull := symplectic_character_orthogonality q v.1 u.1
  have hcomm :
      (∑ w : PauliLabel q,
          commutationSign (symplectic q v.1 w) *
            commutationSign (symplectic q w u.1)) =
        ∑ w : PauliLabel q,
          commutationSign (symplectic q v.1 w) *
            commutationSign (symplectic q u.1 w) := by
    apply Finset.sum_congr rfl
    intro w _
    rw [symplectic_comm q w u.1]
  rw [hcomm, hfull]
  by_cases hvu : v = u
  · subst u
    simp
  · have hcoe : v.1 ≠ u.1 := by
      exact fun h => hvu (Subtype.ext h)
    simp [hvu, hcoe, Matrix.one_apply]

/-- A two-point column orthogonal to the all-ones row. -/
def pauliGammaDifferenceColumn (q : ℕ) :
    Matrix (PauliKey (q + 1)) (Fin 1) ℂ := fun k _ =>
  if k = firstPauliKey q then 1
  else if k = firstZPauliKey q then -1
  else 0

theorem pauliGammaDifferenceColumn_ne_zero (q : ℕ) :
    pauliGammaDifferenceColumn q ≠ 0 := by
  intro hzero
  have hentry := congrArg
    (fun A : Matrix (PauliKey (q + 1)) (Fin 1) ℂ =>
      A (firstPauliKey q) 0) hzero
  simp [pauliGammaDifferenceColumn,
    firstPauliKey_ne_firstZPauliKey q] at hentry

theorem allOnes_mul_pauliGammaDifferenceColumn (q : ℕ) :
    constantOneMatrix (PauliKey (q + 1)) *
      pauliGammaDifferenceColumn q = 0 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, constantOneMatrix, one_mul,
    pauliGammaDifferenceColumn, Matrix.zero_apply]
  have hfun : ∀ x : PauliKey (q + 1),
      (if x = firstPauliKey q then (1 : ℂ)
        else if x = firstZPauliKey q then -1 else 0) =
      (if x = firstPauliKey q then (1 : ℂ) else 0) -
        (if x = firstZPauliKey q then (1 : ℂ) else 0) := by
    intro x
    by_cases hx : x = firstPauliKey q
    · subst x
      simp [firstPauliKey_ne_firstZPauliKey q]
    · by_cases hz : x = firstZPauliKey q <;>
        simp [hx, hz, firstPauliKey_ne_firstZPauliKey q,
          (firstPauliKey_ne_firstZPauliKey q).symm]
  simp_rw [hfun, Finset.sum_sub_distrib]
  simp

theorem nonzeroSymplecticSignMatrix_square_mul_differenceColumn (q : ℕ) :
    (nonzeroSymplecticSignMatrix (q + 1) *
        nonzeroSymplecticSignMatrix (q + 1)) *
        pauliGammaDifferenceColumn q =
      (((4 ^ (q + 1) : ℕ) : ℂ) • pauliGammaDifferenceColumn q) := by
  have h := congrArg
    (fun A : CMatrix (PauliKey (q + 1)) =>
      A * pauliGammaDifferenceColumn q)
    (nonzeroSymplecticSignMatrix_square_identity (q + 1))
  simpa [Matrix.add_mul, Matrix.smul_mul,
    allOnes_mul_pauliGammaDifferenceColumn q] using h.symm

/-- Exact current-paper norm of the nonidentity Pauli commutation matrix. -/
theorem nonzeroSymplecticSignMatrix_norm (q : ℕ) :
    ‖nonzeroSymplecticSignMatrix (q + 1)‖ =
      ((2 ^ (q + 1) : ℕ) : ℝ) := by
  classical
  letI : Nonempty (PauliKey (q + 1)) := ⟨firstPauliKey q⟩
  let Gamma := nonzeroSymplecticSignMatrix (q + 1)
  let V := pauliGammaDifferenceColumn q
  have hVpos : 0 < ‖V‖ := by
    exact norm_pos_iff.mpr (pauliGammaDifferenceColumn_ne_zero q)
  have hmul := Matrix.l2_opNorm_mul (Gamma * Gamma) V
  have hact : (Gamma * Gamma) * V =
      (((4 ^ (q + 1) : ℕ) : ℂ) • V) := by
    exact nonzeroSymplecticSignMatrix_square_mul_differenceColumn q
  rw [hact, norm_smul] at hmul
  have hscalar : ‖(((4 ^ (q + 1) : ℕ) : ℂ))‖ =
      ((4 ^ (q + 1) : ℕ) : ℝ) := by simp
  rw [hscalar] at hmul
  have hGG := Matrix.l2_opNorm_mul Gamma Gamma
  have hchain :
      ((4 ^ (q + 1) : ℕ) : ℝ) * ‖V‖ ≤
        (‖Gamma‖ * ‖Gamma‖) * ‖V‖ :=
    hmul.trans (mul_le_mul_of_nonneg_right hGG (norm_nonneg V))
  have hpow :
      ((4 ^ (q + 1) : ℕ) : ℝ) =
        ((2 ^ (q + 1) : ℕ) : ℝ) *
          ((2 ^ (q + 1) : ℕ) : ℝ) := by
    norm_cast
    rw [← Nat.mul_pow]
  have hlower : ((2 ^ (q + 1) : ℕ) : ℝ) ≤ ‖Gamma‖ := by
    rw [hpow] at hchain
    have hsquares :
        ((2 ^ (q + 1) : ℕ) : ℝ) * ((2 ^ (q + 1) : ℕ) : ℝ) ≤
          ‖Gamma‖ * ‖Gamma‖ := by
      exact le_of_mul_le_mul_right hchain hVpos
    nlinarith [norm_nonneg Gamma]
  have hupper := nonzeroSymplecticSignMatrix_norm_le (q + 1)
  exact le_antisymm hupper hlower

/-- The full nonidentity-Pauli family as abstract reflection data. -/
def pauliReflectionFamily (q : ℕ) :
    ReflectionFamily (PauliKey q) (Fin (2 ^ q)) where
  Q k := pauli k.1
  Gamma := nonzeroSymplecticSignMatrix q
  Q_hermitian k := pauli_isHermitian k.1
  Q_involution k := pauli_mul_self k.1
  Q_trace_zero k := pauliKey_trace_eq_zero k
  commutation φ θ := pauli_commutation φ.1 θ.1

@[simp]
theorem pauliReflectionFamily_Gamma (q : ℕ) :
    (pauliReflectionFamily q).Gamma = nonzeroSymplecticSignMatrix q := rfl

/-- The abstract Gamma ratio at Lean parameter `n` in real-power notation. -/
theorem pauliReflectionFamily_Gamma_ratio (n : ℕ) :
    ‖(pauliReflectionFamily (n + 1)).Gamma‖ /
        (Fintype.card (PauliKey (n + 1)) : ℝ) =
      (2 : ℝ) ^ (n + 1) / ((4 : ℝ) ^ (n + 1) - 1) := by
  rw [pauliReflectionFamily_Gamma, nonzeroSymplecticSignMatrix_norm n]
  norm_num [Nat.cast_sub (by
    have : 1 ≤ 4 ^ (n + 1) := one_le_pow₀ (by omega)
    exact this)]

end

end UE.PauliConstructionAndProof
