import PauliConstructionAndProof.Asymptotic
import Mathlib.Tactic

/-!
# Advantage bounds for Theorem 4.1
-/

namespace UE.PauliConstructionAndProof

noncomputable section

/-- The additive advantage bound in equation (17) at Lean index `n`. -/
def pauliExactCorrection (n : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ * Real.sqrt
    (((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1))

theorem pauli_denominator_pos (n : ℕ) :
    0 < (4 : ℝ) ^ (n + 1) - 1 := by
  have hpow : (1 : ℝ) < 4 ^ (n + 1) :=
    one_lt_pow₀ (by norm_num) (by omega)
  linarith

theorem pauli_natCast_ratio_eq_real_ratio (n : ℕ) :
    (((2 ^ (n + 1) : ℕ) : ℝ) /
        (((4 ^ (n + 1) - 1 : ℕ) : ℝ))) =
      (2 : ℝ) ^ (n + 1) / ((4 : ℝ) ^ (n + 1) - 1) := by
  norm_num [Nat.cast_sub (by
    have : 1 ≤ 4 ^ (n + 1) := one_le_pow₀ (by omega)
    exact this)]

theorem half_four_pow_le_denominator (n : ℕ) :
    (2 : ℝ)⁻¹ * (4 : ℝ) ^ (n + 1) ≤
      (4 : ℝ) ^ (n + 1) - 1 := by
  have hfour : (4 : ℝ) ≤ (4 : ℝ) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith [one_le_pow₀ (n := n) (by norm_num : (1 : ℝ) ≤ 4)]
  nlinarith

private theorem half_pow_mul_half_four_pow (n : ℕ) :
    ((2 : ℝ)⁻¹) ^ n * ((2 : ℝ)⁻¹ * (4 : ℝ) ^ (n + 1)) =
      (2 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        ((2 : ℝ)⁻¹) ^ (n + 1) *
            ((2 : ℝ)⁻¹ * (4 : ℝ) ^ (n + 1 + 1)) =
            2 * (((2 : ℝ)⁻¹) ^ n *
              ((2 : ℝ)⁻¹ * (4 : ℝ) ^ (n + 1))) := by
                rw [pow_succ (2 : ℝ)⁻¹ n, pow_succ (4 : ℝ) (n + 1)]
                ring
        _ = 2 * (2 : ℝ) ^ (n + 1) := by rw [ih]
        _ = (2 : ℝ) ^ (n + 1 + 1) := by
          rw [pow_succ]
          ring

theorem pauli_ratio_le_half_pow (n : ℕ) :
    ((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1) ≤
      ((2 : ℝ)⁻¹) ^ n := by
  have hden := pauli_denominator_pos n
  apply (div_le_iff₀ hden).2
  have hhalf := half_four_pow_le_denominator n
  calc
    (2 : ℝ) ^ (n + 1) =
        ((2 : ℝ)⁻¹) ^ n * ((2 : ℝ)⁻¹ * (4 : ℝ) ^ (n + 1)) :=
      (half_pow_mul_half_four_pow n).symm
    _ ≤ ((2 : ℝ)⁻¹) ^ n * ((4 : ℝ) ^ (n + 1) - 1) :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)

theorem half_pow_le_four_mul_nine_sixteenths_pow (n : ℕ) :
    ((2 : ℝ)⁻¹) ^ n ≤ 4 * ((9 : ℝ) / 16) ^ n := by
  have hbase : (2 : ℝ)⁻¹ ≤ (9 : ℝ) / 16 := by norm_num
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) hbase n
  have hnon : 0 ≤ ((9 : ℝ) / 16) ^ n := by positivity
  nlinarith

/-- The exact correction is pointwise dominated by `(3/4)^n`. -/
theorem pauliExactCorrection_le_three_fourths_pow (n : ℕ) :
    pauliExactCorrection n ≤ ((3 : ℝ) / 4) ^ n := by
  unfold pauliExactCorrection
  have hratio_nonneg :
      0 ≤ ((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1) := by
    exact div_nonneg (by positivity) (pauli_denominator_pos n).le
  have hrhs_nonneg : 0 ≤ 2 * ((3 : ℝ) / 4) ^ n := by positivity
  have hsqrt :
      Real.sqrt (((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1)) ≤
        2 * ((3 : ℝ) / 4) ^ n := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hrhs_nonneg
    · calc
        ((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1) ≤
            ((2 : ℝ)⁻¹) ^ n := pauli_ratio_le_half_pow n
        _ ≤ 4 * ((9 : ℝ) / 16) ^ n :=
          half_pow_le_four_mul_nine_sixteenths_pow n
        _ = (2 * ((3 : ℝ) / 4) ^ n) ^ 2 := by
          simp only [pow_two]
          rw [show (9 : ℝ) / 16 = ((3 : ℝ) / 4) * ((3 : ℝ) / 4) by norm_num,
            mul_pow]
          ring
  nlinarith

theorem pauliExactCorrection_nonneg (n : ℕ) :
    0 ≤ pauliExactCorrection n := by
  unfold pauliExactCorrection
  positivity

/-- The additive advantage bound in equation (17) indexed by the
paper's positive qubit count `m`. -/
def pauliPaperExactCorrection (m : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ * Real.sqrt
    (((2 : ℝ) ^ m) / ((4 : ℝ) ^ m - 1))

/-- At qubit count `m ≥ 1`, the additive bound in Theorem 4.1 is at most
`(1/sqrt 2)^(m+1)`. -/
theorem pauliPaperExactCorrection_le_invSqrtTwo_pow
    (m : ℕ) (hm : 1 ≤ m) :
    pauliPaperExactCorrection m ≤
      ((1 : ℝ) / Real.sqrt 2) ^ (m + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 1 n]
  change pauliExactCorrection n ≤
    ((1 : ℝ) / Real.sqrt 2) ^ (n + 1 + 1)
  let b : ℝ := (1 : ℝ) / Real.sqrt 2
  have hbnonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  have hbSq : b ^ 2 = (2 : ℝ)⁻¹ := by
    dsimp [b]
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hratio := pauli_ratio_le_half_pow n
  have hleft : 0 ≤ pauliExactCorrection n :=
    pauliExactCorrection_nonneg n
  have hright : 0 ≤ b ^ (n + 2) := pow_nonneg hbnonneg _
  apply (sq_le_sq₀ hleft hright).mp
  calc
    pauliExactCorrection n ^ 2 =
        (4 : ℝ)⁻¹ *
          (((2 : ℝ) ^ (n + 1)) /
            ((4 : ℝ) ^ (n + 1) - 1)) := by
      rw [pauliExactCorrection, mul_pow,
        Real.sq_sqrt (by
          exact div_nonneg (by positivity) (pauli_denominator_pos n).le)]
      norm_num
    _ ≤ (4 : ℝ)⁻¹ * ((2 : ℝ)⁻¹) ^ n := by
      gcongr
    _ = (b ^ (n + 2)) ^ 2 := by
      rw [pow_two, ← mul_pow, ← pow_two, hbSq, pow_add]
      norm_num
      ring

/-- The advantage bound in Theorem 4.1 has rate
`1/2 sqrt(2^m/(4^m-1)) = O(2^{-m/2})`.

The comparison function `(1/sqrt 2)^m` is exactly `2^{-m/2}`.
-/
theorem pauliPaperExactCorrection_isBigO_invSqrtTwo_pow :
    Asymptotics.IsBigO Filter.atTop pauliPaperExactCorrection
      (fun m : ℕ => ((1 : ℝ) / Real.sqrt 2) ^ m) := by
  apply Asymptotics.IsBigO.of_bound 1
  refine (Filter.eventually_ge_atTop (α := ℕ) 1).mono ?_
  intro m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    dsimp [pauliPaperExactCorrection]
    positivity)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpoint := pauliPaperExactCorrection_le_invSqrtTwo_pow m hm
  have hb : (1 : ℝ) / Real.sqrt 2 ≤ 1 := by
    have hsqrt :=
      Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)
    exact (div_le_one (Real.sqrt_pos.2 (by norm_num))).2 hsqrt
  have hnonneg : 0 ≤ (1 : ℝ) / Real.sqrt 2 := by positivity
  calc
    pauliPaperExactCorrection m ≤
        ((1 : ℝ) / Real.sqrt 2) ^ (m + 1) := hpoint
    _ ≤ ((1 : ℝ) / Real.sqrt 2) ^ m := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hnonneg m) hb
    _ = 1 * ((1 : ℝ) / Real.sqrt 2) ^ m := by ring

end

end UE.PauliConstructionAndProof
