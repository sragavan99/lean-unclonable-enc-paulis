import PauliConstructionAndProof.Asymptotic
import Mathlib.Tactic

/-!
# Scalar bounds for the Pauli correction term
-/

namespace UE.PauliConstructionAndProof

noncomputable section

/-- The exact additive correction supplied by the operator argument. -/
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

end

end UE.PauliConstructionAndProof
