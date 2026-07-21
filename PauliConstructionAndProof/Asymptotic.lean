import UE.Security
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Asymptotic helpers for negligible geometric errors
-/

open Filter

namespace UE.PauliConstructionAndProof

noncomputable section

/-- A nonnegative real geometric sequence with ratio strictly below one is
negligible in the repository's inverse-polynomial sense. -/
theorem negligible_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Negligible (fun n => r ^ n) := by
  constructor
  · intro n
    positivity
  · intro c hc
    by_cases hr : r = 0
    · subst r
      filter_upwards [eventually_gt_atTop 0] with n hn
      simp [Nat.ne_of_gt hn]
    · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
      have hinv : 1 < r⁻¹ := (one_lt_inv₀ hrpos).2 hr1
      have hdom :=
        (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) c hinv).bound
          (by norm_num : (0 : ℝ) < 1)
      filter_upwards [hdom, eventually_gt_atTop 0] with n hn hnpos
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
      have hpolypos : 0 < (n : ℝ) ^ c := pow_pos hnreal c
      have hexppos : 0 < (r⁻¹) ^ n := pow_pos (inv_pos.mpr hrpos) n
      have hpoly : (n : ℝ) ^ c ≤ (r⁻¹) ^ n := by
        simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hnreal.le c),
          abs_of_pos hrpos, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hr0) n)] using hn
      have hinvle : ((r⁻¹) ^ n)⁻¹ ≤ ((n : ℝ) ^ c)⁻¹ :=
        (inv_le_inv₀ hexppos hpolypos).2 hpoly
      simpa [inv_pow] using hinvle

/-- The concrete error ratio used by the Pauli construction is negligible. -/
theorem three_fourths_pow_negligible :
    Negligible (fun n => (3 / 4 : ℝ) ^ n) := by
  apply negligible_geometric
  · norm_num
  · norm_num

end

end UE.PauliConstructionAndProof
