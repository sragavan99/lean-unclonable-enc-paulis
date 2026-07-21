import PauliConstructionAndProof.WordMoments
import PauliConstructionAndProof.Resolvent
import PauliConstructionAndProof.Separator
import QIT.Util.SDP.HermitianPSDTraceDuality

/-!
# Abstract security of reflection encryption

This file assembles the Gamma estimate, ordered-word moments, geometric
resolvent, and current separator into the abstract finite-key theorem.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh ub uc

variable {κ : Type uκ} {h : Type uh}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype h] [DecidableEq h] [Nonempty h]

/-- The operator-level assembly from a strictly positive uniform word bound. -/
theorem gameXi_le_of_word_moment_bound
    (G : GameOperatorData κ h) {ε : ℝ} (hε : 0 < ε)
    (hpowers : ∀ ℓ : ℕ, ‖G.SB * G.Z ^ ℓ * G.SC‖ ≤ ε) :
    G.Xi ≤ ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt ε) •
      (1 : CMatrix h) := by
  let δ : ℝ := Real.sqrt ε
  have hδ : 0 < δ := Real.sqrt_pos.2 hε
  have hδsq : δ ^ 2 = ε := Real.sq_sqrt hε.le
  have hquot : ε / δ = δ := by
    rw [← hδsq]
    field_simp
  have hresolvent :
      ‖G.SB * (G.D + δ • (1 : CMatrix h))⁻¹ * G.SC‖ ≤ δ := by
    have h := resolvent_sandwich_l2OperatorNorm_le
      G.D G.Z G.SB G.SC G.D_posSemidef G.D_le_one hε.le hδ
        G.Z_eq_one_sub_two_D hpowers
    rwa [hquot] at h
  have hminus :
      (G.D - (2 : ℝ)⁻¹ • (G.SB - G.SC)).PosSemidef :=
    Matrix.le_iff.mp G.half_SB_sub_SC_le_D
  have hplus :
      (G.D - (2 : ℝ)⁻¹ • (G.SC - G.SB)).PosSemidef :=
    Matrix.le_iff.mp G.half_SC_sub_SB_le_D
  have hseparator :
      (2 : ℝ)⁻¹ • (G.SB + G.SC) - G.D ≤
        δ • (1 : CMatrix h) := by
    have h := reflectionGameSeparator G.SB G.SC G.D
      G.SB_isHermitian G.SC_isHermitian G.D_isHermitian
      hminus hplus hδ hδ hresolvent
    simpa using h
  have hscaled :
      (2 : ℝ)⁻¹ •
          ((2 : ℝ)⁻¹ • (G.SB + G.SC) - G.D) ≤
        (2 : ℝ)⁻¹ • (δ • (1 : CMatrix h)) := by
    rw [Matrix.le_iff]
    have hs := (Matrix.le_iff.mp hseparator).smul
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    convert hs using 1
    module
  have hXi :
      G.Xi = (2 : ℝ)⁻¹ • (1 : CMatrix h) +
        (2 : ℝ)⁻¹ •
          ((2 : ℝ)⁻¹ • (G.SB + G.SC) - G.D) := by
    rw [G.Xi_decomposition]
    module
  rw [hXi]
  calc
    (2 : ℝ)⁻¹ • (1 : CMatrix h) +
        (2 : ℝ)⁻¹ •
          ((2 : ℝ)⁻¹ • (G.SB + G.SC) - G.D) ≤
      (2 : ℝ)⁻¹ • (1 : CMatrix h) +
        (2 : ℝ)⁻¹ • (δ • (1 : CMatrix h)) :=
      add_le_add (le_refl _) hscaled
    _ = ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt ε) •
        (1 : CMatrix h) := by
      dsimp [δ]
      module

variable {bob : Type ub} {charlie : Type uc}
variable [Fintype bob] [DecidableEq bob] [Nonempty bob]
variable [Fintype charlie] [DecidableEq charlie] [Nonempty charlie]
variable {F : ReflectionFamily κ h}

/-- Abstract operator theorem corresponding exactly to equation (A25). -/
theorem reflectionAttackXi_le
    (attack : ReflectionCloningAttack F bob charlie) :
    (reflectionAttackGameData attack).Xi ≤
      ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (‖F.Gamma‖ / (Fintype.card κ : ℝ))) •
          (1 : CMatrix (ReflectionAttackHilbert attack)) := by
  apply gameXi_le_of_word_moment_bound
  · exact div_pos F.Gamma_norm_pos (by positivity)
  · exact reflectionAttack_word_moment_norm_le attack

/-- End-to-end fixed-parameter security of every abstract reflection family. -/
theorem reflectionCloningSuccess_le
    (attack : ReflectionCloningAttack F bob charlie) :
    attack.success ≤
      (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (‖F.Gamma‖ / (Fintype.card κ : ℝ)) := by
  rw [reflectionAttackSuccess_eq_trace_Xi attack]
  have htrace := cMatrix_trace_mul_le_of_le_posSemidef_left
    (reflectionAttackDilationState attack).pos
    (reflectionAttackXi_le attack)
  calc
    Complex.re (((reflectionAttackDilationState attack).matrix *
        (reflectionAttackGameData attack).Xi).trace) ≤
      Complex.re (((reflectionAttackDilationState attack).matrix *
        (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
          (‖F.Gamma‖ / (Fintype.card κ : ℝ))) •
            (1 : CMatrix (ReflectionAttackHilbert attack)))).trace) := htrace
    _ = (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (‖F.Gamma‖ / (Fintype.card κ : ℝ)) := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
        (reflectionAttackDilationState attack).trace_eq_one]
      simp [Complex.real_smul]

end

end UE.PauliConstructionAndProof
