import UE.Definitions
import PauliConstructionAndProof.FiniteProbability
import QIT.Util.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# Reflection-family generalisation of the Pauli scheme

The construction of §3 extends to a finite uniform key set of traceless
Hermitian reflections. Proof A of Lemma 4.4 assumes commutation signs and
Proof B assumes Hilbert--Schmidt orthogonality.
-/

open scoped BigOperators ComplexOrder MatrixOrder NNReal Matrix.Norms.L2Operator

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh ub uc

/-- The plaintext-dependent sign: `false` selects the `+1` eigenspace and
`true` selects the `-1` eigenspace. -/
def bitSign : Bool → ℂ
  | false => 1
  | true => -1

@[simp] theorem bitSign_false : bitSign false = 1 := rfl
@[simp] theorem bitSign_true : bitSign true = -1 := rfl

@[simp]
theorem bitSign_mul_self (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> norm_num [bitSign]

@[simp]
theorem bitSign_neg (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

/-- A finite family of traceless Hermitian reflections. -/
structure ReflectionFamily (κ : Type uκ) (h : Type uh)
    [Fintype κ] [DecidableEq κ] [Fintype h] [DecidableEq h] where
  Q : κ → CMatrix h
  Q_hermitian : ∀ θ, (Q θ).IsHermitian
  Q_involution : ∀ θ, Q θ * Q θ = 1
  Q_trace_zero : ∀ θ, (Q θ).trace = 0

variable {κ : Type uκ} {h : Type uh}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype h] [DecidableEq h] [Nonempty h]

/-- The `b`-labelled eigenspace projection of an abstract reflection. -/
def reflectionEffect (F : ReflectionFamily κ h) (θ : κ) (b : Bool) : CMatrix h :=
  (2 : ℂ)⁻¹ • (1 + bitSign b • F.Q θ)

theorem reflectionEffect_isHermitian (F : ReflectionFamily κ h) (θ : κ) (b : Bool) :
    (reflectionEffect F θ b).IsHermitian := by
  cases b <;>
    simp [reflectionEffect, Matrix.IsHermitian, (F.Q_hermitian θ).eq]

theorem reflectionEffect_idempotent (F : ReflectionFamily κ h) (θ : κ) (b : Bool) :
    reflectionEffect F θ b * reflectionEffect F θ b = reflectionEffect F θ b := by
  cases b <;>
    simp [reflectionEffect, Matrix.add_mul, Matrix.mul_add, F.Q_involution]
  all_goals module

theorem reflectionEffect_pos (F : ReflectionFamily κ h) (θ : κ) (b : Bool) :
    (reflectionEffect F θ b).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (reflectionEffect F θ b)
  rw [reflectionEffect_isHermitian F θ b,
    reflectionEffect_idempotent F θ b] at h
  exact h

theorem reflectionEffect_complement (F : ReflectionFamily κ h) (θ : κ) (b : Bool) :
    1 - reflectionEffect F θ b = reflectionEffect F θ (!b) := by
  cases b <;> simp [reflectionEffect] <;> module

theorem reflectionEffect_le_one (F : ReflectionFamily κ h) (θ : κ) (b : Bool) :
    reflectionEffect F θ b ≤ 1 := by
  rw [Matrix.le_iff, reflectionEffect_complement]
  exact reflectionEffect_pos F θ (!b)

theorem reflectionEffect_orthogonal (F : ReflectionFamily κ h) (θ : κ) (b : Bool) :
    reflectionEffect F θ b * reflectionEffect F θ (!b) = 0 := by
  rw [← reflectionEffect_complement]
  rw [Matrix.mul_sub, Matrix.mul_one, reflectionEffect_idempotent]
  exact sub_self _

/-- Tracelessness makes both eigenspaces have dimension `card h / 2`. -/
theorem reflectionEffect_trace (F : ReflectionFamily κ h) (θ : κ) (b : Bool) :
    (reflectionEffect F θ b).trace = (Fintype.card h : ℂ) / 2 := by
  simp [reflectionEffect, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_one, F.Q_trace_zero]
  ring

/-- The two eigenspace projections form the honest binary POVM. -/
def reflectionPOVM (F : ReflectionFamily κ h) (θ : κ) : POVM Bool h :=
  POVM.binaryOfEffect (reflectionEffect F θ true)
    (reflectionEffect_pos F θ true) (reflectionEffect_le_one F θ true)

@[simp]
theorem reflectionPOVM_effects (F : ReflectionFamily κ h) (θ : κ) (b : Bool) :
    (reflectionPOVM F θ).effects b = reflectionEffect F θ b := by
  cases b
  · change 1 - reflectionEffect F θ true = reflectionEffect F θ false
    exact reflectionEffect_complement F θ true
  · rfl

/-- The normalized maximally mixed state on the selected eigenspace. -/
def reflectionCiphertextState (F : ReflectionFamily κ h) (θ : κ) (b : Bool) : State h where
  matrix := (2 / (Fintype.card h : ℝ)) • reflectionEffect F θ b
  pos := (reflectionEffect_pos F θ b).smul (by positivity)
  trace_eq_one := by
    rw [Matrix.trace_smul, reflectionEffect_trace]
    have hcard : (Fintype.card h : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card h ≠ 0)
    norm_num [Complex.real_smul, hcard]

@[simp]
theorem reflectionCiphertextState_matrix (F : ReflectionFamily κ h) (θ : κ) (b : Bool) :
    (reflectionCiphertextState F θ b).matrix =
      (2 / (Fintype.card h : ℝ)) • reflectionEffect F θ b := rfl

/-- The reflection-family form of the mixed-state formula in equation (15). -/
theorem reflectionCiphertextState_matrix_explicit
    (F : ReflectionFamily κ h) (θ : κ) (b : Bool) :
    (reflectionCiphertextState F θ b).matrix =
      (((Fintype.card h : ℝ)⁻¹ : ℂ)) • (1 + bitSign b • F.Q θ) := by
  ext i j
  simp only [reflectionCiphertextState_matrix, reflectionEffect,
    Matrix.smul_apply, Complex.real_smul]
  have hcard : (Fintype.card h : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card h ≠ 0)
  push_cast
  field_simp
  norm_num [hcard]
  ring

theorem reflectionPOVM_honest_probability
    (F : ReflectionFamily κ h) (θ : κ) (b : Bool) :
    ((reflectionPOVM F θ).prob (reflectionCiphertextState F θ b) b : ℝ) = 1 := by
  rw [POVM.prob_eq_trace_re, reflectionPOVM_effects,
    reflectionCiphertextState_matrix]
  rw [Matrix.smul_mul, reflectionEffect_idempotent,
    Matrix.trace_smul, reflectionEffect_trace]
  have hcard : (Fintype.card h : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card h ≠ 0)
  norm_num [Complex.real_smul, hcard]

/-- A fixed-parameter splitting attack against the abstract reflection scheme.
Both output spaces are arbitrary finite types, and both POVM families may
depend on the revealed key. -/
structure ReflectionCloningAttack (F : ReflectionFamily κ h)
    (bob : Type ub) (charlie : Type uc)
    [Fintype bob] [DecidableEq bob] [Fintype charlie] [DecidableEq charlie] where
  pirate : Channel h (bob × charlie)
  bobMeasure : κ → POVM Bool bob
  charlieMeasure : κ → POVM Bool charlie

namespace ReflectionCloningAttack

variable {F : ReflectionFamily κ h}
variable {bob : Type ub} {charlie : Type uc}
variable [Fintype bob] [DecidableEq bob] [Fintype charlie] [DecidableEq charlie]

/-- Fixed-key joint success, averaged over the uniform plaintext bit. -/
def keyScore (A : ReflectionCloningAttack F bob charlie) (θ : κ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ b : Bool,
    ((UE.jointPOVM (A.bobMeasure θ) (A.charlieMeasure θ)).prob
      (A.pirate.applyState (reflectionCiphertextState F θ b)) (b, b) : ℝ)

/-- Overall success under the uniform finite key distribution. -/
def success (A : ReflectionCloningAttack F bob charlie) : ℝ :=
  (Fintype.card κ : ℝ)⁻¹ * ∑ θ, A.keyScore θ

end ReflectionCloningAttack

end

end UE.PauliConstructionAndProof
