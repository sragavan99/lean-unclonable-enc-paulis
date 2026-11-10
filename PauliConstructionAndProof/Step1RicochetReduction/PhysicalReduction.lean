import PauliConstructionAndProof.ReflectionConstruction
import PauliConstructionAndProof.Step1RicochetReduction.ChoiNaimark

/-!
# §4.1: decoding observables in the dilated ricochet reduction

The transposed encoding observables of Definition 4.2 act on the reference
register. Simultaneous local Naimark dilation realizes the receiver POVMs
as projective measurements, giving three families of reflections with
cross-party commutation.
-/

open scoped ComplexOrder MatrixOrder Kronecker

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh ub uc

/-- The reflection associated with a binary projective measurement. -/
def binaryProjectiveReflection {a : Type*} [Fintype a] [DecidableEq a]
    (P : ProjectiveMeasurement Bool a) : CMatrix a :=
  1 - (2 : ℂ) • P.effects true

theorem binaryProjectiveReflection_isHermitian
    {a : Type*} [Fintype a] [DecidableEq a]
    (P : ProjectiveMeasurement Bool a) :
    (binaryProjectiveReflection P).IsHermitian := by
  exact Matrix.isHermitian_one.sub
    ((P.isHermitian true).smul (IsSelfAdjoint.natCast 2))

theorem binaryProjectiveReflection_mul_self
    {a : Type*} [Fintype a] [DecidableEq a]
    (P : ProjectiveMeasurement Bool a) :
    binaryProjectiveReflection P * binaryProjectiveReflection P = 1 := by
  simp only [binaryProjectiveReflection, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    P.idempotent true]
  module

theorem binaryProjective_effect_eq
    {a : Type*} [Fintype a] [DecidableEq a]
    (P : ProjectiveMeasurement Bool a) (b : Bool) :
    P.effects b =
      (2 : ℂ)⁻¹ • (1 + bitSign b • binaryProjectiveReflection P) := by
  cases b
  · have hsum := P.sum_eq_one
    rw [Fintype.sum_bool] at hsum
    simp only [bitSign_false, one_smul, binaryProjectiveReflection]
    rw [← hsum]
    module
  · simp only [bitSign_true, neg_smul, binaryProjectiveReflection]
    module

section Attack

variable {κ : Type uκ} {h : Type uh} {bob : Type ub} {charlie : Type uc}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype h] [DecidableEq h] [Nonempty h]
variable [Fintype bob] [DecidableEq bob] [Nonempty bob]
variable [Fintype charlie] [DecidableEq charlie] [Nonempty charlie]
variable {F : ReflectionFamily κ h}
variable (attack : ReflectionCloningAttack F bob charlie)

/-- Bob's common finite-family Naimark space. -/
abbrev ReflectionAttackBobSpace := POVM.FamilyNaimarkSpace attack.bobMeasure

/-- Charlie's common finite-family Naimark space. -/
abbrev ReflectionAttackCharlieSpace := POVM.FamilyNaimarkSpace attack.charlieMeasure

/-- Basis of the joint reference--Bob--Charlie space after dilation. -/
abbrev ReflectionAttackHilbert :=
  h × (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack)

def reflectionAttackBobProjective (θ : κ) :
    ProjectiveMeasurement Bool (ReflectionAttackBobSpace attack) :=
  POVM.familyNaimarkProjectiveMeasurement attack.bobMeasure θ

def reflectionAttackCharlieProjective (θ : κ) :
    ProjectiveMeasurement Bool (ReflectionAttackCharlieSpace attack) :=
  POVM.familyNaimarkProjectiveMeasurement attack.charlieMeasure θ

/-- Normalized Choi state followed by the two local common dilations. -/
def reflectionAttackDilationState : State (ReflectionAttackHilbert attack) :=
  spectatorReceiverLift attack.bobMeasure attack.charlieMeasure
    (normalizedChoi attack.pirate)

/-- The transposed encoding observable `Θₖ` of equation (23), lifted to
the common space. -/
def reflectionAttackAlice (θ : κ) : CMatrix (ReflectionAttackHilbert attack) :=
  Matrix.kronecker (Matrix.transpose (F.Q θ))
    (1 : CMatrix
      (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack))

/-- Bob's projective reflection on the common space. -/
def reflectionAttackBob (θ : κ) : CMatrix (ReflectionAttackHilbert attack) :=
  Matrix.kronecker (1 : CMatrix h)
    (Matrix.kronecker
      (binaryProjectiveReflection (reflectionAttackBobProjective attack θ))
      (1 : CMatrix (ReflectionAttackCharlieSpace attack)))

/-- Charlie's projective reflection on the common space. -/
def reflectionAttackCharlie (θ : κ) : CMatrix (ReflectionAttackHilbert attack) :=
  Matrix.kronecker (1 : CMatrix h)
    (Matrix.kronecker (1 : CMatrix (ReflectionAttackBobSpace attack))
      (binaryProjectiveReflection (reflectionAttackCharlieProjective attack θ)))

theorem reflectionAttackAlice_isHermitian (θ : κ) :
    (reflectionAttackAlice attack θ).IsHermitian := by
  rw [Matrix.IsHermitian, reflectionAttackAlice, Matrix.kronecker,
    Matrix.conjTranspose_kronecker, (F.Q_hermitian θ).transpose.eq,
    Matrix.conjTranspose_one]

theorem reflectionAttackAlice_mul_self (θ : κ) :
    reflectionAttackAlice attack θ * reflectionAttackAlice attack θ = 1 := by
  change
    ((Matrix.transpose (F.Q θ)) ⊗ₖ
        (1 : CMatrix
          (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack))) *
      ((Matrix.transpose (F.Q θ)) ⊗ₖ
        (1 : CMatrix
          (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack))) = 1
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have htranspose := congrArg Matrix.transpose (F.Q_involution θ)
  rw [show Matrix.transpose (F.Q θ) * Matrix.transpose (F.Q θ) = 1 by
    simpa [Matrix.transpose_mul] using htranspose]
  exact Matrix.one_kronecker_one

theorem reflectionAttackBob_isHermitian (θ : κ) :
    (reflectionAttackBob attack θ).IsHermitian := by
  simp only [Matrix.IsHermitian, reflectionAttackBob, Matrix.kronecker,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    (binaryProjectiveReflection_isHermitian
      (reflectionAttackBobProjective attack θ)).eq]

theorem reflectionAttackBob_mul_self (θ : κ) :
    reflectionAttackBob attack θ * reflectionAttackBob attack θ = 1 := by
  let r := binaryProjectiveReflection (reflectionAttackBobProjective attack θ)
  change
    ((1 : CMatrix h) ⊗ₖ
        (r ⊗ₖ (1 : CMatrix (ReflectionAttackCharlieSpace attack)))) *
      ((1 : CMatrix h) ⊗ₖ
        (r ⊗ₖ (1 : CMatrix (ReflectionAttackCharlieSpace attack)))) = 1
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    binaryProjectiveReflection_mul_self]
  simp

theorem reflectionAttackCharlie_isHermitian (θ : κ) :
    (reflectionAttackCharlie attack θ).IsHermitian := by
  simp only [Matrix.IsHermitian, reflectionAttackCharlie, Matrix.kronecker,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    (binaryProjectiveReflection_isHermitian
      (reflectionAttackCharlieProjective attack θ)).eq]

theorem reflectionAttackCharlie_mul_self (θ : κ) :
    reflectionAttackCharlie attack θ * reflectionAttackCharlie attack θ = 1 := by
  let r := binaryProjectiveReflection (reflectionAttackCharlieProjective attack θ)
  change
    ((1 : CMatrix h) ⊗ₖ
        ((1 : CMatrix (ReflectionAttackBobSpace attack)) ⊗ₖ r)) *
      ((1 : CMatrix h) ⊗ₖ
        ((1 : CMatrix (ReflectionAttackBobSpace attack)) ⊗ₖ r)) = 1
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    binaryProjectiveReflection_mul_self]
  simp

/-- The reference and Bob observables commute for every pair of keys. -/
theorem reflectionAttackAlice_commute_bob (θ φ : κ) :
    reflectionAttackAlice attack θ * reflectionAttackBob attack φ =
      reflectionAttackBob attack φ * reflectionAttackAlice attack θ := by
  let Q := Matrix.transpose (F.Q θ)
  let r := binaryProjectiveReflection (reflectionAttackBobProjective attack φ)
  change
    (Q ⊗ₖ (1 : CMatrix
      (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack))) *
        ((1 : CMatrix h) ⊗ₖ
          (r ⊗ₖ (1 : CMatrix (ReflectionAttackCharlieSpace attack)))) =
      ((1 : CMatrix h) ⊗ₖ
          (r ⊗ₖ (1 : CMatrix (ReflectionAttackCharlieSpace attack)))) *
        (Q ⊗ₖ (1 : CMatrix
          (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack)))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- The reference and Charlie observables commute for every pair of keys. -/
theorem reflectionAttackAlice_commute_charlie (θ φ : κ) :
    reflectionAttackAlice attack θ * reflectionAttackCharlie attack φ =
      reflectionAttackCharlie attack φ * reflectionAttackAlice attack θ := by
  let Q := Matrix.transpose (F.Q θ)
  let r := binaryProjectiveReflection (reflectionAttackCharlieProjective attack φ)
  change
    (Q ⊗ₖ (1 : CMatrix
      (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack))) *
        ((1 : CMatrix h) ⊗ₖ
          ((1 : CMatrix (ReflectionAttackBobSpace attack)) ⊗ₖ r)) =
      ((1 : CMatrix h) ⊗ₖ
          ((1 : CMatrix (ReflectionAttackBobSpace attack)) ⊗ₖ r)) *
        (Q ⊗ₖ (1 : CMatrix
          (ReflectionAttackBobSpace attack × ReflectionAttackCharlieSpace attack)))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- Bob and Charlie commute for every pair of settings because they act on
distinct receiver factors. -/
theorem reflectionAttackBob_commute_charlie (θ φ : κ) :
    reflectionAttackBob attack θ * reflectionAttackCharlie attack φ =
      reflectionAttackCharlie attack φ * reflectionAttackBob attack θ := by
  let r := binaryProjectiveReflection (reflectionAttackBobProjective attack θ)
  let s := binaryProjectiveReflection (reflectionAttackCharlieProjective attack φ)
  change
    ((1 : CMatrix h) ⊗ₖ
        (r ⊗ₖ (1 : CMatrix (ReflectionAttackCharlieSpace attack)))) *
        ((1 : CMatrix h) ⊗ₖ
          ((1 : CMatrix (ReflectionAttackBobSpace attack)) ⊗ₖ s)) =
      ((1 : CMatrix h) ⊗ₖ
          ((1 : CMatrix (ReflectionAttackBobSpace attack)) ⊗ₖ s)) *
        ((1 : CMatrix h) ⊗ₖ
          (r ⊗ₖ (1 : CMatrix (ReflectionAttackCharlieSpace attack))))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- The dilated local product effect has the two-reflection form. -/
theorem reflectionAttackDilatedProductEffect_eq (θ : κ) (b : Bool) :
    Matrix.kronecker (1 : CMatrix h)
        (receiverFamilyProjector attack.bobMeasure attack.charlieMeasure θ b b) =
      ((2 : ℂ)⁻¹ • (1 + bitSign b • reflectionAttackBob attack θ)) *
        ((2 : ℂ)⁻¹ • (1 + bitSign b • reflectionAttackCharlie attack θ)) := by
  rw [show receiverFamilyProjector attack.bobMeasure attack.charlieMeasure θ b b =
      Matrix.kronecker
        ((reflectionAttackBobProjective attack θ).effects b)
        ((reflectionAttackCharlieProjective attack θ).effects b) from rfl,
    binaryProjective_effect_eq, binaryProjective_effect_eq]
  let rB := binaryProjectiveReflection (reflectionAttackBobProjective attack θ)
  let rC := binaryProjectiveReflection (reflectionAttackCharlieProjective attack θ)
  let EB : CMatrix (ReflectionAttackBobSpace attack) :=
    (2 : ℂ)⁻¹ • (1 + bitSign b • rB)
  let EC : CMatrix (ReflectionAttackCharlieSpace attack) :=
    (2 : ℂ)⁻¹ • (1 + bitSign b • rC)
  have hB :
      (2 : ℂ)⁻¹ • (1 + bitSign b • reflectionAttackBob attack θ) =
        Matrix.kronecker (1 : CMatrix h)
          (Matrix.kronecker EB (1 : CMatrix (ReflectionAttackCharlieSpace attack))) := by
    simp [reflectionAttackBob, EB, rB, Matrix.add_kronecker,
      Matrix.kronecker_add, Matrix.smul_kronecker, Matrix.kronecker_smul]
  have hC :
      (2 : ℂ)⁻¹ • (1 + bitSign b • reflectionAttackCharlie attack θ) =
        Matrix.kronecker (1 : CMatrix h)
          (Matrix.kronecker (1 : CMatrix (ReflectionAttackBobSpace attack)) EC) := by
    simp [reflectionAttackCharlie, EC, rC, Matrix.kronecker_add,
      Matrix.kronecker_smul]
  rw [hB, hC]
  change
    (1 : CMatrix h) ⊗ₖ (EB ⊗ₖ EC) =
      ((1 : CMatrix h) ⊗ₖ
          (EB ⊗ₖ (1 : CMatrix (ReflectionAttackCharlieSpace attack)))) *
        ((1 : CMatrix h) ⊗ₖ
          ((1 : CMatrix (ReflectionAttackBobSpace attack)) ⊗ₖ EC))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

end Attack

end


end UE.PauliConstructionAndProof
