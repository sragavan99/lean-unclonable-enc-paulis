import QIT.Classical.Bridge
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Uncloneable-bit encryption: operational definitions

This module gives the finite-dimensional quantum interface for an encrypted bit,
key-dependent decryption, and information-theoretic cloning attacks.  It contains
no construction and makes no security assertion.
-/

open scoped BigOperators NNReal
open MeasureTheory Set Filter

namespace UE

open QIT

universe u

noncomputable section

/-- A possibly continuous key type equipped with its probability measure.

Use `letI := K.measurableSpace` and `letI := K.isProbability` locally when
Mathlib's measure-theory API expects the two structures as typeclass instances.
-/
structure KeyDistribution where
  /-- The type of secret keys. -/
  Key : Type u
  /-- The measurable structure used for key averaging. -/
  measurableSpace : MeasurableSpace Key
  /-- The probability measure from which keys are drawn. -/
  μ : @Measure Key measurableSpace
  /-- The stored key measure has total mass one. -/
  isProbability : @IsProbabilityMeasure Key measurableSpace μ

/-- An abstract family of bit ciphertext states indexed by a security parameter.

Ciphertext systems use the canonical finite register `Fin (cipherDim n)`.  The
entrywise measurability field permits continuous key distributions such as Haar
measure without requiring a bundled measurable structure on density operators.
-/
structure BitEncryptionFamily where
  /-- Ciphertext dimension at security parameter `n`. -/
  cipherDim : ℕ → ℕ
  /-- Every ciphertext register is nonzero. -/
  cipherDim_pos : ∀ n, 0 < cipherDim n
  /-- The probability distribution of keys at parameter `n`. -/
  keys : ℕ → KeyDistribution
  /-- The density operator encrypting bit `b` under key `k`. -/
  encrypt : ∀ n, (keys n).Key → Bool → State (Fin (cipherDim n))
  /-- Every matrix entry of an encryption state is measurable as a function of
  the key, for fixed parameter and plaintext bit. -/
  encrypt_measurable : ∀ n b i j,
    letI := (keys n).measurableSpace
    Measurable (fun k => (encrypt n k b).matrix i j)

namespace BitEncryptionFamily

/-- Concrete key-dependent CPTP decoders for an encryption family. -/
def DecryptionFamily (E : BitEncryptionFamily) :=
  ∀ n, (E.keys n).Key → Channel (Fin (E.cipherDim n)) Bool

/-- Probability of a Boolean computational-basis outcome in a Boolean state. -/
def computationalOutcomeProbability (ρ : State Bool) (b : Bool) : ℝ :=
  ((POVM.coordinate Bool).prob ρ b : ℝ)

/-- Perfect correctness: decrypting an honestly encrypted bit returns that bit
with probability exactly one in the computational basis. -/
def PerfectlyCorrect (E : BitEncryptionFamily) (D : E.DecryptionFamily) : Prop :=
  ∀ n k b,
    computationalOutcomeProbability ((D n k).applyState (E.encrypt n k b)) b = 1

end BitEncryptionFamily

/-- Tensor product of two finite POVMs, with paired outcomes and Kronecker-product
effects. -/
def jointPOVM {x y a b : Type*} [Fintype x] [Fintype y]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (M : POVM x a) (N : POVM y b) : POVM (x × y) (a × b) where
  effects outcome := Matrix.kronecker (M.effects outcome.1) (N.effects outcome.2)
  pos outcome := (M.pos outcome.1).kronecker (N.pos outcome.2)
  sum_eq_one := by
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨i', j'⟩
    have hM := congrArg (fun A : CMatrix a => A i i') M.sum_eq_one
    have hN := congrArg (fun A : CMatrix b => A j j') N.sum_eq_one
    simp only [Matrix.sum_apply] at hM hN
    simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, hM, hN]
    by_cases hi : i = i' <;> by_cases hj : j = j' <;>
      simp [Matrix.one_apply, hi, hj]

/-- A product POVM effect is exactly the Kronecker product of its two local
effects. -/
@[simp]
theorem jointPOVM_effects {x y a b : Type*} [Fintype x] [Fintype y]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (M : POVM x a) (N : POVM y b) (outcome : x × y) :
    (jointPOVM M N).effects outcome =
      Matrix.kronecker (M.effects outcome.1) (N.effects outcome.2) :=
  rfl

/-- The product-POVM probability is the paper's joint Born-rule trace formula. -/
theorem jointPOVM_prob_eq_trace_re {x y a b : Type*} [Fintype x] [DecidableEq x]
    [Fintype y] [DecidableEq y] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (M : POVM x a) (N : POVM y b)
    (ρ : State (a × b)) (outcome : x × y) :
    ((jointPOVM M N).prob ρ outcome : ℝ) =
      Complex.re ((Matrix.kronecker (M.effects outcome.1) (N.effects outcome.2) *
        ρ.matrix).trace) := by
  rw [POVM.prob_eq_trace_re, jointPOVM_effects, Matrix.trace_mul_comm]

/-- A finite-dimensional cloning attack after the ciphertext has been fixed.

The pirate channel has no key argument, so the split occurs before key reveal.
The two local POVMs are functions of the key and can therefore be selected after
the reveal.  The output dimensions are arbitrary positive natural numbers.
-/
structure CloningAttack (E : BitEncryptionFamily) (n : ℕ) where
  /-- Dimension of Bob's output register. -/
  bobDim : ℕ
  /-- Dimension of Charlie's output register. -/
  charlieDim : ℕ
  /-- Bob's register is nonzero. -/
  bobDim_pos : 0 < bobDim
  /-- Charlie's register is nonzero. -/
  charlieDim_pos : 0 < charlieDim
  /-- The key-independent CPTP map that splits the one ciphertext. -/
  pirate : Channel (Fin (E.cipherDim n)) (Fin bobDim × Fin charlieDim)
  /-- Bob's binary POVM, chosen after learning the key. -/
  bobMeasure : (E.keys n).Key → POVM Bool (Fin bobDim)
  /-- Charlie's binary POVM, chosen after learning the key. -/
  charlieMeasure : (E.keys n).Key → POVM Bool (Fin charlieDim)
  /-- Bob's POVM effects are entrywise measurable in the revealed key. -/
  bobMeasure_measurable : ∀ outcome i j,
    letI := (E.keys n).measurableSpace
    Measurable (fun k => (bobMeasure k).effects outcome i j)
  /-- Charlie's POVM effects are entrywise measurable in the revealed key. -/
  charlieMeasure_measurable : ∀ outcome i j,
    letI := (E.keys n).measurableSpace
    Measurable (fun k => (charlieMeasure k).effects outcome i j)

namespace CloningAttack

variable {E : BitEncryptionFamily} {n : ℕ}

/-- The conditional cloning success at a fixed key, averaged over a uniform
plaintext bit.  Success is the joint event in which both outcomes equal `b`. -/
def keyScore (T : CloningAttack E n) (k : (E.keys n).Key) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ b : Bool,
    ((jointPOVM (T.bobMeasure k) (T.charlieMeasure k)).prob
      (T.pirate.applyState (E.encrypt n k b)) (b, b) : ℝ)

/-- A fixed-key cloning score is nonnegative. -/
theorem keyScore_nonneg (T : CloningAttack E n) (k : (E.keys n).Key) :
    0 ≤ T.keyScore k := by
  unfold keyScore
  positivity

/-- A fixed-key cloning score is at most one. -/
theorem keyScore_le_one (T : CloningAttack E n) (k : (E.keys n).Key) :
    T.keyScore k ≤ 1 := by
  unfold keyScore
  rw [Fintype.sum_bool]
  have hfalse := POVM.prob_le_one
    (jointPOVM (T.bobMeasure k) (T.charlieMeasure k))
    (T.pirate.applyState (E.encrypt n k false)) (false, false)
  have htrue := POVM.prob_le_one
    (jointPOVM (T.bobMeasure k) (T.charlieMeasure k))
    (T.pirate.applyState (E.encrypt n k true)) (true, true)
  calc
    (2 : ℝ)⁻¹ *
        (((jointPOVM (T.bobMeasure k) (T.charlieMeasure k)).prob
            (T.pirate.applyState (E.encrypt n k true)) (true, true) : ℝ) +
          ((jointPOVM (T.bobMeasure k) (T.charlieMeasure k)).prob
            (T.pirate.applyState (E.encrypt n k false)) (false, false) : ℝ)) ≤
        (2 : ℝ)⁻¹ * (1 + 1) := by
      gcongr
    _ = 1 := by norm_num

private theorem channel_output_entry_measurable
    {κ a b : Type*} [MeasurableSpace κ] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (Φ : Channel a b) (ρ : κ → State a)
    (hρ : ∀ i j, Measurable (fun k => (ρ k).matrix i j)) (p q : b) :
    Measurable (fun k => (Φ.applyState (ρ k)).matrix p q) := by
  have hsum : Measurable (fun k => ∑ i : a, ∑ j : a,
      (ρ k).matrix i j * Φ.map (Matrix.single i j (1 : ℂ)) p q) := by
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact (hρ i j).mul measurable_const
  convert hsum using 1
  funext k
  rw [show (Φ.applyState (ρ k)).matrix = Φ.map (ρ k).matrix from rfl,
    MatrixMap.map_eq_sum_single]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

private theorem outcome_probability_measurable (T : CloningAttack E n) (b : Bool) :
    letI := (E.keys n).measurableSpace
    Measurable (fun k =>
      ((jointPOVM (T.bobMeasure k) (T.charlieMeasure k)).prob
        (T.pirate.applyState (E.encrypt n k b)) (b, b) : ℝ)) := by
  letI := (E.keys n).measurableSpace
  have hρ : ∀ p q,
      Measurable (fun k =>
        (T.pirate.applyState (E.encrypt n k b)).matrix p q) := by
    intro p q
    exact channel_output_entry_measurable T.pirate (fun k => E.encrypt n k b)
      (E.encrypt_measurable n b) p q
  have heffect : ∀ p q,
      Measurable (fun k =>
        Matrix.kronecker ((T.bobMeasure k).effects b)
          ((T.charlieMeasure k).effects b) p q) := by
    intro p q
    rcases p with ⟨pB, pC⟩
    rcases q with ⟨qB, qC⟩
    exact (T.bobMeasure_measurable b pB qB).mul
      (T.charlieMeasure_measurable b pC qC)
  have htrace : Measurable (fun k => Complex.re
      ((Matrix.kronecker ((T.bobMeasure k).effects b)
        ((T.charlieMeasure k).effects b) *
        (T.pirate.applyState (E.encrypt n k b)).matrix).trace)) := by
    apply Complex.measurable_re.comp
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.measurable_sum
    intro p _
    apply Finset.measurable_sum
    intro q _
    exact (heffect p q).mul (hρ q p)
  simpa only [jointPOVM_prob_eq_trace_re] using htrace

/-- The fixed-key cloning score is measurable under the attack's entrywise
admissibility hypotheses. -/
theorem keyScore_measurable (T : CloningAttack E n) :
    letI := (E.keys n).measurableSpace
    Measurable T.keyScore := by
  letI := (E.keys n).measurableSpace
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro b _
  exact outcome_probability_measurable T b

/-- The fixed-key cloning score is integrable against the stored key measure. -/
theorem keyScore_integrable (T : CloningAttack E n) :
    letI := (E.keys n).measurableSpace
    Integrable T.keyScore (E.keys n).μ := by
  letI := (E.keys n).measurableSpace
  letI := (E.keys n).isProbability
  refine Integrable.of_bound T.keyScore_measurable.aestronglyMeasurable 1 ?_
  filter_upwards [] with k
  rw [Real.norm_eq_abs, abs_of_nonneg (T.keyScore_nonneg k)]
  exact T.keyScore_le_one k

end CloningAttack

/-- Average cloning success over the scheme's genuine key probability measure. -/
def cloningSuccess {E : BitEncryptionFamily} {n : ℕ} (T : CloningAttack E n) : ℝ :=
  letI := (E.keys n).measurableSpace
  ∫ k, T.keyScore k ∂(E.keys n).μ

/-- The averaged cloning success is a probability in the real unit interval. -/
theorem cloningSuccess_mem_unit {E : BitEncryptionFamily} {n : ℕ}
    (T : CloningAttack E n) : cloningSuccess T ∈ Set.Icc (0 : ℝ) 1 := by
  letI := (E.keys n).measurableSpace
  letI := (E.keys n).isProbability
  constructor
  · exact integral_nonneg T.keyScore_nonneg
  · have hle := integral_mono T.keyScore_integrable (integrable_const (1 : ℝ))
      T.keyScore_le_one
    simpa [cloningSuccess] using hle

end

end UE
