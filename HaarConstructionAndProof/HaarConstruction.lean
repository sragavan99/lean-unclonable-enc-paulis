import HaarConstructionAndProof.HaarMeasure
import PauliConstructionAndProof.Construction

/-!
# Haar-random conjugate-subspace bit encryption

At parameter `n` the ciphertext has `q = n+1` qubits.  A key is genuinely
Haar-random in a chosen closed subgroup of `U(2^q)`.  The bit state is the
uniform state on one eigenspace of the first-qubit `Z`, conjugated by the key.
The decoder uses the conjugated eigenspace measurement.
-/

open scoped ComplexOrder MatrixOrder NNReal
open MeasureTheory

namespace UE.PauliConstructionAndProof

open QIT UE

noncomputable section

/-- A parameter-indexed family of compact unitary subgroups containing the
literal Clifford normalizer subgroup. -/
structure HaarSubgroupFamily where
  group : (n : ℕ) →
    ClosedSubgroup (Matrix.unitaryGroup (Fin (2 ^ (n + 1))) ℂ)
  containsClifford : ∀ n, cliffordSubgroup (n + 1) ≤ (group n).toSubgroup

/-- The full unitary groups form a Haar subgroup family. -/
def fullUnitaryHaarFamily : HaarSubgroupFamily where
  group n :=
    { toSubgroup := ⊤
      isClosed' := isClosed_univ }
  containsClifford _ := le_top

/-- The stored key distribution associated with normalized subgroup Haar
measure. -/
def haarKeyDistribution {q : ℕ}
    (H : ClosedSubgroup (Matrix.unitaryGroup (Fin (2 ^ q)) ℂ)) :
    KeyDistribution where
  Key := H
  measurableSpace := inferInstance
  μ := closedSubgroupHaarMeasure H
  isProbability := closedSubgroupHaarMeasure_isProbabilityMeasure H

/-- Unitary conjugation of a finite density state. -/
def conjugateState {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (U : Matrix.unitaryGroup a ℂ) : State a where
  matrix := (U : CMatrix a) * rho.matrix * star (U : CMatrix a)
  pos := by
    simpa [Matrix.star_eq_conjTranspose] using
      rho.pos.mul_mul_conjTranspose_same (U : CMatrix a)
  trace_eq_one := by
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
      rho.trace_eq_one]

@[simp]
theorem conjugateState_matrix {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (U : Matrix.unitaryGroup a ℂ) :
    (conjugateState rho U).matrix =
      (U : CMatrix a) * rho.matrix * star (U : CMatrix a) :=
  rfl

/-- The conjugated first-`Z` decryption projection. -/
def haarDecryptionEffect (H : HaarSubgroupFamily) (n : ℕ)
    (U : (H.group n)) (b : Bool) : CMatrix (Fin (2 ^ (n + 1))) :=
  (U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
    pauliDecryptionEffect (firstZPauliKey n) b *
    star (U.1 : CMatrix (Fin (2 ^ (n + 1))))

theorem haarDecryptionEffect_pos (H : HaarSubgroupFamily) (n : ℕ)
    (U : H.group n) (b : Bool) :
    (haarDecryptionEffect H n U b).PosSemidef := by
  simpa [haarDecryptionEffect, Matrix.star_eq_conjTranspose] using
    (pauliDecryptionEffect_pos (firstZPauliKey n) b).mul_mul_conjTranspose_same
      (U.1 : CMatrix (Fin (2 ^ (n + 1))))

theorem haarDecryptionEffect_isHermitian (H : HaarSubgroupFamily) (n : ℕ)
    (U : H.group n) (b : Bool) :
    (haarDecryptionEffect H n U b).IsHermitian :=
  (haarDecryptionEffect_pos H n U b).isHermitian

theorem haarDecryptionEffect_idempotent (H : HaarSubgroupFamily) (n : ℕ)
    (U : H.group n) (b : Bool) :
    haarDecryptionEffect H n U b * haarDecryptionEffect H n U b =
      haarDecryptionEffect H n U b := by
  have hU := Unitary.coe_star_mul_self U.1
  have hU' :
      ((star U.1 : Matrix.unitaryGroup (Fin (2 ^ (n + 1))) ℂ) :
          CMatrix (Fin (2 ^ (n + 1)))) *
        (U.1 : CMatrix (Fin (2 ^ (n + 1)))) = 1 := by
    simpa using hU
  have hE := pauliDecryptionEffect_idempotent (firstZPauliKey n) b
  unfold haarDecryptionEffect
  calc
    ((U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
          pauliDecryptionEffect (firstZPauliKey n) b * star U.1) *
        ((U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
          pauliDecryptionEffect (firstZPauliKey n) b * star U.1) =
      (U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
        pauliDecryptionEffect (firstZPauliKey n) b * (star U.1 * U.1) *
        pauliDecryptionEffect (firstZPauliKey n) b * star U.1 := by
          noncomm_ring
    _ = (U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
        pauliDecryptionEffect (firstZPauliKey n) b *
        pauliDecryptionEffect (firstZPauliKey n) b * star U.1 := by rw [hU']; simp
    _ = (U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
        (pauliDecryptionEffect (firstZPauliKey n) b *
          pauliDecryptionEffect (firstZPauliKey n) b) * star U.1 := by
            noncomm_ring
    _ = (U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
        pauliDecryptionEffect (firstZPauliKey n) b * star U.1 := by rw [hE]

theorem haarDecryptionEffect_trace (H : HaarSubgroupFamily) (n : ℕ)
    (U : H.group n) (b : Bool) :
    (haarDecryptionEffect H n U b).trace =
      ((2 ^ (n + 1) : ℕ) : ℂ) / 2 := by
  unfold haarDecryptionEffect
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    pauliDecryptionEffect_trace]

theorem haarDecryptionEffect_complement (H : HaarSubgroupFamily) (n : ℕ)
    (U : H.group n) (b : Bool) :
    1 - haarDecryptionEffect H n U b =
      haarDecryptionEffect H n U (!b) := by
  have hU := Unitary.coe_mul_star_self U.1
  have hbase := pauliDecryptionEffect_complement (firstZPauliKey n) b
  unfold haarDecryptionEffect
  calc
    1 - (U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
          pauliDecryptionEffect (firstZPauliKey n) b * star U.1 =
        (U.1 : CMatrix (Fin (2 ^ (n + 1)))) * 1 * star U.1 -
          (U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
            pauliDecryptionEffect (firstZPauliKey n) b * star U.1 := by
              rw [Matrix.mul_one, hU]
    _ = (U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
          (1 - pauliDecryptionEffect (firstZPauliKey n) b) * star U.1 := by
            noncomm_ring
    _ = (U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
          pauliDecryptionEffect (firstZPauliKey n) (!b) * star U.1 := by
            rw [hbase]

theorem haarDecryptionEffect_le_one (H : HaarSubgroupFamily) (n : ℕ)
    (U : H.group n) (b : Bool) :
    haarDecryptionEffect H n U b ≤ 1 := by
  rw [Matrix.le_iff, haarDecryptionEffect_complement]
  exact haarDecryptionEffect_pos H n U (!b)

/-- The conjugated two-eigenspace decoding POVM. -/
def haarPOVM (H : HaarSubgroupFamily) (n : ℕ) (U : H.group n) :
    POVM Bool (Fin (2 ^ (n + 1))) :=
  POVM.binaryOfEffect (haarDecryptionEffect H n U true)
    (haarDecryptionEffect_pos H n U true)
    (haarDecryptionEffect_le_one H n U true)

@[simp]
theorem haarPOVM_effects (H : HaarSubgroupFamily) (n : ℕ)
    (U : H.group n) (b : Bool) :
    (haarPOVM H n U).effects b = haarDecryptionEffect H n U b := by
  cases b
  · change 1 - haarDecryptionEffect H n U true =
      haarDecryptionEffect H n U false
    exact haarDecryptionEffect_complement H n U true
  · rfl

/-- The Haar ciphertext is the conjugated uniform first-`Z` eigenspace state. -/
def haarCiphertextState (H : HaarSubgroupFamily) (n : ℕ)
    (U : H.group n) (b : Bool) : State (Fin (2 ^ (n + 1))) :=
  conjugateState (pauliCiphertextState (firstZPauliKey n) b) U.1

theorem haarCiphertextState_matrix_effect (H : HaarSubgroupFamily) (n : ℕ)
    (U : H.group n) (b : Bool) :
    (haarCiphertextState H n U b).matrix =
      (2 / (2 ^ (n + 1) : ℝ)) • haarDecryptionEffect H n U b := by
  simp only [haarCiphertextState, conjugateState_matrix,
    pauliCiphertextState_matrix, haarDecryptionEffect]
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- The concrete continuous-key Haar encryption family. -/
def haarBitEncryption (H : HaarSubgroupFamily) : BitEncryptionFamily where
  cipherDim n := 2 ^ (n + 1)
  cipherDim_pos _ := by positivity
  keys n := haarKeyDistribution (H.group n)
  encrypt n U b := haarCiphertextState H n U b
  encrypt_measurable := by
    intro n b i j
    change Measurable (fun U : H.group n =>
      ((U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
        (pauliCiphertextState (firstZPauliKey n) b).matrix *
        star (U.1 : CMatrix (Fin (2 ^ (n + 1))))) i j)
    exact (by fun_prop : Continuous (fun U : H.group n =>
      ((U.1 : CMatrix (Fin (2 ^ (n + 1)))) *
        (pauliCiphertextState (firstZPauliKey n) b).matrix *
        star (U.1 : CMatrix (Fin (2 ^ (n + 1))))) i j)).measurable

/-- The key-dependent decoder measures the conjugated first-`Z` eigenspaces. -/
def haarDecryption (H : HaarSubgroupFamily) :
    (haarBitEncryption H).DecryptionFamily :=
  fun n U => Channel.measure (haarPOVM H n U)

private theorem coordinate_probability_after_measure_haar
    {a : Type*} [Fintype a] [DecidableEq a]
    (M : POVM Bool a) (rho : State a) (b : Bool) :
    BitEncryptionFamily.computationalOutcomeProbability
        ((Channel.measure M).applyState rho) b =
      (M.prob rho b : ℝ) := by
  have hcoordinate (sigma : State Bool) :
      BitEncryptionFamily.computationalOutcomeProbability sigma b =
        Complex.re (sigma.matrix b b) := by
    rw [BitEncryptionFamily.computationalOutcomeProbability,
      POVM.prob_eq_trace_re]
    cases b <;> simp [Matrix.trace, Matrix.mul_apply]
  rw [hcoordinate]
  change Complex.re (((Channel.measure M).map rho.matrix) b b) = _
  rw [Channel.measure_map_state_diagonal]
  simp [POVM.prob_eq_trace_re]

theorem haarPOVM_honest_probability (H : HaarSubgroupFamily) (n : ℕ)
    (U : H.group n) (b : Bool) :
    ((haarPOVM H n U).prob (haarCiphertextState H n U b) b : ℝ) = 1 := by
  rw [POVM.prob_eq_trace_re, haarPOVM_effects,
    haarCiphertextState_matrix_effect]
  rw [Matrix.smul_mul, haarDecryptionEffect_idempotent,
    Matrix.trace_smul, haarDecryptionEffect_trace]
  norm_num [Complex.real_smul]

/-- Haar encryption and conjugated-eigenspace decoding are perfectly correct. -/
theorem haarPerfectlyCorrect (H : HaarSubgroupFamily) :
    (haarBitEncryption H).PerfectlyCorrect (haarDecryption H) := by
  intro n U b
  rw [show haarDecryption H n U = Channel.measure (haarPOVM H n U) from rfl]
  exact (coordinate_probability_after_measure_haar (haarPOVM H n U)
    (haarCiphertextState H n U b) b).trans
      (haarPOVM_honest_probability H n U b)

/-- The Haar scheme uses the same `n+1`-qubit ciphertext dimension as the
finite Pauli scheme. -/
theorem haarCipherDimension_polynomiallyBounded (H : HaarSubgroupFamily) :
    (haarBitEncryption H).PolynomiallyBoundedCipherDimension := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp only [haarBitEncryption, Nat.one_mul, pow_one]
  exact le_rfl

end

end UE.PauliConstructionAndProof
