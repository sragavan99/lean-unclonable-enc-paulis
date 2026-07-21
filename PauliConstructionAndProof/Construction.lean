import UE.Security
import PauliConstructionAndProof.Pauli
import PauliConstructionAndProof.FiniteProbability
import PauliConstructionAndProof.ReflectionConstruction

/-!
# The Pauli bit-encryption construction

This file packages the nonidentity Hermitian Paulis as the finite key space,
constructs the two eigenspace states and their binary decoding measurement,
and proves exact correctness and the ciphertext-dimension bound.
-/

open scoped ComplexOrder MatrixOrder NNReal

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

/-- The projection onto the `b`-labelled eigenspace of a Pauli reflection. -/
def pauliDecryptionEffect {q : ℕ} (k : PauliKey q) (b : Bool) :
    CMatrix (Fin (2 ^ q)) :=
  (2 : ℂ)⁻¹ • (1 + bitSign b • pauli k.1)

theorem pauliDecryptionEffect_isHermitian {q : ℕ} (k : PauliKey q) (b : Bool) :
    (pauliDecryptionEffect k b).IsHermitian := by
  cases b <;>
    simp [pauliDecryptionEffect, Matrix.IsHermitian,
      (pauli_isHermitian k.1).eq]

theorem pauliDecryptionEffect_idempotent {q : ℕ} (k : PauliKey q) (b : Bool) :
    pauliDecryptionEffect k b * pauliDecryptionEffect k b =
      pauliDecryptionEffect k b := by
  cases b <;>
    simp [pauliDecryptionEffect, Matrix.add_mul, Matrix.mul_add,
      pauli_mul_self]
  all_goals module

theorem pauliDecryptionEffect_pos {q : ℕ} (k : PauliKey q) (b : Bool) :
    (pauliDecryptionEffect k b).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self
    (pauliDecryptionEffect k b)
  rw [pauliDecryptionEffect_isHermitian k b,
    pauliDecryptionEffect_idempotent k b] at h
  exact h

theorem pauliDecryptionEffect_complement {q : ℕ} (k : PauliKey q) (b : Bool) :
    1 - pauliDecryptionEffect k b = pauliDecryptionEffect k (!b) := by
  cases b <;>
    simp [pauliDecryptionEffect]
  all_goals module

theorem pauliDecryptionEffect_le_one {q : ℕ} (k : PauliKey q) (b : Bool) :
    pauliDecryptionEffect k b ≤ 1 := by
  rw [Matrix.le_iff, pauliDecryptionEffect_complement]
  exact pauliDecryptionEffect_pos k (!b)

theorem pauliDecryptionEffect_orthogonal {q : ℕ} (k : PauliKey q) (b : Bool) :
    pauliDecryptionEffect k b * pauliDecryptionEffect k (!b) = 0 := by
  rw [← pauliDecryptionEffect_complement]
  rw [Matrix.mul_sub, Matrix.mul_one, pauliDecryptionEffect_idempotent]
  exact sub_self _

theorem pauliDecryptionEffect_trace {q : ℕ} (k : PauliKey q) (b : Bool) :
    (pauliDecryptionEffect k b).trace = ((2 ^ q : ℕ) : ℂ) / 2 := by
  simp [pauliDecryptionEffect, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_one, pauliKey_trace_eq_zero]
  ring

/-- The two Pauli eigenspace projections form the decoding POVM. -/
def pauliPOVM {q : ℕ} (k : PauliKey q) : POVM Bool (Fin (2 ^ q)) :=
  POVM.binaryOfEffect (pauliDecryptionEffect k true)
    (pauliDecryptionEffect_pos k true)
    (pauliDecryptionEffect_le_one k true)

@[simp]
theorem pauliPOVM_effects {q : ℕ} (k : PauliKey q) (b : Bool) :
    (pauliPOVM k).effects b = pauliDecryptionEffect k b := by
  cases b
  · change 1 - pauliDecryptionEffect k true = pauliDecryptionEffect k false
    exact pauliDecryptionEffect_complement k true
  · rfl

/-- The normalized state supported on the selected Pauli eigenspace. -/
def pauliCiphertextState {q : ℕ} (k : PauliKey q) (b : Bool) :
    State (Fin (2 ^ q)) where
  matrix := (2 / (2 ^ q : ℝ)) • pauliDecryptionEffect k b
  pos := (pauliDecryptionEffect_pos k b).smul (by positivity)
  trace_eq_one := by
    rw [Matrix.trace_smul, pauliDecryptionEffect_trace]
    norm_num [Complex.real_smul]

@[simp]
theorem pauliCiphertextState_matrix {q : ℕ} (k : PauliKey q) (b : Bool) :
    (pauliCiphertextState k b).matrix =
      (2 / (2 ^ q : ℝ)) • pauliDecryptionEffect k b :=
  rfl

/-- The ciphertext is exactly `d⁻¹ (I + (-1)^b P)`. -/
theorem pauliCiphertextState_matrix_explicit {q : ℕ}
    (k : PauliKey q) (b : Bool) :
    (pauliCiphertextState k b).matrix =
      (((2 ^ q : ℕ) : ℂ)⁻¹) • (1 + bitSign b • pauli k.1) := by
  ext i j
  simp only [pauliCiphertextState_matrix, pauliDecryptionEffect,
    Matrix.smul_apply, Complex.real_smul]
  have hq : (2 : ℝ) ^ q ≠ 0 := by positivity
  push_cast
  field_simp
  simp

/-- A nonidentity Pauli key exists at every security parameter. -/
instance pauliKey_nonempty (n : ℕ) : Nonempty (PauliKey (n + 1)) :=
  ⟨firstPauliKey n⟩

/-- The concrete Pauli bit-encryption family, with `n+1` qubits. -/
def pauliBitEncryption : BitEncryptionFamily where
  cipherDim n := 2 ^ (n + 1)
  cipherDim_pos n := by positivity
  keys n := uniformKeyDistribution (PauliKey (n + 1))
  encrypt n k b := pauliCiphertextState k b
  encrypt_measurable := by
    intro n b i j
    exact measurable_from_top

/-- The concrete decoder measures the two Pauli eigenspaces. -/
def pauliDecryption : pauliBitEncryption.DecryptionFamily :=
  fun _ k => Channel.measure (pauliPOVM k)

private theorem coordinate_probability_after_measure
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

theorem pauliPOVM_honest_probability {q : ℕ}
    (k : PauliKey q) (b : Bool) :
    ((pauliPOVM k).prob (pauliCiphertextState k b) b : ℝ) = 1 := by
  rw [POVM.prob_eq_trace_re, pauliPOVM_effects,
    pauliCiphertextState_matrix]
  rw [Matrix.smul_mul, pauliDecryptionEffect_idempotent,
    Matrix.trace_smul, pauliDecryptionEffect_trace]
  norm_num [Complex.real_smul]

/-- Honest Pauli encryption and decryption is perfectly correct. -/
theorem pauliPerfectlyCorrect :
    pauliBitEncryption.PerfectlyCorrect pauliDecryption := by
  intro n k b
  rw [show pauliDecryption n k = Channel.measure (pauliPOVM k) from rfl]
  exact (coordinate_probability_after_measure (pauliPOVM k)
    (pauliCiphertextState k b) b).trans (pauliPOVM_honest_probability k b)

/-- The `n+1`-qubit ciphertext dimension obeys the repository's polynomial
qubit-dimension condition. -/
theorem pauliCipherDimension_polynomiallyBounded :
    pauliBitEncryption.PolynomiallyBoundedCipherDimension := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp only [pauliBitEncryption, Nat.one_mul, pow_one]
  exact le_rfl

end

end UE.PauliConstructionAndProof
