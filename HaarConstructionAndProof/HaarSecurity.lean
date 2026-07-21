import HaarConstructionAndProof.HaarConstruction
import PauliConstructionAndProof.Assembly

/-!
# Pauli-to-Haar security reduction

For a fixed Haar key `V`, preconjugating a Pauli ciphertext by `V` and asking
the original Haar measurements at `V * U_theta` gives a protected Pauli
attack.  The exact Pauli bound is integrated over `V`; finite sums commute
with the integral and right Haar invariance removes each `U_theta`.
-/

open scoped ComplexOrder MatrixOrder
open MeasureTheory

namespace UE.PauliConstructionAndProof

open QIT UE

noncomputable section

/-- A chosen Clifford representative, regarded as an element of the selected
closed subgroup by literal Clifford containment. -/
def haarPauliRepresentative (H : HaarSubgroupFamily) (n : ℕ)
    (k : PauliKey (n + 1)) : H.group n := by
  let W := Classical.choose (exists_clifford_conjugates_firstZ n k)
  have hW := Classical.choose_spec (exists_clifford_conjugates_firstZ n k)
  exact ⟨W, H.containsClifford n hW.1⟩

theorem haarPauliRepresentative_conjugates_firstZ
    (H : HaarSubgroupFamily) (n : ℕ) (k : PauliKey (n + 1)) :
    ((haarPauliRepresentative H n k).1 : CMatrix (Fin (2 ^ (n + 1)))) *
        pauli (firstZLabel n) *
        star ((haarPauliRepresentative H n k).1 :
          CMatrix (Fin (2 ^ (n + 1)))) = pauli k.1 := by
  exact (Classical.choose_spec (exists_clifford_conjugates_firstZ n k)).2

theorem haarPauliRepresentative_conjugates_effect
    (H : HaarSubgroupFamily) (n : ℕ) (k : PauliKey (n + 1)) (b : Bool) :
    ((haarPauliRepresentative H n k).1 : CMatrix (Fin (2 ^ (n + 1)))) *
        pauliDecryptionEffect (firstZPauliKey n) b *
        star ((haarPauliRepresentative H n k).1 :
          CMatrix (Fin (2 ^ (n + 1)))) =
      pauliDecryptionEffect k b := by
  have hU := Unitary.coe_mul_star_self (haarPauliRepresentative H n k).1
  have hZ := haarPauliRepresentative_conjugates_firstZ H n k
  have hU' :
      ((haarPauliRepresentative H n k).1 : CMatrix (Fin (2 ^ (n + 1)))) *
          star ((haarPauliRepresentative H n k).1 :
            CMatrix (Fin (2 ^ (n + 1)))) = 1 := by
    simp
  have hZ' :
      ((haarPauliRepresentative H n k).1 : CMatrix (Fin (2 ^ (n + 1)))) *
          (pauli (firstZPauliKey n).1 *
            star ((haarPauliRepresentative H n k).1 :
              CMatrix (Fin (2 ^ (n + 1))))) = pauli k.1 := by
    simpa only [Matrix.mul_assoc] using hZ
  unfold pauliDecryptionEffect
  noncomm_ring [hU', hZ']

theorem conjugateState_comp {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (U V : Matrix.unitaryGroup a ℂ) :
    conjugateState (conjugateState rho U) V = conjugateState rho (V * U) := by
  apply State.ext
  simp only [conjugateState_matrix]
  have hstar :
      star ((V * U : Matrix.unitaryGroup a ℂ) : CMatrix a) =
        star (U : CMatrix a) * star (V : CMatrix a) := by
    change star ((V : CMatrix a) * (U : CMatrix a)) = _
    exact star_mul (V : CMatrix a) (U : CMatrix a)
  rw [hstar]
  change
    (V : CMatrix a) *
        ((U : CMatrix a) * rho.matrix * star (U : CMatrix a)) *
        star (V : CMatrix a) =
      ((V : CMatrix a) * (U : CMatrix a)) * rho.matrix *
        (star (U : CMatrix a) * star (V : CMatrix a))
  simp only [Matrix.mul_assoc]

theorem haarPauliRepresentative_conjugates_ciphertext
    (H : HaarSubgroupFamily) (n : ℕ) (k : PauliKey (n + 1)) (b : Bool) :
    conjugateState (pauliCiphertextState (firstZPauliKey n) b)
        (haarPauliRepresentative H n k).1 =
      pauliCiphertextState k b := by
  apply State.ext
  rw [conjugateState_matrix, pauliCiphertextState_matrix,
    pauliCiphertextState_matrix, Matrix.mul_smul, Matrix.smul_mul,
    haarPauliRepresentative_conjugates_effect]

/-- Pointwise ciphertext identity used by the reduction. -/
theorem conjugate_pauliCiphertext_eq_haarCiphertext
    (H : HaarSubgroupFamily) (n : ℕ) (V : H.group n)
    (k : PauliKey (n + 1)) (b : Bool) :
    conjugateState (pauliCiphertextState k b) V.1 =
      haarCiphertextState H n (V * haarPauliRepresentative H n k) b := by
  rw [haarCiphertextState]
  rw [← haarPauliRepresentative_conjugates_ciphertext H n k b]
  exact conjugateState_comp _ _ _

/-- The channel `rho ↦ U rho U*`. -/
def conjugationChannel {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix.unitaryGroup a ℂ) : Channel a a where
  map := MatrixMap.ofKraus (fun (_ : Unit) => (U : CMatrix a))
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := by
    intro X
    simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
      Fintype.sum_unique]
    rw [← Matrix.star_eq_conjTranspose]
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem conjugationChannel_applyState {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix.unitaryGroup a ℂ) (rho : State a) :
    (conjugationChannel U).applyState rho = conjugateState rho U := by
  apply State.ext
  change (∑ _ : Unit, (U : CMatrix a) * rho.matrix *
      Matrix.conjTranspose (U : CMatrix a)) =
    (U : CMatrix a) * rho.matrix * star (U : CMatrix a)
  rw [Fintype.sum_unique, Matrix.star_eq_conjTranspose]

/-- The protected Pauli attack obtained by freezing the left Haar key `V`. -/
def haarAttackAsPauli (H : HaarSubgroupFamily) (n : ℕ)
    (attack : CloningAttack (haarBitEncryption H) n) (V : H.group n) :
    CloningAttack pauliBitEncryption n where
  bobDim := attack.bobDim
  charlieDim := attack.charlieDim
  bobDim_pos := attack.bobDim_pos
  charlieDim_pos := attack.charlieDim_pos
  pirate := attack.pirate.comp (conjugationChannel V.1)
  bobMeasure k := attack.bobMeasure (V * haarPauliRepresentative H n k)
  charlieMeasure k := attack.charlieMeasure (V * haarPauliRepresentative H n k)
  bobMeasure_measurable := by
    intro outcome i j
    exact measurable_from_top
  charlieMeasure_measurable := by
    intro outcome i j
    exact measurable_from_top

/-- Exact fixed-key score identity for the derived Pauli attack. -/
theorem haarAttackAsPauli_keyScore (H : HaarSubgroupFamily) (n : ℕ)
    (attack : CloningAttack (haarBitEncryption H) n) (V : H.group n)
    (k : PauliKey (n + 1)) :
    (haarAttackAsPauli H n attack V).keyScore k =
      attack.keyScore (V * haarPauliRepresentative H n k) := by
  unfold CloningAttack.keyScore
  apply congrArg ((2 : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro b _
  simp only [haarAttackAsPauli]
  have hstate :
      (attack.pirate.comp (conjugationChannel V.1)).applyState
          (pauliBitEncryption.encrypt n k b) =
        attack.pirate.applyState
          ((haarBitEncryption H).encrypt n
            (V * haarPauliRepresentative H n k) b) := by
    rw [Channel.applyState_comp, conjugationChannel_applyState]
    apply congrArg attack.pirate.applyState
    exact conjugate_pauliCiphertext_eq_haarCiphertext H n V k b
  apply congrArg (fun x : NNReal => (x : ℝ))
  exact congrArg
    (fun rho =>
      (jointPOVM
        (attack.bobMeasure (V * haarPauliRepresentative H n k))
        (attack.charlieMeasure (V * haarPauliRepresentative H n k))).prob
          rho (b, b)) hstate

/-- The success of the derived protected Pauli attack is the finite average of
right-translated Haar fixed-key scores. -/
theorem haarAttackAsPauli_success (H : HaarSubgroupFamily) (n : ℕ)
    (attack : CloningAttack (haarBitEncryption H) n) (V : H.group n) :
    cloningSuccess (haarAttackAsPauli H n attack V) =
      (Fintype.card (PauliKey (n + 1)) : ℝ)⁻¹ *
        ∑ k : PauliKey (n + 1),
          attack.keyScore (V * haarPauliRepresentative H n k) := by
  rw [cloningSuccess]
  change
    (letI : MeasurableSpace (PauliKey (n + 1)) := ⊤
      ∫ k : PauliKey (n + 1), (haarAttackAsPauli H n attack V).keyScore k
        ∂(PMF.uniformOfFintype (PauliKey (n + 1))).toMeasure) = _
  rw [integral_uniformKeyDistribution_eq_average]
  apply congrArg ((Fintype.card (PauliKey (n + 1)) : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro k _
  exact haarAttackAsPauli_keyScore H n attack V k

/-- The Pauli theorem gives the translated finite-average bound for every
fixed left Haar key. -/
theorem haar_translated_pauliAverage_le (H : HaarSubgroupFamily) (n : ℕ)
    (attack : CloningAttack (haarBitEncryption H) n) (V : H.group n) :
    (Fintype.card (PauliKey (n + 1)) : ℝ)⁻¹ *
        ∑ k : PauliKey (n + 1),
          attack.keyScore (V * haarPauliRepresentative H n k) ≤
      (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1)) := by
  rw [← haarAttackAsPauli_success H n attack V]
  exact cloningSuccess_le_exact n (haarAttackAsPauli H n attack V)

/-- A right translate of the Haar attack's fixed-key score is integrable. -/
theorem haarTranslatedKeyScore_integrable (H : HaarSubgroupFamily) (n : ℕ)
    (attack : CloningAttack (haarBitEncryption H) n)
    (k : PauliKey (n + 1)) :
    Integrable
      (fun V : H.group n =>
        attack.keyScore (V * haarPauliRepresentative H n k))
      (closedSubgroupHaarMeasure (H.group n)) := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact
      ((attack.keyScore_measurable).comp
        (continuous_mul_const (haarPauliRepresentative H n k)).measurable)
        |>.aestronglyMeasurable
  · filter_upwards [] with V
    rw [Real.norm_eq_abs,
      abs_of_nonneg (attack.keyScore_nonneg
        (V * haarPauliRepresentative H n k))]
    exact attack.keyScore_le_one (V * haarPauliRepresentative H n k)

/-- The finite average of translated fixed-key scores is integrable. -/
theorem haarPauliAverage_integrable (H : HaarSubgroupFamily) (n : ℕ)
    (attack : CloningAttack (haarBitEncryption H) n) :
    Integrable
      (fun V : H.group n =>
        (Fintype.card (PauliKey (n + 1)) : ℝ)⁻¹ *
          ∑ k : PauliKey (n + 1),
            attack.keyScore (V * haarPauliRepresentative H n k))
      (closedSubgroupHaarMeasure (H.group n)) := by
  apply Integrable.const_mul
  exact integrable_finsetSum Finset.univ fun k _ =>
    haarTranslatedKeyScore_integrable H n attack k

/-- Averaging the translated Pauli scores over Haar measure recovers exactly
the original Haar cloning success. -/
theorem integral_haarPauliAverage_eq_cloningSuccess
    (H : HaarSubgroupFamily) (n : ℕ)
    (attack : CloningAttack (haarBitEncryption H) n) :
    (∫ V : H.group n,
        (Fintype.card (PauliKey (n + 1)) : ℝ)⁻¹ *
          ∑ k : PauliKey (n + 1),
            attack.keyScore (V * haarPauliRepresentative H n k)
      ∂closedSubgroupHaarMeasure (H.group n)) =
      cloningSuccess attack := by
  have hpow : (1 : ℝ) < 4 ^ (n + 1) :=
    one_lt_pow₀ (by norm_num) (by omega)
  have hden : (4 : ℝ) ^ (n + 1) - 1 ≠ 0 := by linarith
  rw [integral_const_mul]
  rw [integral_finsetSum Finset.univ (fun k _ =>
    haarTranslatedKeyScore_integrable H n attack k)]
  simp_rw [closedSubgroupHaar_integral_mul_right]
  rw [Finset.sum_const]
  simp [cloningSuccess, haarBitEncryption, haarKeyDistribution]
  field_simp [hden]
  rfl

/-- Exact security for Haar conjugate-subspace encryption over every closed
subgroup family containing the Clifford subgroup.  The paper parameter is the
positive qubit count `q = n + 1`, so `d = 2^(n+1)` and the Pauli orbit has
`M = 4^(n+1) - 1` nonidentity elements. -/
theorem haarCloningSuccess_le_exact (H : HaarSubgroupFamily) (n : ℕ)
    (attack : CloningAttack (haarBitEncryption H) n) :
    cloningSuccess attack ≤
      (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1)) := by
  rw [← integral_haarPauliAverage_eq_cloningSuccess H n attack]
  have hbound := integral_mono
    (haarPauliAverage_integrable H n attack)
    (integrable_const
      ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1))))
    (haar_translated_pauliAverage_le H n attack)
  simpa using hbound

/-- Full-unitary Haar security is the top-subgroup instance of the arbitrary
closed-subgroup theorem. -/
theorem fullUnitaryHaar_cloningSuccess_le_exact (n : ℕ)
    (attack : CloningAttack
      (haarBitEncryption fullUnitaryHaarFamily) n) :
    cloningSuccess attack ≤
      (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Real.sqrt
        (((2 : ℝ) ^ (n + 1)) / ((4 : ℝ) ^ (n + 1) - 1)) :=
  haarCloningSuccess_le_exact fullUnitaryHaarFamily n attack

/-- Every admitted Haar subgroup family gives a secure bit encryption with
the same exact negligible correction as the finite Pauli construction. -/
def haarConstructionSecure (H : HaarSubgroupFamily) : SecureBitEncryption where
  encryption := haarBitEncryption H
  decryption := haarDecryption H
  perfectCorrectness := haarPerfectlyCorrect H
  cipherDimension_polynomiallyBounded :=
    haarCipherDimension_polynomiallyBounded H
  error := pauliSecurityError
  error_negligible := pauliSecurityError_negligible
  security := by
    intro n attack
    simpa [pauliSecurityError] using haarCloningSuccess_le_exact H n attack

/-- Secure-bit-encryption witness for Haar measure on the full unitary group. -/
def fullUnitaryHaarSecure : SecureBitEncryption :=
  haarConstructionSecure fullUnitaryHaarFamily

end

end UE.PauliConstructionAndProof
