import UE.Security

/-!
# Demonstration of the construction interface

The explicit scheme here stores the plaintext in a computational basis state.
It is perfectly correct and intentionally insecure.  Its purpose is only to
show that a later construction can expose concrete data and assemble a witness
after supplying separate negligibility and security proofs.
-/

open MeasureTheory

namespace UE.InterfaceDemo

open QIT

noncomputable section

private def unitKeys : KeyDistribution where
  Key := PUnit
  measurableSpace := ⊤
  μ := @Measure.dirac PUnit ⊤ PUnit.unit
  isProbability := ⟨by simp⟩

private def bitIndex (b : Bool) : Fin 2 :=
  ⟨b.toNat, by cases b <;> simp⟩

private def basisDecoder : Channel (Fin 2) Bool :=
  Channel.prepare fun i => Classical.basisState (Bool.ofNat i.val)

/-- A concrete basis-state encryption family used to exercise the interface. -/
def candidateEncryption : BitEncryptionFamily where
  cipherDim _ := 2
  cipherDim_pos _ := by decide
  keys _ := unitKeys
  encrypt _ _ b := Classical.basisState (bitIndex b)
  encrypt_measurable := by
    intro n b i j
    letI := (unitKeys).measurableSpace
    exact measurable_const

/-- The concrete decoder for `candidateEncryption`. -/
def candidateDecryption : candidateEncryption.DecryptionFamily :=
  fun _ _ => basisDecoder

private theorem basisDecoder_apply (b : Bool) :
    basisDecoder.applyState (Classical.basisState (bitIndex b)) =
      Classical.basisState b := by
  apply State.ext
  change basisDecoder.map (Classical.basisState (bitIndex b)).matrix =
    (Classical.basisState b).matrix
  rw [Classical.basisState_matrix, show basisDecoder =
    Channel.prepare (fun i : Fin 2 => Classical.basisState (Bool.ofNat i.val)) from rfl,
    Channel.prepare_map_single_eq]
  simpa [bitIndex] using congrArg
    (fun x => (Classical.basisState x).matrix) (Bool.ofNat_toNat b)

private theorem coordinate_basis_probability (b : Bool) :
    BitEncryptionFamily.computationalOutcomeProbability
      (Classical.basisState b) b = 1 := by
  rw [BitEncryptionFamily.computationalOutcomeProbability,
    POVM.prob_eq_trace_re]
  cases b <;>
    simp [Classical.basisState, Matrix.trace, Matrix.mul_apply, Matrix.single]

/-- The demonstration encryption and decryption families are perfectly correct. -/
theorem candidate_correct :
    candidateEncryption.PerfectlyCorrect candidateDecryption := by
  intro n k b
  rw [show candidateDecryption n k = basisDecoder from rfl]
  change BitEncryptionFamily.computationalOutcomeProbability
    (basisDecoder.applyState (Classical.basisState (bitIndex b))) b = 1
  rw [basisDecoder_apply]
  exact coordinate_basis_probability b

/-- The two-dimensional demonstration ciphertext fits in one qubit for every
security parameter. -/
theorem candidate_cipherDimension_polynomiallyBounded :
    candidateEncryption.PolynomiallyBoundedCipherDimension := by
  refine ⟨1, 0, ?_⟩
  intro n
  norm_num [candidateEncryption]

/-- The zero error function used to demonstrate witness assembly. -/
def candidateError : ℕ → ℝ :=
  fun _ => 0

/-- Assemble concrete data into a complete witness once negligibility and the
dimension bound and universal security theorem have been proved. -/
def assembleCandidate
    (hdim : candidateEncryption.PolynomiallyBoundedCipherDimension)
    (hnegl : Negligible candidateError)
    (hsec : candidateEncryption.DeltaSecure candidateError) :
    SecureBitEncryption :=
  { encryption := candidateEncryption
    decryption := candidateDecryption
    perfectCorrectness := candidate_correct
    cipherDimension_polynomiallyBounded := hdim
    error := candidateError
    error_negligible := hnegl
    security := hsec }

end

end UE.InterfaceDemo
