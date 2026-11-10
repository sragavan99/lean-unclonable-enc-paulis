import PauliConstructionAndProof.Assembly

/-!
# Public Pauli theorems for ARS26

The public endpoints expose perfect correctness (Lemma 3.1), the exact
security bound (Theorem 4.1), and the negligible advantage for the same
nonidentity Pauli scheme. At Lean index `n`, the qubit count is `q = n + 1`.
-/

namespace UE.PauliConstructionAndProof

open UE

noncomputable section

/-- Perfect correctness of the Pauli scheme (Lemma 3.1). -/
theorem pauliConstructionPerfectlyCorrect :
    pauliBitEncryption.PerfectlyCorrect pauliDecryption :=
  pauliPerfectlyCorrect

/-- Secure Pauli encryption packaged using Proof A of Lemma 4.4. -/
def pauliConstructionSecure_ragavan : SecureBitEncryption :=
  assemblePauliSecure_ragavan

/-- Secure Pauli encryption packaged using Proof B of Lemma 4.4. -/
def pauliConstructionSecure_ananthSahai : SecureBitEncryption :=
  assemblePauliSecure_ananthSahai

/-- The default Pauli security package uses Proof A of Lemma 4.4. -/
def pauliConstructionSecure : SecureBitEncryption :=
  pauliConstructionSecure_ragavan

/-- Existence of secure one-bit unclonable encryption via Proof A. -/
theorem pauliConstructionProvesUncloneableBit_ragavan :
    UncloneableBitExists :=
  ⟨pauliConstructionSecure_ragavan⟩

/-- Existence of secure one-bit unclonable encryption via Proof B. -/
theorem pauliConstructionProvesUncloneableBit_ananthSahai :
    UncloneableBitExists :=
  ⟨pauliConstructionSecure_ananthSahai⟩

/-- The default existence witness uses the Proof A security package. -/
theorem pauliConstructionProvesUncloneableBit : UncloneableBitExists :=
  pauliConstructionProvesUncloneableBit_ragavan

end

end UE.PauliConstructionAndProof
