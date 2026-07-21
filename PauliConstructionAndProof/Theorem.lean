import PauliConstructionAndProof.Assembly

/-!
# Public Pauli endpoints

The Pauli endpoint uses `q = n + 1` ciphertext qubits at protected security
parameter `n`, and exposes the exact correction
`1/2 * sqrt (2^(n+1) / (4^(n+1)-1))`.

-/

namespace UE.PauliConstructionAndProof

open UE

noncomputable section

/-- Complete Pauli bit encryption with exact finite-parameter error. -/
def pauliConstructionSecure : SecureBitEncryption :=
  assemblePauliSecure

/-- The finite-key Pauli construction witnesses uncloneable-bit existence. -/
theorem pauliConstructionProvesUncloneableBit : UncloneableBitExists :=
  ⟨pauliConstructionSecure⟩

end

end UE.PauliConstructionAndProof
