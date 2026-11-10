import PauliConstructionAndProof.PauliReflectionFamily
import PauliConstructionAndProof.Step2CorrelationProduct.ProofB.OrthogonalityData

/-!
# Pauli orthogonality for Proof B

Proposition 2.3 gives the trace identity used for the transposed Pauli
observables in §4.2.2.
-/

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

/-- Orthogonality data for Proof B of Lemma 4.4 on the Pauli key set. -/
def pauliAnanthSahaiData (q : ℕ) :
    AnanthSahaiData (pauliReflectionFamily q) where
  orthogonality θ φ := by
    change
      (Matrix.transpose (pauli θ.1) *
          Matrix.transpose (pauli φ.1)).trace =
        if θ = φ then (Fintype.card (Fin (2 ^ q)) : ℂ) else 0
    rw [← Matrix.transpose_mul, Matrix.trace_transpose, pauli_mul_trace]
    by_cases hθφ : θ = φ
    · subst φ
      simp
    · have hcoe : θ.1 ≠ φ.1 := fun h => hθφ (Subtype.ext h)
      simp [hθφ, Ne.symm hcoe]

/-- The ratio `d / K` of Lemma 4.4 for all nonidentity Paulis at Lean index `n`. -/
theorem pauliAnanthSahai_ratio (n : ℕ) :
    (Fintype.card (Fin (2 ^ (n + 1))) : ℝ) /
        (Fintype.card (PauliKey (n + 1)) : ℝ) =
      (2 : ℝ) ^ (n + 1) / ((4 : ℝ) ^ (n + 1) - 1) := by
  norm_num [Nat.cast_sub (by
    have : 1 ≤ 4 ^ (n + 1) := one_le_pow₀ (by omega)
    exact this)]

end

end UE.PauliConstructionAndProof
