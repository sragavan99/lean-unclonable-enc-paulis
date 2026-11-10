import PauliConstructionAndProof.ReflectionConstruction

/-!
# §4.2.2: reflection-family orthogonality data

The transposed observables from the ricochet reduction satisfy the
Hilbert--Schmidt trace identity of Proposition 2.3 in the Pauli instance.
-/

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

universe uκ uh

/-- Hilbert--Schmidt orthogonality for the reflection-family form of Proof B. -/
structure AnanthSahaiData
    {κ : Type uκ} {h : Type uh}
    [Fintype κ] [DecidableEq κ] [Fintype h] [DecidableEq h]
    (F : ReflectionFamily κ h) where
  orthogonality : ∀ θ φ,
    (Matrix.transpose (F.Q θ) * Matrix.transpose (F.Q φ)).trace =
      if θ = φ then (Fintype.card h : ℂ) else 0

end

end UE.PauliConstructionAndProof
