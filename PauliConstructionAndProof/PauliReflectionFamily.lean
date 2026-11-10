import PauliConstructionAndProof.Pauli
import PauliConstructionAndProof.ReflectionConstruction

/-!
# The nonidentity Pauli reflection family

Proposition 2.3 makes the nonidentity Pauli keys of Definition 4.2 a family
of traceless Hermitian reflections.
-/

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

/-- The full nonidentity-Pauli family as route-neutral reflection data. -/
def pauliReflectionFamily (q : ℕ) :
    ReflectionFamily (PauliKey q) (Fin (2 ^ q)) where
  Q k := pauli k.1
  Q_hermitian k := pauli_isHermitian k.1
  Q_involution k := pauli_mul_self k.1
  Q_trace_zero k := pauliKey_trace_eq_zero k

end

end UE.PauliConstructionAndProof
