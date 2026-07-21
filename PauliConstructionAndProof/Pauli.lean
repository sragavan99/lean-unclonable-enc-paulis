import UE.Definitions
import QIT.Core.System
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-!
# Pauli construction: phase-free Hermitian matrices

This file develops the finite Pauli algebra needed by the construction.  Labels
and computational-basis indices are recursive tensor powers.  The matrices are
first defined on that transparent recursive basis and are then transported to
the public register `Fin (2 ^ q)` by a basis equivalence.

The one-qubit label `(x,z)` denotes `I`, `X`, `Z`, or `Y` in the order
`(0,0)`, `(1,0)`, `(0,1)`, `(1,1)`.  In particular, every represented Pauli is
Hermitian; multiplication of two represented Paulis can have a phase, but its
commutation sign is the binary symplectic character.
-/

open scoped ComplexOrder MatrixOrder

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

/-- A single phase-free Pauli label, written as its binary `X` and `Z` bits. -/
abbrev SingleLabel := Bool × Bool

/-- The recursive label space of phase-free `q`-qubit Paulis. -/
abbrev PauliLabel (q : ℕ) := QIT.TensorPower SingleLabel q

/-- The recursive computational basis of `q` qubits. -/
abbrev QubitBasis (q : ℕ) := QIT.TensorPower Bool q

/-- The all-zero label, representing the identity. -/
def zeroLabel : (q : ℕ) → PauliLabel q
  | 0 => PUnit.unit
  | q + 1 => ((false, false), zeroLabel q)

/-- The nonidentity phase-free Pauli labels used as encryption keys. -/
abbrev PauliKey (q : ℕ) := {v : PauliLabel q // v ≠ zeroLabel q}

/-- The sign character of one binary bit. -/
def commutationSign : Bool → ℂ
  | false => 1
  | true => -1

@[simp]
theorem commutationSign_false : commutationSign false = 1 := rfl

@[simp]
theorem commutationSign_true : commutationSign true = -1 := rfl

@[simp]
theorem commutationSign_xor (a b : Bool) :
    commutationSign (a.xor b) = commutationSign a * commutationSign b := by
  cases a <;> cases b <;> norm_num [commutationSign]

@[simp]
theorem commutationSign_mul_self (a : Bool) :
    commutationSign a * commutationSign a = 1 := by
  cases a <;> norm_num [commutationSign]

@[simp]
theorem commutationSign_ne_zero (a : Bool) : commutationSign a ≠ 0 := by
  cases a <;> norm_num [commutationSign]

/-- The binary symplectic pairing of two one-qubit labels. -/
def singleSymplectic (v w : SingleLabel) : Bool :=
  (v.1 && w.2).xor (v.2 && w.1)

@[simp]
theorem singleSymplectic_zero_left (v : SingleLabel) :
    singleSymplectic (false, false) v = false := by
  cases v
  simp [singleSymplectic]

@[simp]
theorem singleSymplectic_zero_right (v : SingleLabel) :
    singleSymplectic v (false, false) = false := by
  cases v
  simp [singleSymplectic]

theorem singleSymplectic_comm (v w : SingleLabel) :
    singleSymplectic v w = singleSymplectic w v := by
  rcases v with ⟨vx, vz⟩
  rcases w with ⟨wx, wz⟩
  cases vx <;> cases vz <;> cases wx <;> cases wz <;>
    decide

/-- The binary symplectic pairing, accumulated over the `q` tensor factors. -/
def symplectic : (q : ℕ) → PauliLabel q → PauliLabel q → Bool
  | 0, _, _ => false
  | q + 1, v, w =>
      (singleSymplectic v.1 w.1).xor (symplectic q v.2 w.2)

@[simp]
theorem symplectic_zero_left (q : ℕ) (v : PauliLabel q) :
    symplectic q (zeroLabel q) v = false := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp [symplectic, zeroLabel, ih]

@[simp]
theorem symplectic_zero_right (q : ℕ) (v : PauliLabel q) :
    symplectic q v (zeroLabel q) = false := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp [symplectic, zeroLabel, ih]

theorem symplectic_comm (q : ℕ) (v w : PauliLabel q) :
    symplectic q v w = symplectic q w v := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp only [symplectic]
      rw [singleSymplectic_comm, ih]

/-- The standard Hermitian one-qubit Pauli represented by a binary label. -/
def singlePauli : SingleLabel → CMatrix Bool
  | (false, false) => 1
  | (true, false) => fun i j =>
      match i, j with
      | false, true => 1
      | true, false => 1
      | _, _ => 0
  | (false, true) => fun i j =>
      match i, j with
      | false, false => 1
      | true, true => -1
      | _, _ => 0
  | (true, true) => fun i j =>
      match i, j with
      | false, true => -Complex.I
      | true, false => Complex.I
      | _, _ => 0

@[simp]
theorem singlePauli_zero : singlePauli (false, false) = 1 := rfl

theorem singlePauli_isHermitian (v : SingleLabel) :
    (singlePauli v).IsHermitian := by
  rcases v with ⟨x, z⟩
  cases x <;> cases z <;>
    ext i j <;> cases i <;> cases j <;>
    norm_num [singlePauli, Matrix.IsHermitian, Matrix.conjTranspose_apply]

theorem singlePauli_mul_self (v : SingleLabel) :
    singlePauli v * singlePauli v = 1 := by
  rcases v with ⟨x, z⟩
  cases x <;> cases z <;>
    ext i j <;> cases i <;> cases j <;>
    norm_num [singlePauli, Matrix.mul_apply, Matrix.one_apply]

theorem singlePauli_commutation (v w : SingleLabel) :
    singlePauli v * singlePauli w =
      commutationSign (singleSymplectic v w) •
        (singlePauli w * singlePauli v) := by
  rcases v with ⟨vx, vz⟩
  rcases w with ⟨wx, wz⟩
  cases vx <;> cases vz <;> cases wx <;> cases wz <;>
    ext i j <;> cases i <;> cases j <;>
    norm_num [singlePauli, singleSymplectic, commutationSign,
      Matrix.mul_apply, Matrix.smul_apply]

theorem singlePauli_trace (v : SingleLabel) :
    (singlePauli v).trace = if v = (false, false) then 2 else 0 := by
  rcases v with ⟨x, z⟩
  cases x <;> cases z <;>
    norm_num [singlePauli, Matrix.trace]

/-- One-qubit Hilbert--Schmidt orthogonality. -/
theorem singlePauli_mul_trace (v w : SingleLabel) :
    (singlePauli v * singlePauli w).trace =
      if v = w then 2 else 0 := by
  rcases v with ⟨vx, vz⟩
  rcases w with ⟨wx, wz⟩
  cases vx <;> cases vz <;> cases wx <;> cases wz <;>
    norm_num [singlePauli, Matrix.trace, Matrix.mul_apply]

/-- The recursive tensor-product matrix before transport to a `Fin` register. -/
def rawPauli : (q : ℕ) → PauliLabel q → CMatrix (QubitBasis q)
  | 0, _ => 1
  | q + 1, v => Matrix.kronecker (singlePauli v.1) (rawPauli q v.2)

@[simp]
theorem rawPauli_zero (q : ℕ) : rawPauli q (zeroLabel q) = 1 := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [rawPauli, zeroLabel, singlePauli_zero, ih]
      exact Matrix.one_kronecker_one

theorem rawPauli_isHermitian (q : ℕ) (v : PauliLabel q) :
    (rawPauli q v).IsHermitian := by
  induction q with
  | zero => exact Matrix.isHermitian_one
  | succ q ih =>
      rw [Matrix.IsHermitian, rawPauli]
      calc
        (Matrix.kronecker (singlePauli v.1) (rawPauli q v.2)).conjTranspose =
            Matrix.kronecker (singlePauli v.1).conjTranspose
              (rawPauli q v.2).conjTranspose :=
          Matrix.conjTranspose_kronecker _ _
        _ = Matrix.kronecker (singlePauli v.1) (rawPauli q v.2) := by
          rw [singlePauli_isHermitian, ih]

theorem rawPauli_mul_self (q : ℕ) (v : PauliLabel q) :
    rawPauli q v * rawPauli q v = 1 := by
  induction q with
  | zero => simp [rawPauli]
  | succ q ih =>
      rw [rawPauli]
      change
        Matrix.kroneckerMap (fun x y : ℂ => x * y)
            (singlePauli v.1) (rawPauli q v.2) *
          Matrix.kroneckerMap (fun x y : ℂ => x * y)
            (singlePauli v.1) (rawPauli q v.2) = 1
      rw [← Matrix.mul_kronecker_mul, singlePauli_mul_self, ih,
        Matrix.one_kronecker_one]

theorem rawPauli_commutation (q : ℕ) (v w : PauliLabel q) :
    rawPauli q v * rawPauli q w =
      commutationSign (symplectic q v w) •
        (rawPauli q w * rawPauli q v) := by
  induction q with
  | zero => simp [rawPauli, symplectic, commutationSign]
  | succ q ih =>
      change
        Matrix.kronecker (singlePauli v.1) (rawPauli q v.2) *
            Matrix.kronecker (singlePauli w.1) (rawPauli q w.2) =
          commutationSign (symplectic (q + 1) v w) •
            (Matrix.kronecker (singlePauli w.1) (rawPauli q w.2) *
              Matrix.kronecker (singlePauli v.1) (rawPauli q v.2))
      calc
        Matrix.kronecker (singlePauli v.1) (rawPauli q v.2) *
            Matrix.kronecker (singlePauli w.1) (rawPauli q w.2) =
            Matrix.kronecker (singlePauli v.1 * singlePauli w.1)
              (rawPauli q v.2 * rawPauli q w.2) := by
                exact (Matrix.mul_kronecker_mul
                  (singlePauli v.1) (singlePauli w.1)
                  (rawPauli q v.2) (rawPauli q w.2)).symm
        _ = Matrix.kronecker
              (commutationSign (singleSymplectic v.1 w.1) •
                (singlePauli w.1 * singlePauli v.1))
              (commutationSign (symplectic q v.2 w.2) •
                (rawPauli q w.2 * rawPauli q v.2)) := by
              rw [singlePauli_commutation, ih]
        _ = commutationSign (symplectic (q + 1) v w) •
                Matrix.kronecker (singlePauli w.1 * singlePauli v.1)
                  (rawPauli q w.2 * rawPauli q v.2) := by
              simp [symplectic, Matrix.smul_kronecker,
                Matrix.kronecker_smul, smul_smul, mul_comm]
        _ = commutationSign (symplectic (q + 1) v w) •
              (Matrix.kronecker (singlePauli w.1) (rawPauli q w.2) *
                Matrix.kronecker (singlePauli v.1) (rawPauli q v.2)) := by
              apply congrArg (commutationSign (symplectic (q + 1) v w) • ·)
              exact Matrix.mul_kronecker_mul
                (singlePauli w.1) (singlePauli v.1)
                (rawPauli q w.2) (rawPauli q v.2)

theorem rawPauli_trace (q : ℕ) (v : PauliLabel q) :
    (rawPauli q v).trace = if v = zeroLabel q then (2 : ℂ) ^ q else 0 := by
  induction q with
  | zero =>
      rcases v with ⟨⟩
      change (1 : CMatrix PUnit).trace = 1
      simp [Matrix.trace]
  | succ q ih =>
      rw [rawPauli]
      change
        (Matrix.kroneckerMap (fun x y : ℂ => x * y)
          (singlePauli v.1) (rawPauli q v.2)).trace = _
      rw [Matrix.trace_kronecker, singlePauli_trace, ih]
      by_cases hhead : v.1 = (false, false)
      · by_cases htail : v.2 = zeroLabel q
        · have hv : v = zeroLabel (q + 1) := by
            apply Prod.ext
            · exact hhead
            · exact htail
          simp [hv, zeroLabel, pow_succ, mul_comm]
        · have hv : v ≠ zeroLabel (q + 1) := by
            intro hv
            exact htail (congrArg Prod.snd hv)
          simp [hhead, htail, hv]
      · have hv : v ≠ zeroLabel (q + 1) := by
          intro hv
          exact hhead (congrArg Prod.fst hv)
        simp [hhead, hv]

theorem rawPauli_trace_eq_zero {q : ℕ} {v : PauliLabel q}
    (hv : v ≠ zeroLabel q) : (rawPauli q v).trace = 0 := by
  rw [rawPauli_trace, if_neg hv]

/-- Tensor-product Hilbert--Schmidt orthogonality of phase-free Paulis. -/
theorem rawPauli_mul_trace (q : ℕ) (v w : PauliLabel q) :
    (rawPauli q v * rawPauli q w).trace =
      if v = w then (2 : ℂ) ^ q else 0 := by
  induction q with
  | zero =>
      rcases v with ⟨⟩
      rcases w with ⟨⟩
      simp only [rawPauli, if_pos rfl, pow_zero]
      rw [Matrix.one_mul]
      simp [Matrix.trace, QIT.TensorPower]
  | succ q ih =>
      rw [rawPauli, rawPauli]
      change
        (Matrix.kroneckerMap (fun x y : ℂ => x * y)
            (singlePauli v.1) (rawPauli q v.2) *
          Matrix.kroneckerMap (fun x y : ℂ => x * y)
            (singlePauli w.1) (rawPauli q w.2)).trace = _
      rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
        singlePauli_mul_trace, ih]
      by_cases hhead : v.1 = w.1
      · by_cases htail : v.2 = w.2
        · have hvw : v = w := Prod.ext hhead htail
          simp [hvw, pow_succ]
          ring
        · have hvw : v ≠ w := fun h => htail (congrArg Prod.snd h)
          simp [hhead, htail, hvw]
      · have hvw : v ≠ w := fun h => hhead (congrArg Prod.fst h)
        simp [hhead, hvw]

/-- There are exactly `4 ^ q` phase-free Pauli labels. -/
@[simp]
theorem pauliLabel_card (q : ℕ) : Fintype.card (PauliLabel q) = 4 ^ q := by
  induction q with
  | zero => simp [PauliLabel, QIT.TensorPower]
  | succ q ih =>
      change Fintype.card (SingleLabel × PauliLabel q) = 4 ^ (q + 1)
      simp [ih, pow_succ, SingleLabel, Nat.mul_comm]

/-- There are exactly `2 ^ q` computational basis vectors. -/
@[simp]
theorem qubitBasis_card (q : ℕ) : Fintype.card (QubitBasis q) = 2 ^ q := by
  induction q with
  | zero => simp [QubitBasis, QIT.TensorPower]
  | succ q ih =>
      change Fintype.card (Bool × QubitBasis q) = 2 ^ (q + 1)
      simp [ih, pow_succ, Nat.mul_comm]

/-- There are exactly `4 ^ q - 1` nonidentity Pauli labels. -/
@[simp]
theorem pauliKey_card (q : ℕ) : Fintype.card (PauliKey q) = 4 ^ q - 1 := by
  change Fintype.card {v : PauliLabel q // ¬v = zeroLabel q} = 4 ^ q - 1
  rw [Fintype.card_subtype_compl (fun v : PauliLabel q => v = zeroLabel q),
    Fintype.card_subtype_eq, pauliLabel_card]

/-- A nonzero label on any positive number of qubits. -/
def firstXLabel (q : ℕ) : PauliLabel (q + 1) :=
  ((true, false), zeroLabel q)

/-- A second explicit nonzero label, used in the exact Gamma norm proof. -/
def firstZLabel (q : ℕ) : PauliLabel (q + 1) :=
  ((false, true), zeroLabel q)

theorem firstXLabel_ne_zero (q : ℕ) :
    firstXLabel q ≠ zeroLabel (q + 1) := by
  intro h
  have := congrArg (fun v : PauliLabel (q + 1) => v.1.1) h
  simp [firstXLabel, zeroLabel] at this

theorem firstZLabel_ne_zero (q : ℕ) :
    firstZLabel q ≠ zeroLabel (q + 1) := by
  intro h
  have := congrArg (fun v : PauliLabel (q + 1) => v.1.2) h
  simp [firstZLabel, zeroLabel] at this

/-- The nonidentity key type is inhabited whenever there is at least one qubit. -/
def firstPauliKey (q : ℕ) : PauliKey (q + 1) :=
  ⟨firstXLabel q, firstXLabel_ne_zero q⟩

/-- The explicit `Z` key is distinct from the explicit `X` key. -/
def firstZPauliKey (q : ℕ) : PauliKey (q + 1) :=
  ⟨firstZLabel q, firstZLabel_ne_zero q⟩

theorem firstPauliKey_ne_firstZPauliKey (q : ℕ) :
    firstPauliKey q ≠ firstZPauliKey q := by
  intro h
  have := congrArg (fun v : PauliKey (q + 1) => v.1.1) h
  simp [firstPauliKey, firstZPauliKey, firstXLabel, firstZLabel] at this

/-- A fixed equivalence from the recursive basis to the canonical finite register. -/
def qubitBasisEquivFin (q : ℕ) : QubitBasis q ≃ Fin (2 ^ q) :=
  Fintype.equivFinOfCardEq (qubitBasis_card q)

/-- The public phase-free Hermitian Pauli matrix on `Fin (2 ^ q)`. -/
def pauli {q : ℕ} (v : PauliLabel q) : CMatrix (Fin (2 ^ q)) :=
  Matrix.reindex (qubitBasisEquivFin q) (qubitBasisEquivFin q) (rawPauli q v)

@[simp]
theorem pauli_zero (q : ℕ) : pauli (zeroLabel q) = 1 := by
  change Matrix.reindex (qubitBasisEquivFin q) (qubitBasisEquivFin q)
    (rawPauli q (zeroLabel q)) = 1
  rw [rawPauli_zero]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (qubitBasisEquivFin q)).map_one

theorem pauli_isHermitian {q : ℕ} (v : PauliLabel q) :
    (pauli v).IsHermitian := by
  exact (rawPauli_isHermitian q v).reindex (qubitBasisEquivFin q)

theorem pauli_mul_self {q : ℕ} (v : PauliLabel q) :
    pauli v * pauli v = 1 := by
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ (qubitBasisEquivFin q))
    (rawPauli_mul_self q v)
  simpa [pauli, Matrix.reindexAlgEquiv_apply] using h

/-- Every represented Pauli is a Hermitian reflection. -/
def IsHermitianReflection {d : ℕ} (A : CMatrix (Fin d)) : Prop :=
  A.IsHermitian ∧ A * A = 1

theorem pauli_isHermitianReflection {q : ℕ} (v : PauliLabel q) :
    IsHermitianReflection (pauli v) :=
  ⟨pauli_isHermitian v, pauli_mul_self v⟩

/-- Every represented Pauli is unitary. -/
theorem pauli_mem_unitaryGroup {q : ℕ} (v : PauliLabel q) :
    pauli v ∈ Matrix.unitaryGroup (Fin (2 ^ q)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    pauli_isHermitian v, pauli_mul_self]

private theorem trace_reindex_equiv
    {a b : Type*} [Fintype a] [Fintype b]
    (e : a ≃ b) (A : CMatrix a) :
    (Matrix.reindex e e A).trace = A.trace := by
  classical
  rw [Matrix.trace, Matrix.trace]
  apply Fintype.sum_equiv e.symm
  intro x
  rfl

theorem pauli_trace {q : ℕ} (v : PauliLabel q) :
    (pauli v).trace = if v = zeroLabel q then (2 : ℂ) ^ q else 0 := by
  rw [pauli, trace_reindex_equiv, rawPauli_trace]

theorem pauli_trace_eq_zero {q : ℕ} {v : PauliLabel q}
    (hv : v ≠ zeroLabel q) : (pauli v).trace = 0 := by
  rw [pauli_trace, if_neg hv]

theorem pauliKey_trace_eq_zero {q : ℕ} (v : PauliKey q) :
    (pauli v.1).trace = 0 :=
  pauli_trace_eq_zero v.2

/-- Exact Pauli Hilbert--Schmidt orthogonality:
`Tr(P_v P_w) = 2^q` for equal labels and zero otherwise. -/
theorem pauli_mul_trace {q : ℕ} (v w : PauliLabel q) :
    (pauli v * pauli w).trace =
      if v = w then (2 : ℂ) ^ q else 0 := by
  change
    ((Matrix.reindexAlgEquiv ℂ ℂ (qubitBasisEquivFin q)) (rawPauli q v) *
      (Matrix.reindexAlgEquiv ℂ ℂ (qubitBasisEquivFin q))
        (rawPauli q w)).trace = _
  rw [← map_mul]
  change
    (Matrix.reindex (qubitBasisEquivFin q) (qubitBasisEquivFin q)
      (rawPauli q v * rawPauli q w)).trace = _
  rw [trace_reindex_equiv, rawPauli_mul_trace]

/-- The Pauli commutation law with its binary symplectic sign. -/
theorem pauli_commutation {q : ℕ} (v w : PauliLabel q) :
    pauli v * pauli w =
      commutationSign (symplectic q v w) • (pauli w * pauli v) := by
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ (qubitBasisEquivFin q))
    (rawPauli_commutation q v w)
  simpa [pauli, Matrix.reindexAlgEquiv_apply] using h

/-- Transposition preserves the symplectic commutation-sign relation.

This deliberately does not assert that an individual Pauli is fixed by
transpose: every `Y` tensor factor contributes a minus sign.
-/
theorem pauli_transpose_commutation {q : ℕ} (v w : PauliLabel q) :
    Matrix.transpose (pauli v) * Matrix.transpose (pauli w) =
      commutationSign (symplectic q v w) •
        (Matrix.transpose (pauli w) * Matrix.transpose (pauli v)) := by
  have h := congrArg (fun A => Matrix.transpose A) (pauli_commutation w v)
  simpa [Matrix.transpose_mul, Matrix.transpose_smul, symplectic_comm] using h

end

end UE.PauliConstructionAndProof
