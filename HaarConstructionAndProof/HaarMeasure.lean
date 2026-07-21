import HaarConstructionAndProof.Clifford
import QIT.Symmetry.UnitaryTwirl
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Normalized Haar probability on closed unitary subgroups

A closed subgroup of a finite-dimensional unitary group is compact.  We use
mathlib's Haar measure normalized on the whole compact group.  Left invariance
is supplied by the Haar construction.  Right invariance is proved separately
from uniqueness of the normalized Haar probability; this is the invariance
direction used in the Pauli-to-Haar security reduction.
-/

open MeasureTheory

namespace UE.PauliConstructionAndProof

open QIT

noncomputable section

instance closedSubgroupIsTopologicalGroup {q : ℕ}
    (H : ClosedSubgroup (Matrix.unitaryGroup (Fin (2 ^ q)) ℂ)) :
    IsTopologicalGroup H := by
  exact inferInstanceAs (IsTopologicalGroup H.toSubgroup)

/-- Haar measure on a closed subgroup, normalized on the whole compact group. -/
def closedSubgroupHaarMeasure {q : ℕ}
    (H : ClosedSubgroup (Matrix.unitaryGroup (Fin (2 ^ q)) ℂ)) : Measure H :=
  MeasureTheory.Measure.haarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts H)

theorem closedSubgroupHaarMeasure_univ {q : ℕ}
    (H : ClosedSubgroup (Matrix.unitaryGroup (Fin (2 ^ q)) ℂ)) :
    closedSubgroupHaarMeasure H Set.univ = 1 := by
  simpa [closedSubgroupHaarMeasure] using
    (MeasureTheory.Measure.haarMeasure_self
      (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H)))

instance closedSubgroupHaarMeasure_isProbabilityMeasure {q : ℕ}
    (H : ClosedSubgroup (Matrix.unitaryGroup (Fin (2 ^ q)) ℂ)) :
    IsProbabilityMeasure (closedSubgroupHaarMeasure H) :=
  ⟨closedSubgroupHaarMeasure_univ H⟩

instance closedSubgroupHaarMeasure_isMulLeftInvariant {q : ℕ}
    (H : ClosedSubgroup (Matrix.unitaryGroup (Fin (2 ^ q)) ℂ)) :
    MeasureTheory.Measure.IsMulLeftInvariant (closedSubgroupHaarMeasure H) := by
  dsimp [closedSubgroupHaarMeasure]
  infer_instance

/-- Normalized Haar measure on a compact closed unitary subgroup is right
invariant.  The proof maps Haar measure by right multiplication, checks that
the mapped probability still has mass one on `univ`, and invokes Haar
uniqueness. -/
instance closedSubgroupHaarMeasure_isMulRightInvariant {q : ℕ}
    (H : ClosedSubgroup (Matrix.unitaryGroup (Fin (2 ^ q)) ℂ)) :
    MeasureTheory.Measure.IsMulRightInvariant (closedSubgroupHaarMeasure H) := by
  haveI : SecondCountableTopology (Matrix.unitaryGroup (Fin (2 ^ q)) ℂ) := by
    haveI : SecondCountableTopology (Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ) := by
      change SecondCountableTopology (Fin (2 ^ q) → Fin (2 ^ q) → ℂ)
      infer_instance
    change SecondCountableTopology
      ({x // x ∈ (Matrix.unitaryGroup (Fin (2 ^ q)) ℂ :
        Set (Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ))})
    infer_instance
  haveI : SecondCountableTopology H :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  refine ⟨?_⟩
  intro g
  let K₀ : TopologicalSpace.PositiveCompacts H := ⊤
  have hmass :
      (MeasureTheory.Measure.map (fun U : H => U * g)
        (closedSubgroupHaarMeasure H)) K₀ = 1 := by
    rw [MeasureTheory.Measure.map_apply]
    · change closedSubgroupHaarMeasure H Set.univ = 1
      exact closedSubgroupHaarMeasure_univ H
    · exact continuous_mul_const g |>.measurable
    · exact K₀.isCompact.measurableSet
  have hhaar := (MeasureTheory.Measure.haarMeasure_eq_iff K₀
    (MeasureTheory.Measure.map (fun U : H => U * g)
      (closedSubgroupHaarMeasure H))).2 hmass
  simpa [closedSubgroupHaarMeasure, K₀] using hhaar.symm

/-- Bochner integrals against the normalized subgroup Haar measure are
unchanged by right translation. -/
theorem closedSubgroupHaar_integral_mul_right {q : ℕ}
    (H : ClosedSubgroup (Matrix.unitaryGroup (Fin (2 ^ q)) ℂ))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : H → E) (g : H) :
    (∫ U, f (U * g) ∂closedSubgroupHaarMeasure H) =
      ∫ U, f U ∂closedSubgroupHaarMeasure H := by
  exact MeasureTheory.integral_mul_right_eq_self f g

end

end UE.PauliConstructionAndProof
