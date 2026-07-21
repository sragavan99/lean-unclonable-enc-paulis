import UE.Definitions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Pauli construction: uniform finite key distributions

This module packages a finite uniform PMF as the key distribution used by the
construction and records the exact conversion of its integral to a normalized
finite sum.
-/

open MeasureTheory

namespace UE.PauliConstructionAndProof

noncomputable section

/-- The uniform probability distribution on a nonempty finite type, equipped
with its discrete measurable space. -/
def uniformKeyDistribution (α : Type*) [Fintype α] [Nonempty α] :
    KeyDistribution where
  Key := α
  measurableSpace := ⊤
  μ := @PMF.toMeasure α ⊤ (PMF.uniformOfFintype α)
  isProbability :=
    @PMF.toMeasure.isProbabilityMeasure α ⊤ (PMF.uniformOfFintype α)

/-- Integration against the uniform finite key distribution is the normalized
finite sum. -/
theorem integral_uniformKeyDistribution_eq_average
    (α : Type*) [Fintype α] [Nonempty α] (f : α → ℝ) :
    letI : MeasurableSpace α := ⊤
    ∫ x, f x ∂(PMF.uniformOfFintype α).toMeasure =
      (Fintype.card α : ℝ)⁻¹ * ∑ x, f x := by
  letI : MeasurableSpace α := ⊤
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, Finset.mul_sum]

/-- Every function out of a finite discrete key type is measurable. -/
theorem measurable_uniformKeyDistribution
    (α : Type*) [Fintype α] [Nonempty α]
    {β : Type*} [MeasurableSpace β] (f : α → β) :
    letI : MeasurableSpace α := ⊤
    Measurable f := by
  letI : MeasurableSpace α := ⊤
  exact measurable_of_finite f

end

end UE.PauliConstructionAndProof
