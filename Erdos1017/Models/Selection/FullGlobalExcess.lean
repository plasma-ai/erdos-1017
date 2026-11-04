module

public import Erdos1017.Models.Capped.CappedLimitValue
public import Erdos1017.Models.Selection.FullModelEdits
public import Erdos1017.Models.Selection.GlobalExcessMaximum

/-!
# Fully feasible model at a positive global excess

A failure of the sharp upper bound yields a fully feasible averaged model at a
positive global maximum of the benchmark excess
(`exists_full_positive_global_excess`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]

/-- An actual failure of the sharp upper bound yields an actual fully feasible
averaged model at a positive global maximum of the benchmark excess. Its
comparison includes competitors with any probability law on the carrier. -/
theorem exists_full_positive_global_excess
    (hfailure : ∃ d ∈ Set.Icc (0 : ℝ) (1 / 2),
      benchmark d < FractionalGraph.densityLimit d) :
    ∃ W : Model Ω μ, FullFeasible W ∧ density W ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧
      objective W = FractionalGraph.densityLimit (density W) ∧
      0 < objective W - benchmark (density W) ∧
      (∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
        FullFeasible V → objective V - benchmark (density V) ≤
          objective W - benchmark (density W)) ∧
      (∀ p, ∀ᵐ c ∂W.kernel p,
        CappedColor.charge c = conditionalCharge W p * CappedColor.adjacency c) := by
  obtain ⟨d, hd, hpositive, hmax⟩ := Erdos1017.exists_positive_global_excess hfailure
  obtain ⟨U, hU, hdU, hoU⟩ := exists_fullFeasible_at_density (μ := μ) d
    ⟨by linarith [hd.1], hd.2.le⟩
  let W := averaged U
  have hdW : density W = d := (density_averaged U).trans hdU
  have hoW : objective W = FractionalGraph.densityLimit d := (objective_averaged U).trans hoU
  refine ⟨W, fullFeasible_averaged U hU, hdW.symm ▸ hd, ?_, ?_, ?_, ?_⟩
  · rw [hdW, hoW]
  · simpa only [hdW, hoW] using hpositive
  · intro ν _ V hV
    calc
      objective V - benchmark (density V) ≤
          FractionalGraph.densityLimit (density V) - benchmark (density V) :=
        sub_le_sub_right (fullFeasible_objective_le_densityLimit V hV) _
      _ ≤ FractionalGraph.densityLimit d - benchmark d := hmax _ (density_mem V)
      _ = objective W - benchmark (density W) := by rw [hoW, hdW]
  · intro p
    change ∀ᵐ c ∂(averaged U).kernel p,
      CappedColor.charge c = conditionalCharge (averaged U) p * CappedColor.adjacency c
    rw [conditionalCharge_averaged]
    exact averaged_deterministic U p

end Erdos1017.CappedModel
