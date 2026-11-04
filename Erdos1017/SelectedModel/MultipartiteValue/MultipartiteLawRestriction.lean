module

public import Erdos1017.SelectedModel.Structure.IntegrableReweight
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteModelComparison
public import Erdos1017.Models.Capped.CappedRegularSelection

/-!
# Benchmark bound under a restricted probability law

Under a probability law supported on an original set, every clique order remains
feasible and restricted scalar moments determine the conditional color support,
so restricted partition support gives the benchmark bound for the unchanged
kernel under the new law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A weight vanishing outside a measurable set gives an actual law
absolutely continuous with respect to the original restricted measure.
This fact requires no normalization or integrability premise. -/
theorem weightedMeasure_ac_restrict_of_ae_zero (w : Ω → ℝ)
    (T : Set Ω) (hT : MeasurableSet T)
    (hzero : ∀ᵐ x ∂μ, x ∉ T → w x = 0) :
    weightedMeasure (μ := μ) w ≪ μ.restrict T := by
  classical
  have heq : (fun x => ENNReal.ofReal (w x)) =ᵐ[μ]
      T.indicator (fun x => ENNReal.ofReal (w x)) := by
    filter_upwards [hzero] with x hx
    by_cases hxT : x ∈ T
    · simp only [indicator_of_mem hxT]
    · simp only [indicator_of_notMem hxT, hx hxT, ENNReal.ofReal_zero]
  rw [weightedMeasure, withDensity_congr_ae heq, withDensity_indicator hT]
  exact withDensity_absolutelyContinuous _ _

variable [IsProbabilityMeasure μ] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- Restricted scalar zero/one moments determine actual conditional color
support under every probability law supported on that original set. -/
theorem ae_color_adjacency_of_restricted_moment
    (W : Model Ω μ) (T : Set Ω) (hν : ν ≪ μ.restrict T)
    (P : Ω × Ω → Prop) [DecidablePred P]
    (hmoment : ∀ᵐ p ∂(μ.restrict T).prod (μ.restrict T),
      W.moment CappedColor.adjacency p = if P p then 1 else 0) :
    ∀ᵐ p ∂ν.prod ν, ∀ᵐ z ∂W.kernel p, CappedColor.adjacency z = 1 ↔ P p := by
  filter_upwards [(hν.prod hν).ae_le hmoment] with p hp
  by_cases hP : P p
  · rw [ite_eq_left hP] at hp
    filter_upwards [ae_adjacency_one_of_moment_one W p hp] with z hz
    simp only [hz, hP]
  · rw [ite_eq_right hP] at hp
    filter_upwards [ae_adjacency_zero_of_moment_zero W p hp] with z hz
    simp only [hz, zero_ne_one, hP]

/-- Every original clique order remains feasible under a probability law
supported on an arbitrary measurable or nonmeasurable original set. -/
theorem fullFeasible_changeMeasure_of_restrict_ac
    (W : Model Ω μ) (hW : FullFeasible W) (T : Set Ω) (hν : ν ≪ μ.restrict T) :
    FullFeasible (W.changeMeasure (hν.trans Measure.absolutelyContinuous_restrict)) := by
  intro n
  exact feasible_changeMeasure W (hν.trans Measure.absolutelyContinuous_restrict) (hW n)

/-- Actual restricted moment partition support gives the benchmark bound
for the unchanged kernel under its actual new probability law. -/
theorem objective_changeMeasure_le_benchmark_of_restricted_partition
    (W : Model Ω μ) (hW : FullFeasible W) (T : Set Ω) (hν : ν ≪ μ.restrict T)
    {ι : Type*} (π : Ω → ι)
    (hmoment : ∀ᵐ p ∂(μ.restrict T).prod (μ.restrict T),
      W.moment CappedColor.adjacency p = if π p.1 ≠ π p.2 then 1 else 0) :
    objective (W.changeMeasure (hν.trans Measure.absolutelyContinuous_restrict)) ≤
      benchmark (density (W.changeMeasure (hν.trans Measure.absolutelyContinuous_restrict))) := by
  classical
  exact objective_le_benchmark_of_partition_support _
    (fullFeasible_changeMeasure_of_restrict_ac W hW T hν) π
    (ae_color_adjacency_of_restricted_moment W T hν (fun p => π p.1 ≠ π p.2) hmoment)

end Erdos1017.CappedModel
