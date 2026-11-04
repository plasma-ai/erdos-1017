module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredAveraging

/-!
# Deterministic averaging of the entry dual

Conditional-color averaging makes the entry dual deterministic without changing
the graph or any charge moment, and the original row equation is retained
(`exists_covered_deterministic_average`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- Actual conditional-color averaging makes the entry dual deterministic
without changing any literal graph or charge moment. The original row
equation is retained; an independently selected own multiplier is not assigned. -/
theorem exists_covered_deterministic_average
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) :
    ∃ V : Model Ω μ, FullFeasible V ∧ density V = d ∧ objective V = c ∧
      objective V = FractionalGraph.densityLimit (density V) ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if S.coveredGraph r a (S.coveredLabel a p.1) (S.coveredLabel a p.2) = true then 1 else 0) ∧
        V.moment CappedColor.charge p =
          ConditionalAveraging.charge (μ := μ) (S.coveredLabel a) (chargeKernel W) p.1 p.2) ∧
      (∀ x, (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d)) ∧
      ∀ p, ∀ᵐ z ∂V.kernel p,
        CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z := by
  obtain ⟨V, hfull, hdV, hcV, hopt, hmom, hrow⟩ :=
    S.exists_covered_conditional_average r a hW hd hgap hpair hzero hR hE
  refine ⟨averaged V, fun n => feasible_averaged V (hfull n),
    (density_averaged V).trans hdV, (objective_averaged V).trans hcV, ?_, ?_, ?_, ?_⟩
  · rwa [objective_averaged, density_averaged]
  · intro p
    exact ⟨(adjacency_moment_averaged V p).trans (hmom p).1,
      (charge_moment_averaged V p).trans (hmom p).2⟩
  · intro x
    convert hrow x using 1
    apply integral_congr_ae
    filter_upwards with y
    simp only [shiftedKernel, shiftedMoment_eq, charge_moment_averaged, adjacency_moment_averaged]
  · intro p
    rw [conditionalCharge_averaged]
    exact averaged_deterministic V p

end Erdos1017.CappedModel.SelectedHighLowStructure
