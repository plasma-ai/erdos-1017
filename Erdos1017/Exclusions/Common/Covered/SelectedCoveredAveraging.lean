module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredPartition
public import Erdos1017.Exclusions.Common.CappedConditionalAveragingStationarity

/-!
# Block averaging of the covered zero-body optimum

The covered zero-body optimum admits full countable block averaging on its
original probability space, keeping every original atom and the two positive
diffuse regions (`exists_covered_conditional_average`).
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

/-- The actual covered zero-body optimum admits full countable block
averaging on its original probability space. Every original atom remains;
the two positive diffuse regions are the only new labels. The original
multiplier's row equation is proved by conditional averaging. -/
theorem exists_covered_conditional_average
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
      ∀ x, (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d) := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  have hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if S.coveredGraph r a (S.coveredLabel a p.1) (S.coveredLabel a p.2) = true then 1 else 0 :=
    S.ae_covered_graph r a hW hd hgap hpair hzero
  obtain ⟨V, hfull, hdV, hcV, hmom, hrow⟩ := exists_full_conditional_average_stationary
    W hW.full m (2 * (c - m * d)) hW.stationary (S.coveredLabel a)
    (S.measurable_coveredLabel a) (S.coveredLabel_fibers_positive a hR hE)
    (S.coveredGraph r a) (S.coveredGraph_symm r a) hsupport
  have hdV' := hdV.trans hW.density_eq
  have hcV' := hcV.trans hW.objective_eq
  refine ⟨V, hfull, hdV', hcV', ?_, hmom, hrow⟩
  rw [hcV', hdV']
  exact hW.optimal

end Erdos1017.CappedModel.SelectedHighLowStructure
