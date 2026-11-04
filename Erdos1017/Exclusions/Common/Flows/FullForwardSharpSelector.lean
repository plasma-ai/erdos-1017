module

public import Erdos1017.Exclusions.Common.SharpCounts.MultipartiteSharpCountCells
public import Erdos1017.Exclusions.Common.SharpCounts.MultipartiteSharpLargePart
public import Erdos1017.SelectedModel.Flows.FullForwardPeak

/-!
# Sharp selector bounds at a forward endpoint

All sharp selector estimates are instantiated on one full forward endpoint with
a specified largest class, whose density and tail square are computed under that
endpoint.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- All sharp selector estimates are instantiated on the same actual
full forward endpoint and specified largest class. Its density and tail
square are computed under its own actual unchanged-dual endpoint law. -/
theorem endpoint_sharp_selector_bounds (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (i : S.I) (hpos : 0 < S.forwardClassMass q i)
    (hmax : ∀ j, S.forwardClassMass q j ≤ S.forwardClassMass q i) :
    let A := S.forwardClassMass q i
    let h := 1 - 2 * density hq.endpoint
    let T := (1 - A) / A
    let σ := h - A ^ 2
    objective hq.endpoint ≤ A ^ 2 ∧ 0 ≤ σ ∧
      (A ≤ 1 / 3 → objective hq.endpoint ≤ min (1 / 9) (h / 3 + 1 / 27)) ∧
      (1 / 3 ≤ A → objective hq.endpoint ≤ (h + A ^ 2) / 3) ∧
      (T ∈ Icc (2 : ℝ) 3 → objective hq.endpoint ≤ A ^ 2 * (6 * T - T ^ 2) / 12 + σ / 3) ∧
      (3 ≤ T → objective hq.endpoint ≤ A ^ 2 * T / 4 + σ / T) := by
  let := hq.endpoint_probability
  let : NullSingletonClass (missingFlowEndpointLaw μ q) := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hs : ∀ᵐ p ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q),
      hq.endpoint.moment CappedColor.adjacency p =
        if S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none
        then 1 else 0 := hq.endpoint_collapsed_support hW hd hgap
  have hcost := MultipartiteClassMasses.objective_le_class_bound_sq hq.endpoint
    (hq.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by filter_upwards [hs] with p hp; split_ifs at hp ⊢ <;> exact hp)
    (S.forwardClassMass q i) hmax
  have hcells := MultipartiteClassMasses.objective_sharp_countCells hq.endpoint
    (hq.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by filter_upwards [hs] with p hp; split_ifs at hp ⊢ <;> exact hp) i hpos hmax
  refine ⟨hcost, hcells.1, ?_, ?_, hcells.2.1, hcells.2.2⟩
  · intro ha
    exact MultipartiteClassMasses.objective_le_sharp_smallPart hq.endpoint
      (hq.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
      (by filter_upwards [hs] with p hp; split_ifs at hp ⊢ <;> exact hp) i hpos ha hmax
  · intro ha
    exact (MultipartiteClassMasses.objective_le_sharp_largePart hq.endpoint
      (hq.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
      (by filter_upwards [hs] with p hp; split_ifs at hp ⊢ <;> exact hp) i ha hmax).trans
      (min_le_right _ _)

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow
