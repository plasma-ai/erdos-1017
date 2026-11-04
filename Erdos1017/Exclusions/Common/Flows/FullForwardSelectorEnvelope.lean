module

public import Erdos1017.Exclusions.Common.MultipartiteCollisionEnvelope
public import Erdos1017.SelectedModel.OriginalAtomicSquareReserve

/-!
# Forward selector envelope

The envelope `selectorEnvelope` equals the collision-curve expression for a
positive mass; weighting the two selector bounds on one endpoint by `1 - ell`
and `ell` cancels the tail-square quantity, and the original peak satisfies the
envelope together with its total reserve and strict square majority.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.ForwardPeak

/-- The forward selector envelope in the existing split-curve normalization. -/
def selectorEnvelope (ell A : ℝ) : ℝ :=
  (2 - 3 * ell) * A ^ 2 + 2 * ell * Benchmark.splitValue A

/-- This is exactly the collision-curve expression for a positive mass. -/
theorem selectorEnvelope_eq_collision {A : ℝ} (hA : 0 < A) (ell : ℝ) :
    selectorEnvelope ell A =
      A ^ 2 * (2 - 3 * ell + 2 * ell * Selector.Collision.collisionCurve ((1 - A) / A)) := by
  rw [selectorEnvelope, ← Multipartite.collision_curve_normalization hA]
  ring

end Erdos1017.ForwardPeak

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- Both selector bounds concern this same actual endpoint and its same
tail-square quantity. Weighting them by 1-ell and ell cancels that quantity
exactly; actual nonnegative flow energy gives the original gamma bound. -/
theorem selector_envelope (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (i : S.I) (hpos : 0 < S.forwardClassMass q i)
    (hmax : ∀ j, S.forwardClassMass q j ≤ S.forwardClassMass q i) :
    2 * (c - m * d) + m ≤ ForwardPeak.selectorEnvelope (-m) (S.forwardClassMass q i) := by
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
  have hcollision := MultipartiteClassMasses.objective_le_split_add_tail hq.endpoint
    (hq.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by filter_upwards [hs] with p hp; split_ifs at hp ⊢ <;> exact hp) i hpos hmax
  change objective hq.endpoint ≤ Benchmark.splitValue (S.forwardClassMass q i) +
    (1 - 2 * density hq.endpoint - (S.forwardClassMass q i) ^ 2) / 2 at hcollision
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hfirst := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 1 + m by linarith)
  have hsecond := mul_le_mul_of_nonneg_left hcollision (neg_nonneg.mpr hm.le)
  have hbudget := hq.endpoint_budget hW
  have henergy := hq.energy_nonnegative hW hd hgap
  unfold ForwardPeak.selectorEnvelope
  nlinarith

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The same actual original peak satisfies the selector envelope together
with its already proved total reserve and strict square majority. An actual
avoiding endpoint is constructed; its class mass is proved to equal the
original peak mass before applying the two endpoint selector bounds. -/
theorem exists_original_forward_selector_envelope (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      0 < S.originalAtomMass i ∧
      ((∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.H) ∨
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.N)) ∧
      (∀ (r : Ω × Ω → ℝ), S.IsFullForwardFlow r →
        0 < S.forwardClassMass r i ∧
        ForwardPeak.massPeak (S.forwardClassMass r) = S.forwardClassMass r i ∧
        ForwardPeak.IsSeparatedPeak (S.forwardClassMass r) (forwardPeakGap d c m) i) ∧
      (∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i) ∧
      (2 * (c - m * d) + m + (-m) * (∑' k, (S.originalAtomMass k) ^ 2) ≤
        2 * (S.originalAtomMass i) ^ 2) ∧
      ((∑' k : {k : S.I // k ≠ i}, (S.originalAtomMass k.val) ^ 2) <
        (S.originalAtomMass i) ^ 2) ∧
      2 * (c - m * d) + m ≤ ForwardPeak.selectorEnvelope (-m) (S.originalAtomMass i) := by
  obtain ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, hmajority⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L := by
    rcases hside with hH | hN
    · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
    · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  have hret := hq.classMass_eq_original_of_avoids_nonlow i hnonlow havoid
  change S.forwardClassMass q i = S.originalAtomMass i at hret
  have hmax (k : S.I) : S.forwardClassMass q k ≤ S.forwardClassMass q i := by
    by_cases hki : k = i
    · rw [hki]
    · have hsep := (hpeak q hq).2.2 k hki
      linarith
  have h := hq.selector_envelope hW hd hgap hell i (hpeak q hq).1 hmax
  rw [hret] at h
  exact ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, hmajority, h⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
