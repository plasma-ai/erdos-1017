module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredDeterministicAveraging
public import Erdos1017.Exclusions.Common.StationaryMultiplierUniqueness

/-!
# Stationary record of the covered conditional model

The covered conditional model has its own full stationary record at the original
multiplier, with the equality proved from its own nonconstant degree
(`exists_covered_stationary_average`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- The actual covered conditional model has its own full stationary
record at the original multiplier. Equality is proved using its own
nonconstant degree and the two actual row equations. All original labels
and literal conditional charge moments are retained. -/
theorem exists_covered_stationary_average
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) :
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if S.coveredGraph r a (S.coveredLabel a p.1) (S.coveredLabel a p.2) = true then 1 else 0) ∧
        V.moment CappedColor.charge p =
          ConditionalAveraging.charge (μ := μ) (S.coveredLabel a) (chargeKernel W) p.1 p.2) ∧
      (∀ x, (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d)) ∧
      ∀ p, ∀ᵐ z ∂V.kernel p,
        CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z := by
  obtain ⟨V, hfull, hdV, hcV, hopt, hmom, hrow, hphysical⟩ :=
    S.exists_covered_deterministic_average r a hW hd hgap hpair hzero hR hE
  have hdV' : density V ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdV ▸ hd
  have hgapV : benchmark (density V) < objective V := by
    rw [hdV, hcV]
    exact hgap
  obtain ⟨hclass, _⟩ := fullStationaryClass_of_recorded_rows V hfull hopt hphysical hdV' hgapV
    m (2 * (c - m * d)) (Eventually.of_forall hrow)
  rw [hdV, hcV] at hclass
  exact ⟨V, hclass, hmom, hrow, hphysical⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
