module

public import Erdos1017.Exclusions.SmoothW.CoveredTwoNeighborSmoothWGate
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTwoNeighborCounts

/-!
# Two-neighbor zero-body case at a smooth point of `W`

The `E`-null saturated zero-body case at smooth-`W` contact is excluded when
exactly two exterior atoms remain and `R` has positive mass
(`no_smoothW_zero_body_two_neighbor`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- The original E-null smooth-W saturated zero-body case is excluded
when exactly two exterior atoms remain and R has positive mass. The
actual entry and every active child dual's own data are constructed. -/
theorem no_smoothW_zero_body_two_neighbor
    (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a)) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a)
    (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) : False := by
  obtain ⟨hy, V, hV, hmom, hphysical, _⟩ :=
    S.exists_covered_two_neighbor_entry r a z1 z2 hW hd hgap hpair hzero hE hR
      hz1r hz1a hz2r hz2a hz12 hatoms
  have hglobalV : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
      FullFeasible T → objective T - benchmark (density T) ≤
        objective V - benchmark (density V) := by
    intro ν _ T hT
    simpa only [hW.objective_eq, hW.density_eq, hV.objective_eq, hV.density_eq] using
      hglobal ν T hT
  have hD : 0 < μ S.D := hR.trans_le (measure_mono inter_subset_left)
  exact CoveredTwoExteriorNeighbor.no_smoothW_five_region hV hd hgap he hactive hglobalV hphysical
    (S.coveredTwoBoundaryLabel r a z1) (S.measurable_coveredTwoBoundaryLabel r a z1)
    (S.coveredTwoBoundaryLabel_fibers_positive r a z1 z2 hpair.1
      hz1r hz1a hz2r hz2a hz12 hatoms hD)
    (S.coveredTwoBoundaryEntry r a z1) hy hmom

end Erdos1017.CappedModel.SelectedHighLowStructure
