module

public import Erdos1017.Exclusions.SmoothW.CoveredOneExteriorSmoothWGate
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredOneExteriorCounts

/-!
# One-exterior zero-body case at the smooth `W` contact

The `R`-null smooth-`W` saturated zero-body case is excluded when exactly one
exterior atom remains and `E` has positive mass
(`no_smoothW_zero_body_one_exterior`).
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

/-- The original R-null smooth-W saturated zero-body case is excluded
when exactly one exterior atom remains and E has positive mass. The
actual entry and every optimal child dual's own data are constructed. -/
theorem no_smoothW_zero_body_one_exterior
    (S : SelectedHighLowStructure W m) (r a z : S.I)
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
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) : False := by
  obtain ⟨hy, V, hV, hmom, hphysical, _⟩ :=
    S.exists_covered_one_exterior_entry r a z hW hd hgap hpair hzero hR hE hzr hza hatoms
  have hglobalV : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
      FullFeasible T → objective T - benchmark (density T) ≤
        objective V - benchmark (density V) := by
    intro ν _ T hT
    simpa only [hW.objective_eq, hW.density_eq, hV.objective_eq, hV.density_eq] using
      hglobal ν T hT
  have hD : 0 < μ S.D := hE.trans_le (measure_mono sdiff_subset)
  exact CoveredOneExterior.no_smoothW_one_exterior hV hd hgap he hactive hglobalV hphysical
    (S.coveredBoundaryLabel r a) (S.measurable_coveredBoundaryLabel r a)
    (S.coveredBoundaryLabel_fibers_positive r a z hpair.1 hzr hza hatoms hD)
    (S.coveredBoundaryEntry r a) hy hmom

end Erdos1017.CappedModel.SelectedHighLowStructure
