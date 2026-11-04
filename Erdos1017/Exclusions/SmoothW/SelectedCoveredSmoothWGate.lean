module

public import Erdos1017.Exclusions.SmoothW.TwoAtomSmoothWGate
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredFourRegionEntry
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredWeakMassOrder

/-!
# Zero-body two-atom gate at the smooth `W` contact

The original selected smooth-`W` zero-body model is excluded when only its
saturated pair remains and both diffuse regions are positive
(`no_smoothW_zero_body_of_two_atoms`).
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

/-- The original selected smooth-W zero-body model is excluded when
only its saturated pair remains and both diffuse regions are positive.
The actual entry, weak mass order and every active dual's own data are
constructed internally. Exterior elimination and absent regions are not
covered here. -/
theorem no_smoothW_zero_body_of_two_atoms
    (S : SelectedHighLowStructure W m) (r a : S.I)
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
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) : False := by
  obtain ⟨V, hV, hmom, hphysical, hh, hx, _⟩ :=
    S.exists_covered_four_region_entry r a hW hd hgap hpair hzero hR hE hatoms
  have hglobalV : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
      FullFeasible T → objective T - benchmark (density T) ≤
        objective V - benchmark (density V) := by
    intro ν _ T hT
    simpa only [hW.objective_eq, hW.density_eq, hV.objective_eq, hV.density_eq] using
      hglobal ν T hT
  apply TwoAtomCountGate.no_smoothW_four_region hV hd hgap he hactive hglobalV hphysical
    (S.coveredFourLabel a) (S.measurable_coveredFourLabel a)
    (S.coveredFourLabel_fibers_positive r a hpair.1 hatoms hR hE)
    (S.coveredEntry r a) hx hh hmom
  obtain ⟨_, hB, hRl, _⟩ := S.coveredFourLabel_fibers r a hpair.1 hatoms
  rw [hB, hRl]
  exact S.covered_R_mass_le_root r a hW hd hgap hpair hzero

end Erdos1017.CappedModel.SelectedHighLowStructure
