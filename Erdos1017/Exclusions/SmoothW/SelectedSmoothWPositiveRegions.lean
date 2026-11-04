module

public import Erdos1017.Exclusions.SmoothW.SelectedCoveredSmoothWContact
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredNoExterior
public import Erdos1017.Exclusions.SmoothW.SelectedCoveredSmoothWGate

/-!
# Zero-body case with both diffuse regions positive at smooth `W`

The selected smooth-`W` zero-body saturated case is impossible when both diffuse
regions have positive mass; exterior atoms, the entry model and all later active
cases are excluded (`no_smoothW_zero_body_of_positive_regions`).
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

/-- The selected smooth-W zero-body saturated case is impossible when
both actual diffuse regions have positive mass. Exterior atoms, the entry
model and all later active duals' own data are eliminated or constructed
inside the proof. No no-exterior or own-data callback remains. -/
theorem no_smoothW_zero_body_of_positive_regions
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
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) : False := by
  obtain ⟨hell, _, _, hbonus, _⟩ := S.smoothW_covered_contact_guards r a hpair.1
    hW hd hgap he hactive hglobal
  have hatoms := S.covered_atoms_eq_root_or_saturated r a hW hd hgap hpair hzero hR hE
    hell.1 hbonus
  exact S.no_smoothW_zero_body_of_two_atoms r a hW hd hgap he hactive hglobal
    hpair hzero hR hE hatoms

end Erdos1017.CappedModel.SelectedHighLowStructure
