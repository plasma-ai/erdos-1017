module

public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredNoExterior
public import Erdos1017.Exclusions.E2.Upper.SelectedCoveredE2Gate

/-!
# Zero-body `E₂` case with both diffuse regions positive

The saturated zero-body `E₂` case is impossible with both diffuse regions
positive; own contact guards eliminate exterior atoms first
(`no_e2_zero_body_of_positive_regions`).
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

/-- The original saturated zero-body E2 case is impossible with both
diffuse regions positive. Actual own contact guards eliminate exterior
atoms before the original physical all-count moment contradiction applies. -/
theorem no_e2_zero_body_of_positive_regions
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
    hdq ▸ LowerE2Scalar.contact_density_mem hq
  obtain ⟨_, hell, _, _, hbonus, _⟩ :=
    S.e2_atom_contact_guards r hW hq hdq hvalue hderiv hgap hglobal
  have hatoms := S.covered_atoms_eq_root_or_saturated r a hW hd hgap hpair hzero hR hE
    hell.1 hbonus
  exact S.no_e2_zero_body_of_two_atoms r a hW hq hdq hvalue hderiv hgap hglobal
    hpair hzero hR hE hatoms

end Erdos1017.CappedModel.SelectedHighLowStructure
