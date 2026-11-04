module

public import Erdos1017.Exclusions.E2.Upper.SelectedE2RNull
public import Erdos1017.Exclusions.E2.Upper.SelectedE2SaturatedPositiveRegions
public import Erdos1017.Exclusions.E2.Upper.SelectedE2UnsaturatedZeroBody

/-!
# No zero positive-body energy at the `E₂` contact

Every diffuse-region alternative of the saturated `E₂` zero-body case is
excluded without a region or exterior-atom certificate
(`no_e2_saturated_zero_body`), and an original `E₂` atom cannot have zero
positive-body energy, both saturation alternatives being derived
(`no_e2_zero_body`).
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

/-- Every diffuse-region alternative of the actual saturated E2
zero-body case is excluded. No region or exterior-atom certificate is supplied. -/
theorem no_e2_saturated_zero_body
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
      {x | S.ρ x = r.val} = 0) : False := by
  by_cases hR : μ (S.D ∩ S.rootNeighborhood a) = 0
  · exact S.no_e2_zero_body_R_null r a hW hq hdq hvalue hderiv hgap hglobal hpair hzero hR
  · by_cases hE : μ (S.D \ S.rootNeighborhood a) = 0
    · exact S.no_e2_zero_body_E_null r a hW hq hdq hvalue hderiv hgap hglobal hpair hzero hE
    · exact S.no_e2_zero_body_of_positive_regions r a hW hq hdq hvalue hderiv hgap hglobal
        hpair hzero (pos_iff_ne_zero.mpr hR) (pos_iff_ne_zero.mpr hE)

/-- An original E2 atom cannot have zero positive-body energy. Both
saturation alternatives and all diffuse/exterior boundaries are derived. -/
theorem no_e2_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) : False := by
  by_cases hsat : ∃ a : S.I, S.IsSaturatedAtomPair r a
  · obtain ⟨a, hpair⟩ := hsat
    exact S.no_e2_saturated_zero_body r a hW hq hdq hvalue hderiv hgap hglobal hpair hzero
  · exact S.not_e2_zero_body_of_no_saturated_partner r hW hq hdq hvalue hderiv hgap hglobal
      hzero (fun a _ hpair => hsat ⟨a, hpair⟩)

end Erdos1017.CappedModel.SelectedHighLowStructure
