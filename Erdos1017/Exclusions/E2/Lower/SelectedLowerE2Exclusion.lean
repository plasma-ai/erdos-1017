module

public import Erdos1017.Exclusions.E2.Lower.FullLowerE2PeakIncidence
public import Erdos1017.Exclusions.E2.Lower.SelectedLowerE2UniversalExclusion

/-!
# Exclusion of the lower `E₂` range

No positive global excess contact lies in the entire lower `E₂` range (`q ≤
1/10`); the same original common peak, its saturation and its universality are
constructed internally (`no_lowerE2_contact`). This is one of the exclusions
assembled in `FullBenchmarkUpper`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  [StandardBorelSpace Ω] [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m q : ℝ}

/-- No genuine positive global excess contact lies in the entire lower-E2
range. The same original common peak, saturation and universality are
constructed internally; no recovery or scalar-resource certificate is assumed. -/
theorem no_lowerE2_contact (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioc (0 : ℝ) (1 / 10))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : False := by
  obtain ⟨r, p, hpair, hpeak, _, hN, _⟩ :=
    S.exists_lowerE2_universal_saturated_peak hW hq hdq hgap hglobal
  exact S.no_lowerE2_universal_saturated_peak r p hpair hW hq hdq hgap hglobal hpeak hN

end Erdos1017.CappedModel.SelectedHighLowStructure
