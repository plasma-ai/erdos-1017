module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateSoleSourceExposure

/-!
# Exclusion of the no-saturation middle `E₂` contact

The complete no-saturation middle `E₂` contact is impossible
(`no_middle_unsaturated_contact`): the recovery, private peak and sole-source
boundary are constructed internally, and strict hole exposure closes the case.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c q : ℝ}

/-- The complete no-saturation middle-E2 contact is impossible. The actual
recovery, private peak and sole-source boundary are constructed internally;
strict hole exposure contradicts the original curvature bound. -/
theorem no_middle_unsaturated_contact (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : (μ.prod μ) {z | chargeKernel W z.1 z.2 = 1} = 0) : False := by
  obtain ⟨_, _, _, p, i, _, hip, hpeak, _, _, hsrc, hprivate, _, hreverse⟩ :=
    S.exists_middle_unsaturated_sole_source_residual hW hq hdq hvalue hderiv hgap hglobal hnull
  have hexposure := S.middle_private_sole_source_exposure i p hip hW hq hdq hvalue hderiv
    hgap hglobal hnull hpeak hsrc hprivate
  exact (not_lt_of_ge hreverse) hexposure

end Erdos1017.CappedModel.SelectedHighLowStructure
