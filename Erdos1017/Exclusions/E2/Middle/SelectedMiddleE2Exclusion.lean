module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSaturatedDichotomy
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSaturatedPrivateExclusion
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleLargeUniversalPrice
public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateSound

/-!
# Exclusion of the middle `E₂` range

The open middle range of `E₂` is excluded, conditional only on the final finite
fixed-point cover (`no_middle_e2_contact_of_cover`): the common peak, saturated
pair, private alternative and necessary system are all derived on the selected
model. This is one of the exclusions assembled in `FullBenchmarkUpper`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  [StandardBorelSpace Ω] [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

/-- Actual open-middle E2 exclusion, conditional only on the final finite
fixed-point cover. The common peak, saturated pair, private alternative,
necessary system and same-point price tests are all derived internally. -/
theorem no_middle_e2_contact_of_cover (S : SelectedHighLowStructure W m)
    (hcover : MiddleE2LargeUniversal.FixedPoint.cover 80
      MiddleE2LargeUniversal.FixedPoint.IBox.root = true)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : False := by
  obtain ⟨i, hpeak, hcases⟩ := S.exists_middle_saturated_dichotomy hW hq hdq hvalue
    hderiv hgap hglobal
  rcases hcases with ⟨p, hpair, _, _, huniv⟩ |
      ⟨p, u, hpair, hip, hiu, _, _, _, _, _, _, hprivate⟩
  · obtain ⟨_, _, _, _, hbox, hnecessary⟩ := S.middle_large_universal_necessary_system
      i p hpair hW hq hdq hgap hglobal hpeak huniv
    have htests := MiddleE2LargeUniversal.FixedPoint.priceTests_of_cover hcover hbox hnecessary
    exact S.no_middle_large_universal_of_price_tests i p hpair hW hq hdq hgap hglobal
      hpeak huniv hnecessary htests
  · exact S.no_middle_saturated_private_contact p u i hpair hip hiu hW hq hdq hvalue
      hderiv hgap hglobal hpeak hprivate

end Erdos1017.CappedModel.SelectedHighLowStructure
