module

public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWUniversalZeroBody
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWPositiveBody
public import Erdos1017.SelectedModel.SelectedBodyEnergy

/-!
# No neutral common peak at the smooth `W` contact

A neutral original common forward peak is impossible at smooth-`W` contact, with
the positive and zero body cases both proved (`no_smoothW_neutral_common_peak`).
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

/-- A neutral original common forward peak is impossible at genuine
smooth-W contact, with the positive and zero body cases both proved. -/
theorem no_smoothW_neutral_common_peak
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) : False := by
  let I := {x | S.ρ x = r.val}
  by_cases hzero : PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) I = 0
  · exact S.no_smoothW_zero_body r hW hd hgap he hactive hglobal hzero
  · have hpositive := lt_of_le_of_ne (bodyPositiveEnergy_nonnegative W I) (Ne.symm hzero)
    rw [hW.bodyPositiveEnergy_eq_physicalBody hd hgap I (S.hfibers r.val r.property).1]
      at hpositive
    exact S.no_smoothW_universal_peak_positive_body r hW hd hgap he hactive hglobal
      hpeak hN hpositive

end Erdos1017.CappedModel.SelectedHighLowStructure
