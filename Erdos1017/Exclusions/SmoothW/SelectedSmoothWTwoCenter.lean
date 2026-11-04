module

public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWNeutralPeak
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWTwoCenterLocations

/-!
# No two-center recovery at the smooth `W` contact

Smooth-`W` recovery cannot have two original centers; the common peak and its
neutral-head location are constructed internally (`no_smoothW_two_center`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- Actual smooth-W recovery cannot have two original centers. The
common peak and its neutral-head location are constructed internally. -/
theorem no_smoothW_two_center (R : S.ReverseRecovery)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 2) : False := by
  obtain ⟨_, r, _, _, _, hpeak, _⟩ :=
    S.exists_sharp_smoothW_peak hW hd hgap he hactive hglobal
  have hr := R.smoothW_common_peak_mem_plateau hW hd hgap he hactive hglobal hcard r hpeak
  exact S.no_smoothW_neutral_common_peak r hW hd hgap he hactive hglobal hpeak
    (R.common_peak_head_neutral r hr hpeak)

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
