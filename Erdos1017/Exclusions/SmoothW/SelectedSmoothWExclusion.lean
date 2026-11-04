module

public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWRecovery
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWEmptySource
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWOneCenterExclusion
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWTwoCenter

/-!
# Exclusion of a smooth point of `W`

Global excess contact in the strictly active smooth-`W` region is impossible,
with the original recovery and every case derived internally
(`no_smoothW_contact`).
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

/-- Genuine global excess contact in the strict active smooth-W region
is impossible. The original recovery and every case are derived internally. -/
theorem no_smoothW_contact
    (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : False := by
  obtain ⟨R⟩ := S.exists_reverseRecovery hW hd hgap
  rcases R.smoothW_plateau_card_eq_one_or_two hW hd hgap he hactive hglobal with hcard | hcard
  · by_cases hnull : μ (S.reverseCompulsorySource R.plateau) = 0
    · exact R.no_smoothW_one_center_empty_source hW hd hgap he hactive hglobal hcard hnull
    · exact R.no_smoothW_one_center_nonempty_source hW hd hgap he hactive hglobal hcard
        (pos_iff_ne_zero.mpr hnull)
  · exact R.no_smoothW_two_center hW hd hgap he hactive hglobal hcard

end Erdos1017.CappedModel.SelectedHighLowStructure
