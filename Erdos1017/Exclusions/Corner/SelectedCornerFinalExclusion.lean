module

public import Erdos1017.Exclusions.Corner.SelectedCornerExclusion

/-!
# Exclusion of the `W`/`E₂` corner

A global excess contact at the `W`/`E₂` corner is impossible: the recovery and
both whole-source alternatives are derived and excluded. This is one of the
exclusions assembled in `FullBenchmarkUpper`.
-/

@[expose] public section

noncomputable section

set_option Elab.async false

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ}

/-- Genuine global excess contact at the W/E2 corner is impossible.
The actual recovery and both entire-source alternatives are derived. -/
theorem no_corner_global_excess (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : False := by
  obtain ⟨R⟩ := S.exists_reverseRecovery hW hd hgap
  by_cases hnull : μ (S.reverseCompulsorySource R.plateau) = 0
  · have hcard := R.corner_plateau_card_eq_one hW hd hgap he heq hglobal
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard
    exact R.no_corner_one_center_empty_source r hr hW hd hgap he heq hglobal hnull
  · exact R.no_corner_positive_source hW hd hgap he heq hglobal
      (pos_iff_ne_zero.mpr hnull)

end Erdos1017.CappedModel.SelectedHighLowStructure
