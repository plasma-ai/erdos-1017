module

public import Erdos1017.Exclusions.Corner.SelectedCornerRecovery
public import Erdos1017.Exclusions.Corner.SelectedCornerUniversalPrice

/-!
# Exclusion of the corner recovery with positive source

A corner recovery cannot have a positive whole source; its one-center plateau,
common peak and universal saturated exit are derived.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- An actual corner recovery cannot have positive entire source. Its
one-center plateau, original common peak and universal saturated exit are derived. -/
theorem ReverseRecovery.no_corner_positive_source (R : S.ReverseRecovery)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hsource : 0 < μ (S.reverseCompulsorySource R.plateau)) : False := by
  have hcard := R.corner_plateau_card_eq_one hW hd hgap he heq hglobal
  obtain ⟨_, r, _, hpeak, _, _⟩ := S.exists_sharp_corner_peak hW hd hgap he heq hglobal
  change S.IsCommonForwardPeak d c r at hpeak
  obtain ⟨p, hplateau, _, hpair, huniv⟩ :=
    R.exists_corner_one_center_saturated_universal hW hd hgap he heq hglobal
      hcard hsource r hpeak
  exact R.no_corner_one_center_universal r p hplateau hW hd hgap he heq hglobal
    hpair hpeak huniv

end Erdos1017.CappedModel.SelectedHighLowStructure
