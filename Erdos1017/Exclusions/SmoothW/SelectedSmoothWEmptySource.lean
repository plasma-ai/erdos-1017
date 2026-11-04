module

public import Erdos1017.SelectedModel.SelectedBodyEnergy
public import Erdos1017.Exclusions.Common.SelectedEmptySource
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWPositiveBody
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWUniversalZeroBody

/-!
# No empty source for the smooth `W` singleton recovery

A singleton reverse recovery cannot have null entire source at smooth-`W`
contact; its original common peak, universal head and both body-energy
alternatives are derived on the selected model
(`no_smoothW_one_center_empty_source`).
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

/-- An actual singleton reverse recovery cannot have null entire source
at smooth-W contact. Its original common peak, universal head and both
body-energy alternatives are constructed on the same original law. -/
theorem no_smoothW_one_center_empty_source (R : S.ReverseRecovery)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) : False := by
  obtain ⟨r, _, hpeak, _, hN, _, _, _⟩ :=
    R.exists_empty_source_universal_peak hW hd hgap hcard hnull
  let I := {x | S.ρ x = r.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hnonnegative := bodyPositiveEnergy_nonnegative W I
  by_cases hzero : PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) I = 0
  · exact S.no_smoothW_zero_body r hW hd hgap he hactive hglobal hzero
  have hpositive := lt_of_le_of_ne hnonnegative (Ne.symm hzero)
  rw [hW.bodyPositiveEnergy_eq_physicalBody hd hgap I hI] at hpositive
  exact S.no_smoothW_universal_peak_positive_body r hW hd hgap he hactive hglobal
    hpeak hN hpositive

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
