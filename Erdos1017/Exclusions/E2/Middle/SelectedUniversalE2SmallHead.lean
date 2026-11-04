module

public import Erdos1017.Exclusions.E2.Middle.SelectedUniversalMiddleSmallParameter
public import Erdos1017.Exclusions.E2.Middle.SelectedUniversalMiddleLowParameter
public import Erdos1017.Exclusions.E2.Middle.SelectedUniversalMiddleSmallHead

/-!
# No universal saturated peak of small mass

A universal saturated common peak of mass at most one third is impossible
throughout the full positive `E₂` parameter interval, with three overlapping
exits (`no_universal_e2_small_head_saturated_peak`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

/-- An actual universal saturated common peak of mass at most one third
is impossible throughout the full positive E2 parameter interval. The
three actual exits overlap at both rational subdivision endpoints. -/
theorem no_universal_e2_small_head_saturated_peak
    (S : SelectedHighLowStructure W m) (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = r.val then 0 else 1)
    (hsmallHead : S.originalAtomMass r ≤ 1 / 3) : False := by
  by_cases hsmall : q ≤ 7 / 50
  · exact S.no_universal_middle_small_parameter_saturated_peak r p hpair hW
      ⟨hq.1, hsmall⟩ hdq hgap hglobal hpeak huniv
  by_cases hlow : q ≤ 157 / 1000
  · exact S.no_universal_middle_low_parameter_saturated_peak r p hpair hW
      ⟨(lt_of_not_ge hsmall).le, hlow⟩ hdq hgap hglobal hpeak huniv
  · exact S.no_universal_middle_small_head_saturated_peak r p hpair hW
      ⟨(lt_of_not_ge hlow).le, hq.2⟩ hdq hgap hglobal hpeak huniv hsmallHead

end Erdos1017.CappedModel.SelectedHighLowStructure
