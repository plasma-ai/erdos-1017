module

public import Erdos1017.Exclusions.Common.Universal.UniversalCopyCubic
public import Erdos1017.Exclusions.SmoothW.FullSharpWPeak

/-!
# Positive-body universal peak at the smooth `W` contact

Exact rational guards contradict the positive-body universal trace, the sharp
`W` guards belong to the same supplied common original peak by separated-peak
uniqueness, and the smooth-`W` universal-common-peak positive-body branch is
excluded with all guards and trace derived internally
(`no_smoothW_universal_peak_positive_body`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.SmoothWScalar

/-- Exact rational guards contradict the positive-body universal trace. -/
theorem not_trace_of_sharp_guards {A g h : ℝ}
    (hA : 357 / 1000 < A) (hg : 103 / 1000 < g) (hh : h < 1163 / 5000) :
    ¬(3 * A ^ 2 + 2 * A * g + g ^ 2 ≤ 2 * h) := by
  have hA0 : 0 < A := by linarith
  have hg0 : 0 < g := by linarith
  have hAsq := mul_pos (sub_pos.mpr hA) (show 0 < A + 357 / 1000 by linarith)
  have hgsq := mul_pos (sub_pos.mpr hg) (show 0 < g + 103 / 1000 by linarith)
  have hprod := mul_lt_mul hA hg.le (by norm_num : (0 : ℝ) < 103 / 1000) hA0.le
  intro htrace
  nlinarith

end Erdos1017.SmoothWScalar

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ}

/-- The sharp W guards belong to the same supplied common original peak,
by actual separated-peak uniqueness on a genuine full forward flow. -/
theorem smoothW_common_peak_guards (S : SelectedHighLowStructure W m) (r : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r) :
    357 / 1000 < μ.real {x | S.ρ x = r.val} ∧
      103 / 1000 < 2 * (c - m * d) + m ∧ 1 - 2 * d < 1163 / 5000 := by
  obtain ⟨hΔ, i, hA, hg, _, hi, _, _⟩ :=
    S.exists_sharp_smoothW_peak hW hd hgap he hactive hglobal
  have heq : i = r := (hi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst i
  have hh := (hW.smoothW_contact_parameters hd hgap he hactive hglobal).2.2.2.2.2
  exact ⟨hA, hg, hh⟩

/-- This excludes only the actual smooth-W universal-common-peak
positive-body branch, with all rational guards and trace derived internally. -/
theorem no_smoothW_universal_peak_positive_body (S : SelectedHighLowStructure W m) (r : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpositive : 0 < ∫ p : Ω × Ω,
      (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        {x | S.ρ x = r.val} p.1 p.2) ^ 2 ∂μ.prod μ) : False := by
  obtain ⟨hA, hg, hh⟩ := S.smoothW_common_peak_guards r hW hd hgap he hactive hglobal hpeak
  exact SmoothWScalar.not_trace_of_sharp_guards hA hg hh
    (S.universal_positive_body_trace r hW hd hgap hN hpositive)

end Erdos1017.CappedModel.SelectedHighLowStructure
