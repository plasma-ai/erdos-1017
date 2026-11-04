module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalExclusion
public import Erdos1017.Exclusions.E2.Upper.SelectedE2TwoCenter
public import Erdos1017.Exclusions.E2.Upper.SelectedE2EmptySource

/-!
# Exclusion of the upper `E₂` range

The complete closed upper `E₂` interval is excluded on the original selected
model, with reverse recovery and every plateau and entire-source case derived
(`no_upperE2_contact`). This is one of the exclusions assembled in
`FullBenchmarkUpper`.
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
  {W : Model Ω μ} {m d c q : ℝ}

/-- The complete closed upper-E2 interval is excluded on the original selected
model. Reverse recovery and every plateau and entire-source case are derived. -/
theorem no_upperE2_contact (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : False := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) :=
    ⟨by linarith only [hq.1], by linarith only [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, _, _⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hslope : (2 / 3 : ℝ) ≤ -m := by
    rw [hm, neg_neg, LowerE2Scalar.multiplier]
    rw [le_div_iff₀ (by linarith only [hq.1] : 0 < 2 + q)]
    linarith only [hq.2]
  obtain ⟨R⟩ := S.exists_reverseRecovery hW hd hgap
  have hcard := R.card_le_two_of_neg_multiplier_ge_two_thirds hW hd hgap hslope
  have hpositive := Finset.card_pos.mpr R.plateau_nonempty
  by_cases hone : R.plateau.card = 1
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hone
    by_cases hnull : μ (S.reverseCompulsorySource R.plateau) = 0
    · exact R.no_e2_one_center_empty_source r hr hW ⟨hq'.1, hq.2⟩ hdq hvalue
        hderiv hgap hglobal hnull
    · exact R.no_upper_e2_one_center_positive_source hW hq hdq hvalue hderiv hgap
        hglobal hone (pos_iff_ne_zero.mpr hnull)
  · exact R.no_e2_two_center hW ⟨by linarith only [hq.1], hq.2⟩ hdq hvalue hderiv
      hgap hglobal (by omega)

end Erdos1017.CappedModel.SelectedHighLowStructure
