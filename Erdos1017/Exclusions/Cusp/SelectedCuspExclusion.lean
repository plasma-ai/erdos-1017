module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeExclusion
public import Erdos1017.Exclusions.Cusp.SelectedCuspFourExclusion
public import Erdos1017.Exclusions.Cusp.SelectedCuspFiveExclusion
public import Erdos1017.Exclusions.Cusp.SelectedCuspLargeExclusion

/-!
# Exclusion of the reciprocal cusps

No reciprocal cusp of the split value can carry a selected positive maximum of
`F - B`: the third, fourth, fifth and larger cusps together cover every index
(`no_cusp_contact`). This is one of the exclusions assembled in
`FullBenchmarkUpper`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ}

/-- No reciprocal split cusp can support a selected positive global
excess. The third, fourth, fifth and all larger cusps cover every index. -/
theorem no_cusp_contact (S : SelectedHighLowStructure W m)
    (k : ℕ) (hk : 3 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : False := by
  by_cases hlarge : 6 ≤ k
  · exact S.no_cusp_contact_of_six_le k hlarge hdk hW hgap hglobal
  · have hcases : k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact S.no_cusp_three_contact (by norm_num at hdk ⊢; exact hdk) hW hgap hglobal
    · exact S.no_cusp_four_contact (by norm_num at hdk ⊢; exact hdk) hW hgap hglobal
    · exact S.no_cusp_five_contact (by norm_num at hdk ⊢; exact hdk) hW hgap hglobal

end Erdos1017.CappedModel.SelectedHighLowStructure
