module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeRNull
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreePositiveRegions
public import Erdos1017.Exclusions.Cusp.SelectedCuspUnsaturatedZeroBody

/-!
# No zero positive-body energy at a third-cusp atom

An original third-cusp atom cannot have zero positive-body energy: every
diffuse-region alternative of the saturated case is excluded with no region or
exterior-atom certificate supplied, and both saturation alternatives are derived
(`no_cusp_three_zero_body`).
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

/-- Every diffuse-region alternative of the actual saturated third-cusp
zero-body case is excluded. No region or exterior-atom certificate is supplied. -/
theorem no_cusp_three_saturated_zero_body
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hdk : d = 4 / 9)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) : False := by
  by_cases hR : μ (S.D ∩ S.rootNeighborhood a) = 0
  · exact S.no_cusp_three_zero_body_R_null r a hW hdk hgap hglobal hpair hzero hR
  · by_cases hE : μ (S.D \ S.rootNeighborhood a) = 0
    · exact S.no_cusp_three_zero_body_E_null r a hW hdk hgap hglobal hpair hzero hE
    · exact S.no_cusp_three_zero_body_of_positive_regions r a hW hdk hgap hglobal
        hpair hzero (pos_iff_ne_zero.mpr hR) (pos_iff_ne_zero.mpr hE)

/-- An original third-cusp atom cannot have zero positive-body energy. Both
saturation alternatives and all diffuse/exterior boundaries are derived. -/
theorem no_cusp_three_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hdk : d = 4 / 9)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) : False := by
  by_cases hsat : ∃ a : S.I, S.IsSaturatedAtomPair r a
  · obtain ⟨a, hpair⟩ := hsat
    exact S.no_cusp_three_saturated_zero_body r a hW hdk hgap hglobal hpair hzero
  · exact S.not_cusp_zero_body_of_no_saturated_partner r hW 3 (by omega)
      (by norm_num; exact hdk) hgap hglobal
      hzero (fun a _ hpair => hsat ⟨a, hpair⟩)

end Erdos1017.CappedModel.SelectedHighLowStructure
