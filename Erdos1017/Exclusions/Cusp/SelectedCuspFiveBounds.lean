module

public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceHeadBound
public import Erdos1017.Exclusions.Cusp.SelectedCuspWholeSourceInventory
public import Erdos1017.Exclusions.Common.BoundedKernelSupportBound

/-!
# Endpoint bounds at the fifth cusp

At the fifth cusp the support bound already gives `H < 5/32`, which is stronger
than the height bound needed by the whole-source child
(`cusp_five_endpoint_bounds`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- At the fifth cusp the actual support bound already gives H<5/32,
which is stronger than the height bound needed by the source child. -/
theorem cusp_five_endpoint_bounds (R : S.ReverseRecovery) (hdk : d = 12 / 25)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    1 - 2 * density R.isFullReverseFlow.endpoint < 5 / 32 ∧
      1 / 5 < R.height ∧ R.height < 2 / 5 := by
  have hdk' : d = (1 - 1 / (5 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  obtain ⟨hd, hslope, _, hgamma, _⟩ :=
    hW.cusp_contact_parameters 5 (by norm_num) hdk' hgap hglobal
  have hell : 19 / 15 < -m := by norm_num at hslope; exact hslope.1
  let := R.isFullReverseFlow.endpoint_probability
  have hmem := density_mem R.isFullReverseFlow.endpoint
  have hcost := fullFeasible_objective_le_densityLimit R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full)
  have hsupport := FractionalGraph.densityLimit_add_density_le hmem
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hproduct := mul_nonneg (show 0 ≤ -m - 19 / 15 by linarith only [hell])
    (show 0 ≤ 1 - 2 * density R.isFullReverseFlow.endpoint by linarith only [hmem.2])
  have hH : 1 - 2 * density R.isFullReverseFlow.endpoint < 5 / 32 := by
    nlinarith only [hcost, hsupport, hbudget, hE, hgamma, hproduct]
  obtain ⟨r, hr⟩ := R.cusp_plateau_singleton 5 (by norm_num) hdk' hW hgap hglobal
  have hinventory := R.cuspEndpoint_missing_eq_whole r hW hd hgap hr
  have hQO : 0 ≤ R.cuspWholeOutsideSquares r := tsum_nonneg (fun _ => sq_nonneg _)
  have hlo := R.cusp_height_gt_reciprocal 5 (by norm_num) hdk' hW hgap hglobal
  norm_num only [Nat.cast_ofNat] at hlo
  exact ⟨hH, hlo, by nlinarith only [hH, hinventory, hQO, R.height_pos]⟩

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
