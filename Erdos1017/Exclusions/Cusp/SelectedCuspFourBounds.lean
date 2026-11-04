module

public import Erdos1017.Exclusions.Cusp.BenchmarkCuspFourReverseBound
public import Erdos1017.Exclusions.Cusp.SelectedCuspWholeSourceInventory

/-!
# Endpoint bounds at the fourth cusp

The fourth-cusp reverse endpoint lies below the `5/32` missing cutoff, by the
full multipartite benchmark bound and the same original multiplier budget, and
this cutoff licenses the dense split upper bound for the endpoint without any
global multipartite frontier identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- The fourth-cusp reverse endpoint lies below the actual 5/32 missing
cutoff. The proof uses its full multipartite benchmark bound and the same
original multiplier budget, without a dense-frontier premise. -/
theorem cusp_four_endpoint_bounds (R : S.ReverseRecovery) (hdk : d = 15 / 32)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    1 - 2 * density R.isFullReverseFlow.endpoint < 5 / 32 ∧
      1 / 4 < R.height ∧ R.height < 1 / 2 := by
  have hdk' : d = (1 - 1 / (4 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  obtain ⟨hd, hslope, _, _, hmargin⟩ :=
    hW.cusp_contact_parameters 4 (by norm_num) hdk' hgap hglobal
  have hell : 11 / 10 < -m := by norm_num at hslope; exact hslope.1
  have hc : 3 / 64 < c := by rw [hdk] at hmargin; norm_num at hmargin; linarith
  let := R.isFullReverseFlow.endpoint_probability
  have hmem := density_mem R.isFullReverseFlow.endpoint
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hMP := objective_le_benchmark_of_partition_support R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full) S.atomicDustPartLabel
    (R.isFullReverseFlow.endpoint_partition_support hW hd hgap)
  have hH : 1 - 2 * density R.isFullReverseFlow.endpoint < 5 / 32 := by
    by_contra hn
    have hHlo : 5 / 32 ≤ 1 - 2 * density R.isFullReverseFlow.endpoint := le_of_not_gt hn
    have hbound := Benchmark.benchmark_lt_four_cusp_line
      ⟨hHlo, show 1 - 2 * density R.isFullReverseFlow.endpoint ≤ 1 by linarith [hmem.1]⟩
    rw [show (1 - (1 - 2 * density R.isFullReverseFlow.endpoint)) / 2 =
      density R.isFullReverseFlow.endpoint by ring] at hbound
    have hp := mul_pos (show 0 < -m - 11 / 10 by linarith only [hell])
      (show 0 < 1 - 2 * density R.isFullReverseFlow.endpoint - 1 / 16 by linarith only [hHlo])
    rw [hdk] at hbudget
    nlinarith only [hMP, hbound, hbudget, hE, hc, hp]
  obtain ⟨r, hr⟩ := R.cusp_plateau_singleton 4 (by norm_num) hdk' hW hgap hglobal
  have hinventory := R.cuspEndpoint_missing_eq_whole r hW hd hgap hr
  have hQO : 0 ≤ R.cuspWholeOutsideSquares r := tsum_nonneg (fun _ => sq_nonneg _)
  have hlo := R.cusp_height_gt_reciprocal 4 (by norm_num) hdk' hW hgap hglobal
  norm_num only [Nat.cast_ofNat] at hlo
  exact ⟨hH, hlo, by nlinarith only [hH, hinventory, hQO, R.height_pos]⟩

/-- The proved fourth-cusp cutoff licenses the actual dense split upper
bound for this same endpoint; no global multipartite frontier identity is used. -/
theorem cusp_four_endpoint_split (R : S.ReverseRecovery) (hdk : d = 15 / 32)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    objective R.isFullReverseFlow.endpoint ≤
      Benchmark.splitValue (Real.sqrt (1 - 2 * density R.isFullReverseFlow.endpoint)) := by
  have hb := R.cusp_four_endpoint_bounds hdk hW hgap hglobal
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by rw [hdk]; norm_num
  let := R.isFullReverseFlow.endpoint_probability
  have hmem := density_mem R.isFullReverseFlow.endpoint
  have hMP := objective_le_benchmark_of_partition_support R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full) S.atomicDustPartLabel
    (R.isFullReverseFlow.endpoint_partition_support hW hd hgap)
  rw [Benchmark.benchmark_eq_split_of_dense ⟨by linarith [hb.1], hmem.2⟩] at hMP
  exact hMP

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
