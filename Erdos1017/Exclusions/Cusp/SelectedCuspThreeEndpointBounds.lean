module

public import Erdos1017.Exclusions.Cusp.SelectedCuspWholeSourceInventory
public import Erdos1017.Exclusions.Common.SharpCounts.MultipartiteSharpCountCells
public import Erdos1017.Exclusions.Cusp.BenchmarkCuspFourReverseBound

/-!
# Endpoint bounds at the third cusp

With own penalty at least one the reverse recovery has a singleton plateau, the
small-anchor strong selector forces its height above one third, the high-slope
endpoint lies below the benchmark-only missing-density cap, and the collision
bound pays the full-flow variance budget.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- At the third cusp, an actual own penalty at least one forces this
same reverse recovery to have a singleton plateau, including equality. -/
theorem cusp_three_plateau_singleton (R : S.ReverseRecovery) (hdk : d = 4 / 9)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c) (hell : 1 ≤ -m) :
    ∃ r : S.I, R.plateau = {r} := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by rw [hdk]; norm_num
  have hcard := R.card_lt_two_div_neg_multiplier hW hd hgap
  have hmul := (lt_div_iff₀ (by linarith : 0 < -m)).mp hcard
  have hprod := mul_le_mul_of_nonneg_left hell (Nat.cast_nonneg (α := ℝ) R.plateau.card)
  have hreal : (R.plateau.card : ℝ) < 2 := by linarith
  have hnat : R.plateau.card < 2 := by exact_mod_cast hreal
  exact Finset.card_eq_one.mp (by have := R.plateau_nonempty.card_pos; omega)

/-- The actual small-anchor strong selector, rather than a supplied
capped profile estimate, forces this recovery above the third cusp. -/
theorem cusp_three_height_gt_third (R : S.ReverseRecovery) (hdk : d = 4 / 9)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) (hell : 1 ≤ -m) :
    1 / 3 < R.height := by
  have hdk' : d = (1 - 1 / (3 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  obtain ⟨hd, _, _, _, hmargin⟩ :=
    hW.cusp_contact_parameters 3 (by norm_num) hdk' hgap hglobal
  obtain ⟨r, hr⟩ := R.cusp_three_plateau_singleton hdk hW hgap hell
  by_contra hn
  have hcap : R.height ≤ 1 / 3 := le_of_not_gt hn
  let ν := missingFlowEndpointLaw μ R.flow
  let := R.isFullReverseFlow.endpoint_probability
  let : NullSingletonClass ν := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hmass : MultipartiteClassMasses.classMass ν S.collapsedPartLabel r = R.height :=
    (R.classMass_eq_iff hW r).mpr (by rw [hr]; exact Finset.mem_singleton_self r)
  have hcost := MultipartiteClassMasses.objective_le_sharp_smallPart R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by
      filter_upwards [R.isFullReverseFlow.endpoint_collapsed_support hW hd hgap] with p hp
      split_ifs at hp ⊢ <;> exact hp)
    r (hmass ▸ R.height_pos) (hmass ▸ hcap) (by
      intro j
      rw [hmass]
      exact R.classMass_le hW j)
  have hcost' := hcost.trans (min_le_right _ _)
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hdrop := R.isFullReverseFlow.endpoint_density_lt hW hd hgap
  have hproduct := mul_pos (show 0 < -m - 2 / 3 by linarith only [hell])
    (sub_pos.mpr hdrop)
  norm_num at hmargin
  rw [hdk] at hbudget hproduct hmargin
  nlinarith only [hcost', hbudget, hE, hmargin, hproduct]

/-- The actual third-cusp high-slope endpoint lies strictly below the
benchmark-only missing-density cap, and hence genuinely in the split band. -/
theorem cusp_three_endpoint_bounds (R : S.ReverseRecovery) (hdk : d = 4 / 9)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) (hell : 1 ≤ -m) :
    1 - 2 * density R.isFullReverseFlow.endpoint < 25 / 144 ∧
      1 / 3 < R.height ∧ R.height < 5 / 12 ∧
      objective R.isFullReverseFlow.endpoint ≤
        Benchmark.splitValue (Real.sqrt (1 - 2 * density R.isFullReverseFlow.endpoint)) := by
  have hdk' : d = (1 - 1 / (3 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  obtain ⟨hd, _, _, _, hmargin⟩ :=
    hW.cusp_contact_parameters 3 (by norm_num) hdk' hgap hglobal
  have hheight := R.cusp_three_height_gt_third hdk hW hgap hglobal hell
  obtain ⟨r, hr⟩ := R.cusp_three_plateau_singleton hdk hW hgap hell
  let := R.isFullReverseFlow.endpoint_probability
  have hmem := density_mem R.isFullReverseFlow.endpoint
  have hcost := objective_le_benchmark_of_partition_support R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full) S.atomicDustPartLabel
    (R.isFullReverseFlow.endpoint_partition_support hW hd hgap)
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hH : 1 - 2 * density R.isFullReverseFlow.endpoint < 25 / 144 := by
    by_contra hn
    have hcap := Benchmark.benchmark_shifted_half_le_one_fifty_fourth
      ⟨le_of_not_gt hn, by linarith only [hmem.1]⟩
    have hid : (1 - (1 - 2 * density R.isFullReverseFlow.endpoint)) / 2 =
        density R.isFullReverseFlow.endpoint := by ring
    rw [hid] at hcap
    have hproduct := mul_nonneg (show 0 ≤ -m - 1 by linarith only [hell])
      (show 0 ≤ 1 - 2 * density R.isFullReverseFlow.endpoint - 1 / 9 by linarith only [hn])
    norm_num at hmargin
    rw [hdk] at hmargin hbudget
    nlinarith only [hcost, hcap, hbudget, hE, hmargin, hproduct]
  have hinventory := R.cuspEndpoint_missing_eq_whole r hW hd hgap hr
  have hQO : 0 ≤ R.cuspWholeOutsideSquares r := tsum_nonneg (fun _ => sq_nonneg _)
  have hheightCap : R.height < 5 / 12 := by
    nlinarith only [hH, hinventory, hQO, hheight]
  have hstar : 25 / 288 < Benchmark.epsilonStar := by
    unfold Benchmark.epsilonStar
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
    have hn := Real.sqrt_nonneg (21 : ℝ)
    nlinarith
  have hband : density R.isFullReverseFlow.endpoint ∈
      Ioo (1 / 2 - Benchmark.epsilonStar) (1 / 2) := by
    have hpositive : 0 < 1 - 2 * density R.isFullReverseFlow.endpoint := by
      nlinarith only [hinventory, hQO, hheight]
    constructor <;> linarith only [hH, hstar, hpositive]
  rw [(Benchmark.benchmark_split_eventually hband).eq_of_nhds] at hcost
  exact ⟨hH, hheight, hheightCap, hcost⟩

/-- The third-cusp collision bound pays the same full-flow variance
budget. It includes penalty exactly one and never divides by its excess. -/
theorem cusp_three_endpoint_source_budget (R : S.ReverseRecovery) (r : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) (hell : 1 ≤ -m)
    (hr : R.plateau = {r}) :
    c - 2 / 27 +
        kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) / 2 +
        (-m - 1) * R.cuspWholeOutsideSquares r / 2 ≤
      (4 / 3 + m) * (R.height ^ 2 - 1 / 9) / 2 := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by rw [hdk]; norm_num
  let ν := missingFlowEndpointLaw μ R.flow
  let := R.isFullReverseFlow.endpoint_probability
  let : NullSingletonClass ν := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hmass : MultipartiteClassMasses.classMass ν S.collapsedPartLabel r = R.height :=
    (R.classMass_eq_iff hW r).mpr (by rw [hr]; exact Finset.mem_singleton_self r)
  have hcost := MultipartiteClassMasses.objective_le_split_add_tail R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by
      filter_upwards [R.isFullReverseFlow.endpoint_collapsed_support hW hd hgap] with p hp
      split_ifs at hp ⊢ <;> exact hp)
    r (hmass ▸ R.height_pos) (by
      intro j
      rw [hmass]
      exact R.classMass_le hW j)
  rw [hmass, R.cuspEndpoint_missing_eq_whole r hW hd hgap hr] at hcost
  have hcurve := Benchmark.splitValue_le_reciprocal_mass_cap 3 (by norm_num)
    (R.cusp_three_height_gt_third hdk hW hgap hglobal hell).le
  norm_num at hcurve
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  rw [hdk, R.cuspEndpoint_missing_eq_whole r hW hd hgap hr] at hbudget
  linear_combination hcost + hcurve + hbudget / 2

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
