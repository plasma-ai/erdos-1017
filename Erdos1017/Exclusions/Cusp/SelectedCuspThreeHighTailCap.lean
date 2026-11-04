module

public import Erdos1017.Exclusions.Cusp.MultipartiteHeadDustComparison
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeEndpointBounds

/-!
# Tail cap for the third-cusp high-slope endpoint

A head-to-dust edit of the current reverse endpoint pays the strict normalized
tail cap, with no stationarity assigned to the endpoint
(`cusp_three_high_outsideSquares_lt_half`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- A genuine head-to-dust edit of the current reverse endpoint pays the
strict normalized tail cap. The endpoint is never assigned stationarity. -/
theorem cusp_three_high_outsideSquares_lt_half (R : S.ReverseRecovery) (r : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) (hell : 1 ≤ -m)
    (hr : R.plateau = {r}) :
    R.cuspWholeOutsideSquares r / R.height ^ 2 < 1 / 2 := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by rw [hdk]; norm_num
  let T := R.height
  let Q := R.cuspWholeOutsideSquares r
  let ν := missingFlowEndpointLaw μ R.flow
  let := R.isFullReverseFlow.endpoint_probability
  let : NullSingletonClass ν := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hhead : MultipartiteClassMasses.classMass ν S.collapsedPartLabel r = T :=
    (R.classMass_eq_iff hW r).mpr (by rw [hr]; exact Finset.mem_singleton_self r)
  obtain ⟨hcut, hTlo, hThi, _⟩ := R.cusp_three_endpoint_bounds hdk hW hgap hglobal hell
  have hH := R.cuspEndpoint_missing_eq_whole r hW hd hgap hr
  change 1 - 2 * density R.isFullReverseFlow.endpoint = T ^ 2 + Q at hH
  have hsum := R.isFullReverseFlow.missing_density_eq_classMass_sq hW hd hgap
  have hother (j : S.I) (hj : j ≠ r) :
      MultipartiteClassMasses.classMass ν S.collapsedPartLabel j ≤ 1 / 3 := by
    have hb := R.isFullReverseFlow.classMass_sq_summable.sum_le_tsum {r, j}
      (fun k _ => sq_nonneg (S.reverseClassMass R.flow k))
    have hrj : r ≠ j := Ne.symm hj
    simp only [Finset.sum_insert (Finset.notMem_singleton.mpr hrj), Finset.sum_singleton] at hb
    rw [← hsum] at hb
    change (MultipartiteClassMasses.classMass ν S.collapsedPartLabel r) ^ 2 +
      (MultipartiteClassMasses.classMass ν S.collapsedPartLabel j) ^ 2 ≤ _ at hb
    rw [hhead] at hb
    by_contra hn
    have hlarge := lt_of_not_ge hn
    change 1 / 3 < T at hTlo
    nlinarith only [hb, hcut, hTlo, hlarge]
  have hcost := MultipartiteClassMasses.objective_le_shrunk_third
    R.isFullReverseFlow.endpoint (R.isFullReverseFlow.endpoint_fullFeasible hW.full)
    S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by
      filter_upwards [R.isFullReverseFlow.endpoint_collapsed_support hW hd hgap] with p hp
      split_ifs at hp ⊢ <;> exact hp)
    r (hhead ▸ hTlo) hother
  rw [hhead, hH] at hcost
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hp := hW.cusp_contact_parameters 3 (by norm_num)
    (show d = (1 - 1 / (3 : ℝ) ^ 2) / 2 by norm_num [hdk]) hgap hglobal
  have hc : 2 / 27 < c := by
    have h := hp.2.2.2.2
    rw [hdk] at h
    norm_num at h
    linarith only [h]
  have hQ : 0 ≤ Q := tsum_nonneg (fun _ => sq_nonneg _)
  have hproduct := mul_nonneg (show 0 ≤ -m - 1 by linarith only [hell])
    (show 0 ≤ T ^ 2 + Q - 1 / 9 by nlinarith only [hTlo, hQ])
  rw [hdk, hH] at hbudget
  have hcredit : Q / 6 < (T - 1 / 3) * (5 / 6 - 3 * T / 2) := by
    nlinarith only [hcost, hbudget, hE, hc, hproduct, hH]
  have hT0 : 0 < T := R.height_pos
  apply (div_lt_iff₀ (sq_pos_of_pos hT0)).mpr
  by_cases hsmall : T ≤ 7 / 20
  · have hp := mul_nonneg (show 0 ≤ T - 1 / 3 by linarith only [hTlo])
        (show 0 ≤ 3 * T / 2 - 1 / 2 by linarith only [hTlo])
    nlinarith only [hcredit, hp, hsmall, hTlo]
  · have ht := lt_of_not_ge hsmall
    nlinarith only [hcut, hH, ht]

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
