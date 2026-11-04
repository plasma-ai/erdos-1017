module

public import Erdos1017.Exclusions.Common.MultipartiteHeadPrice
public import Erdos1017.SelectedModel.Recovery.SelectedReverseRecovery
public import Erdos1017.SelectedModel.Structure.WholeRowCrossBlocks

/-!
# Head price of a two-center recovery

This module defines the two-head price under the recovered endpoint's law,
bounds it above by one and below under the intercept guard, and identifies it
with the original conditional charge mean by cross-block homogeneity and
absolute continuity, so a two-element plateau gives the original-law head-price
bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The actual two-head price under the recovered endpoint's own law,
using the unchanged original charge kernel and literal original classes. -/
def currentHeadPrice (R : S.ReverseRecovery) (r u : S.I) : ℝ :=
  MultipartiteHeadPrice.headPrice R.isFullReverseFlow.endpoint
    (S.collapsedPartLabel ⁻¹' {some r}) (S.collapsedPartLabel ⁻¹' {some u})

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Positive recovered head masses normalize their current conditional
laws and keep the actual old charge mean at most one. -/
theorem currentHeadPrice_le_one (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (r u : S.I) (hr : r ∈ R.plateau) (hu : u ∈ R.plateau) :
    R.currentHeadPrice r u ≤ 1 := by
  have := R.isFullReverseFlow.endpoint_probability
  have hmr := (R.classMass_eq_iff hW r).mpr hr
  have hmu := (R.classMass_eq_iff hW u).mpr hu
  have hr0 : missingFlowEndpointLaw μ R.flow (S.collapsedPartLabel ⁻¹' {some r}) ≠ 0 := by
    intro hz
    change (missingFlowEndpointLaw μ R.flow).real (S.collapsedPartLabel ⁻¹' {some r}) = R.height at hmr
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hmr
    linarith [R.height_pos]
  have hu0 : missingFlowEndpointLaw μ R.flow (S.collapsedPartLabel ⁻¹' {some u}) ≠ 0 := by
    intro hz
    change (missingFlowEndpointLaw μ R.flow).real (S.collapsedPartLabel ⁻¹' {some u}) = R.height at hmu
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hmu
    linarith [R.height_pos]
  exact MultipartiteHeadPrice.headPrice_le_one R.isFullReverseFlow.endpoint _ _ hr0 hu0

/-- The actual two-center budget and explicit intercept put the common
head mass above one third before the physical head-price law is applied. -/
theorem two_center_parameters (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hcard : R.plateau.card = 2)
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m) :
    0 < -m ∧ -m < 1 ∧ 1 / 3 < R.height ∧ R.height ≤ 1 / 2 := by
  have hs := hW.strict_gap_structure hd hgap
  have hm : 0 < -m := neg_pos.mpr hs.multiplier_neg
  have hplateau : ∀ r ∈ R.plateau, S.reverseClassMass R.flow r = R.height :=
    fun r hr => (R.classMass_eq_iff hW r).mpr hr
  have hmass := R.isFullReverseFlow.plateau_mass_bounds hW hd hgap R.plateau R.height hplateau
  have hcount := R.card_lt_two_div_neg_multiplier hW hd hgap
  rw [hcard] at hmass hcount
  norm_num only [Nat.cast_ofNat] at hmass hcount
  have hmul := (lt_div_iff₀ hm).mp hcount
  have hell : -m < 1 := by linarith
  have hbudget := R.isFullReverseFlow.plateau_budget hW hd hgap R.plateau R.height
    (R.classMass_le hW) hplateau
  rw [hcard] at hbudget
  norm_num only [Nat.cast_ofNat] at hbudget
  have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hplain : 2 * (c - m * d) + m ≤ 2 * (1 + m) * R.height ^ 2 := by
    nlinarith [hbudget.1, hbudget.2]
  have ht := TwoCenterHeadPrice.one_third_lt_of_intercept R.height_pos.le
    (show 0 < 1 + m by linarith) hintercept hplain
  exact ⟨hm, hell, ht, by linarith [hmass.1]⟩

/-- The actual full endpoint objective retains its own conditional head
price slack, with all masses and multipartite support derived from recovery. -/
theorem two_center_objective_bound (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r u : S.I) (hru : r ≠ u) (hr : r ∈ R.plateau)
    (hu : u ∈ R.plateau) (ht : 1 / 3 < R.height) :
    objective R.isFullReverseFlow.endpoint ≤ R.height ^ 2 - R.height * (3 * R.height - 1) *
      (1 - R.currentHeadPrice r u) := by
  have := R.isFullReverseFlow.endpoint_probability
  have : NullSingletonClass (missingFlowEndpointLaw μ R.flow) := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  apply MultipartiteHeadPrice.objective_le_two_head_price R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full) S.collapsedPartLabel
    S.measurable_collapsedPartLabel r u hru ht
    ((R.classMass_eq_iff hW r).mpr hr) ((R.classMass_eq_iff hW u).mpr hu)
  filter_upwards [R.isFullReverseFlow.endpoint_collapsed_support hW hd hgap] with p hp
  by_cases he : S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none
  · simpa only [he, ite_true] using hp
  · simpa only [he, ite_false] using hp

/-- A recovered two-center configuration with the stated original intercept
guard has the claimed lower bound on its actual current-law head price. -/
theorem current_head_price_lower_bound (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hcard : R.plateau.card = 2)
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (r u : S.I) (hru : r ≠ u) (hr : r ∈ R.plateau) (hu : u ∈ R.plateau) :
    -m + 2 * (2 * (c - m * d) + m) ≤ R.currentHeadPrice r u := by
  obtain ⟨_, hell, ht, htop⟩ := R.two_center_parameters hW hd hgap hcard hintercept
  have hcost := R.two_center_objective_bound hW hd hgap r u hru hr hu ht
  have hplateau : ∀ v ∈ R.plateau, S.reverseClassMass R.flow v = R.height :=
    fun v hv => (R.classMass_eq_iff hW v).mpr hv
  have hmissing := (R.isFullReverseFlow.plateau_mass_bounds hW hd hgap R.plateau R.height hplateau).2
  rw [hcard] at hmissing
  norm_num only [Nat.cast_ofNat] at hmissing
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hmissingCost := mul_le_mul_of_nonpos_left hmissing hm.le
  have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  have hhead : 2 * (c - m * d) + m ≤ 2 * (1 - -m) * R.height ^ 2 -
      2 * R.height * (3 * R.height - 1) * (1 - R.currentHeadPrice r u) := by
    nlinarith
  apply TwoCenterHeadPrice.head_price_lower_bound ht htop hell
    (R.currentHeadPrice_le_one hW r u hr hu)
  · simpa only [sub_neg_eq_add] using hintercept
  · exact hhead


omit [StandardBorelSpace Ω] [MeasurableEq Ω] in
private theorem integral_cellLaw_prod_of_const (ν : Measure Ω) [IsProbabilityMeasure ν]
    (I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J) (hI0 : ν I ≠ 0) (hJ0 : ν J ≠ 0)
    (Y : Ω × Ω → ℝ) (k : ℝ)
    (hconst : ∀ᵐ p ∂ν.prod ν, p.1 ∈ I → p.2 ∈ J → Y p = k) :
    (∫ p, Y p ∂(MultipartiteHeadPrice.headLaw ν I).prod (MultipartiteHeadPrice.headLaw ν J)) = k := by
  have := PhysicalCliqueRepresentative.cellLaw_probability ν I hI0
  have := PhysicalCliqueRepresentative.cellLaw_probability ν J hJ0
  have hc := ((PhysicalCliqueRepresentative.cellLaw_absolutelyContinuous ν I).prod
    (PhysicalCliqueRepresentative.cellLaw_absolutelyContinuous ν J)).ae_le hconst
  have heq : Y =ᵐ[(MultipartiteHeadPrice.headLaw ν I).prod (MultipartiteHeadPrice.headLaw ν J)]
      fun _ => k := by
    filter_upwards [hc,
      Measure.quasiMeasurePreserving_fst.ae (MultipartiteHeadPrice.ae_mem_headLaw (μ := ν) hI),
      Measure.quasiMeasurePreserving_snd.ae (MultipartiteHeadPrice.ae_mem_headLaw (μ := ν) hJ)]
      with p hp hi hj
    exact hp hi hj
  rw [integral_congr_ae heq]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Whole-row cross-block homogeneity and actual endpoint absolute
continuity identify the current and original conditional charge means.
No endpoint stationarity is used in this comparison. -/
theorem current_head_price_eq_original (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (r u : S.I) (hr : r ∈ R.plateau) (hu : u ∈ R.plateau) :
    R.currentHeadPrice r u = MultipartiteHeadPrice.headPrice W
      (S.collapsedPartLabel ⁻¹' {some r}) (S.collapsedPartLabel ⁻¹' {some u}) := by
  have := R.isFullReverseFlow.endpoint_probability
  let ν := missingFlowEndpointLaw μ R.flow
  have hν : ν ≪ μ := by
    change μ.withDensity _ ≪ μ
    exact withDensity_absolutelyContinuous _ _
  have hIr := S.hfibers r.val r.property
  have hIu := S.hfibers u.val u.property
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 :=
    (shiftedMoment_symm W m).mono (fun _ hx => hx.symm)
  obtain ⟨q, _, _, _, hcross⟩ := KernelOperator.exists_whole_row_cross_block
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ r.val u.val
    hIr.2.1 hIu.2.1 hIr.2.2.2 hIu.2.2.2 (shiftedKernel_measurable W m)
    (adjacencyKernel_measurable W) (chargeKernel_measurable W) hsym hW.moment_mem
  let k := q + m * (if 0 < q then 1 else 0)
  have hy : ∀ᵐ p ∂μ.prod μ, p.1 ∈ {x | S.ρ x = r.val} → p.2 ∈ {x | S.ρ x = u.val} →
      chargeKernel W p.1 p.2 = k := by
    have h := hcross.mono (fun _ hp => hp.2.2)
    rw [Measure.prod_restrict] at h
    exact ((ae_restrict_iff' (hIr.1.prod hIu.1)).mp h).mono (fun _ hp hi hj => hp ⟨hi, hj⟩)
  have hmr := (R.classMass_eq_iff hW r).mpr hr
  have hmu := (R.classMass_eq_iff hW u).mpr hu
  rw [reverseClassMass, S.collapsedPartLabel_fiber] at hmr hmu
  have hνr : ν {x | S.ρ x = r.val} ≠ 0 := by
    intro hz
    change ν.real {x | S.ρ x = r.val} = R.height at hmr
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hmr
    linarith [R.height_pos]
  have hνu : ν {x | S.ρ x = u.val} ≠ 0 := by
    intro hz
    change ν.real {x | S.ρ x = u.val} = R.height at hmu
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hmu
    linarith [R.height_pos]
  have hcurrent := integral_cellLaw_prod_of_const ν _ _ hIr.1 hIu.1 hνr hνu
    (fun p => chargeKernel W p.1 p.2) k ((hν.prod hν).ae_le hy)
  have horiginal := integral_cellLaw_prod_of_const μ _ _ hIr.1 hIu.1 hIr.2.1.ne' hIu.2.1.ne'
    (fun p => chargeKernel W p.1 p.2) k hy
  rw [currentHeadPrice, MultipartiteHeadPrice.headPrice, MultipartiteHeadPrice.headPrice,
    S.collapsedPartLabel_fiber, S.collapsedPartLabel_fiber]
  exact hcurrent.trans horiginal.symm

/-- The actual original whole-head charge mean satisfies the reconstructed
head-price bound after its equality to the current-law mean is proved. -/
theorem original_head_price_lower_bound (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hcard : R.plateau.card = 2)
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (r u : S.I) (hru : r ≠ u) (hr : r ∈ R.plateau) (hu : u ∈ R.plateau) :
    -m + 2 * (2 * (c - m * d) + m) ≤ MultipartiteHeadPrice.headPrice W
      (S.collapsedPartLabel ⁻¹' {some r}) (S.collapsedPartLabel ⁻¹' {some u}) := by
  have h := R.current_head_price_lower_bound hW hd hgap hcard hintercept r u hru hr hu
  rwa [R.current_head_price_eq_original hW r u hr hu] at h

/-- An actual two-element plateau supplies its two distinct original
centers and the original-law head-price bound. -/
theorem exists_original_head_price_lower_bound (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hcard : R.plateau.card = 2)
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m) :
    ∃ r u : S.I, r ≠ u ∧ R.plateau = {r, u} ∧
      -m + 2 * (2 * (c - m * d) + m) ≤ MultipartiteHeadPrice.headPrice W
        (S.collapsedPartLabel ⁻¹' {some r}) (S.collapsedPartLabel ⁻¹' {some u}) := by
  obtain ⟨r, u, hru, hp⟩ := Finset.card_eq_two.mp hcard
  refine ⟨r, u, hru, hp, R.original_head_price_lower_bound hW hd hgap hcard hintercept r u hru ?_ ?_⟩
  · rw [hp]; exact Finset.mem_insert_self r {u}
  · rw [hp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self u)

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
