module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairMatching
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedPairStrictScore
public import Erdos1017.SelectedModel.Structure.DegreeSetAverages

/-!
# Uniqueness of the saturated pair

The same original strict-gap model has at most one unordered saturated pair, by
comparing negative degree variations (`IsSaturatedAtomPair.unique`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

private theorem outside_heads_mixed_energy_lt
    {S : SelectedHighLowStructure W m} {r u v w : S.I}
    (hru : S.IsSaturatedAtomPair r u)
    (hrv : r ≠ v) (hrw : r ≠ w) (huv : u ≠ v) (huw : u ≠ w)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    ⟪shiftedOperator W m (S.saturatedDirection r u), S.saturatedDirection v w⟫ <
      2 * (1 - m - 2 * (2 * (c - m * d))) := by
  have hnorv : ¬S.IsSaturatedAtomPair r v :=
    fun h => huv (hru.symm.other_head_eq h hW hd hgap hell)
  have hnorw : ¬S.IsSaturatedAtomPair r w :=
    fun h => huw (hru.symm.other_head_eq h hW hd hgap hell)
  have hnouv : ¬S.IsSaturatedAtomPair u v :=
    fun h => hrv (hru.other_head_eq h hW hd hgap hell)
  have hnouw : ¬S.IsSaturatedAtomPair u w :=
    fun h => hrw (hru.other_head_eq h hW hd hgap hell)
  let n (k : S.I) : Lp ℝ 2 μ := KernelOperator.normalizedSetL2 {x | S.ρ x = k.val}
    (S.hfibers k.val k.property).1
  have hscore (k : S.I) (hrk : r ≠ k) (huk : u ≠ k)
      (hnork : ¬S.IsSaturatedAtomPair r k) (hnouk : ¬S.IsSaturatedAtomPair u k) :
      ⟪r.val + u.val, n k⟫ < 1 - m := by
    apply KernelOperator.normalizedSetL2_inner_lt_of_ae_lt _ _
      (S.hfibers k.val k.property).2.1
    filter_upwards [hru.score_lt_on_other_atom k hrk huk hnork hnouk hW hd hgap hell,
      ae_restrict_of_ae (Lp.coeFn_add r.val u.val)] with x hx ha
    simpa only [ha, Pi.add_apply] using hx
  have hscorev := hscore v hrv huv hnorv hnouv
  have hscorew := hscore w hrw huw hnorw hnouw
  have hrowo : ⟪r.val + u.val, Lp.const 2 μ (1 : ℝ)⟫ = 2 * (2 * (c - m * d)) := by
    rw [real_inner_comm, KernelOperator.inner_constant_one]
    have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
    have hu : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
    rw [integral_congr_ae (Lp.coeFn_add r.val u.val)]
    simp only [Pi.add_apply]
    rw [integral_add hr hu,
      S.row_integral_of_stationary r hW, S.row_integral_of_stationary u hW]
    ring
  have hon (k : S.I) : ⟪Lp.const 2 μ (1 : ℝ), n k⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral _ _ (S.hfibers k.val k.property).2.1
  have hoo : ⟪Lp.const 2 μ (1 : ℝ), Lp.const 2 μ (1 : ℝ)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, KernelOperator.constant_one_norm]
    norm_num
  rw [S.shiftedOperator_saturatedDirection r u hW, saturatedDirection]
  change ⟪r.val + u.val - (2 * (2 * (c - m * d))) • Lp.const 2 μ (1 : ℝ),
    n v + n w - (2 : ℝ) • Lp.const 2 μ (1 : ℝ)⟫ < _
  simp only [inner_sub_left, inner_sub_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hrowo, hon, hoo]
  linarith

/-- The same original strict-gap model has at most one unordered saturated
pair. The comparison uses its actual negative degree variations. -/
theorem IsSaturatedAtomPair.unique
    {S : SelectedHighLowStructure W m} {r u v w : S.I}
    (hru : S.IsSaturatedAtomPair r u) (hvw : S.IsSaturatedAtomPair v w)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    (r = v ∧ u = w) ∨ (r = w ∧ u = v) := by
  rcases hru.eq_or_disjoint hvw hW hd hgap hell with heq | heq | ⟨hrv, hrw, huv, huw⟩
  · exact Or.inl heq
  · exact Or.inr heq
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let h₁ := S.saturatedDirection r u
  let h₂ := S.saturatedDirection v w
  let U₁ := ⟪g, h₁⟫
  let U₂ := ⟪g, h₂⟫
  let f := U₂ • h₁ - U₁ • h₂
  have hf : f ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem
      ((KernelOperator.boundedL2Submodule μ).smul_mem U₂ (S.saturatedDirection_bounded r u))
      ((KernelOperator.boundedL2Submodule μ).smul_mem U₁ (S.saturatedDirection_bounded v w))
  have hmean : (∫ x, f x ∂μ) = 0 := by
    rw [← KernelOperator.inner_constant_one]
    change ⟪Lp.const 2 μ (1 : ℝ), U₂ • h₁ - U₁ • h₂⟫ = 0
    simp only [inner_sub_right, real_inner_smul_right, KernelOperator.inner_constant_one,
      S.saturatedDirection_integral, h₁, h₂, mul_zero, sub_self]
  have hdegree : ⟪g, f⟫ = 0 := by
    change ⟪g, U₂ • h₁ - U₁ • h₂⟫ = 0
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right]
    change U₂ * U₁ - U₁ * U₂ = 0
    ring
  have hn := hW.bounded_tangent_nonpositive (hW.strict_gap_structure hd hgap).regular
    f hf hmean hdegree
  have hsym : (shiftedOperator W m).toLinearMap.IsSymmetric :=
    KernelOperator.operator_symmetric (shiftedKernel W m) (by positivity)
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
      ((shiftedMoment_symm W m).mono (fun _ hx => hx.symm))
  have hcross := outside_heads_mixed_energy_lt hru hrv hrw huv huw hW hd hgap hell
  have hcrosssym : ⟪shiftedOperator W m h₂, h₁⟫ = ⟪shiftedOperator W m h₁, h₂⟫ :=
    (hsym h₂ h₁).trans (real_inner_comm _ _)
  have he₁ := hru.shifted_energy hW
  have he₂ := hvw.shifted_energy hW
  change ⟪shiftedOperator W m h₁, h₁⟫ = _ at he₁
  change ⟪shiftedOperator W m h₂, h₂⟫ = _ at he₂
  have hU₁ : U₁ < 0 := hru.degree_inner_neg hW hd hgap hell
  have hU₂ : U₂ < 0 := hvw.degree_inner_neg hW hd hgap hell
  have hDelta := hru.gap_pos hW hd hgap hell
  have hprod : 0 < U₁ * U₂ := mul_pos_of_neg_of_neg hU₁ hU₂
  have hpositive : 0 < (U₁ * U₂) *
      (2 * (1 - m - 2 * (2 * (c - m * d))) - ⟪shiftedOperator W m h₁, h₂⟫) :=
    mul_pos hprod (sub_pos.mpr hcross)
  change ⟪shiftedOperator W m (U₂ • h₁ - U₁ • h₂), U₂ • h₁ - U₁ • h₂⟫ ≤ 0 at hn
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right] at hn
  rw [he₁, he₂, hcrosssym] at hn
  have hsquare : 0 ≤ (1 - m - 2 * (2 * (c - m * d))) * (U₁ - U₂) ^ 2 :=
    mul_nonneg hDelta.le (sq_nonneg _)
  exact False.elim (by nlinarith)

end Erdos1017.CappedModel.SelectedHighLowStructure
