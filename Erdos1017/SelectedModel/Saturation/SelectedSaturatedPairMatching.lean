module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairStrict
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairIncidence

/-!
# Matching of saturated pairs

Two saturated pairs sharing one head have the same other head, by a
degree-neutral tangent built from their degree variations, so any two saturated
pairs are the same unordered pair or have disjoint heads.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

omit [IsProbabilityMeasure μ] in
private theorem inner_eq_integral_mul (f g : Lp ℝ 2 μ) :
    ⟪f, g⟫ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by simp only [RCLike.inner_apply, conj_trivial]; ring)

private theorem normalized_atom_inner_one (S : SelectedHighLowStructure W m) (r : S.I) :
    ⟪Lp.const 2 μ (1 : ℝ), KernelOperator.normalizedSetL2 {x | S.ρ x = r.val}
      (S.hfibers r.val r.property).1⟫ = 1 := by
  rw [KernelOperator.inner_constant_one]
  exact KernelOperator.normalizedSetL2_integral _ _ (S.hfibers r.val r.property).2.1

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

private theorem shared_head_mixed_energy
    {S : SelectedHighLowStructure W m} {r u v : S.I}
    (hru : S.IsSaturatedAtomPair r u) (huv : S.IsSaturatedAtomPair u v)
    (hrv : r ≠ v) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    ⟪shiftedOperator W m (S.saturatedDirection r u), S.saturatedDirection u v⟫ =
      2 * (1 - m - 2 * (2 * (c - m * d))) := by
  have houter := hru.outer_block_zero huv hrv hW hd hgap hell
  let n (k : S.I) : Lp ℝ 2 μ := KernelOperator.normalizedSetL2 {x | S.ρ x = k.val}
    (S.hfibers k.val k.property).1
  have hru' : ⟪r.val, n u⟫ = 1 - m := by
    rw [real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers u.val u.property).2.1 r.val (1 - m) hru.row_on_other
  have hrv' : ⟪r.val, n v⟫ = 0 := by
    rw [real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers v.val v.property).2.1 r.val 0 houter.1
  have huu : ⟪u.val, n u⟫ = 0 := by
    rw [real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers u.val u.property).2.1 u.val 0 (S.root_row_zero_on_fiber u)
  have huv' : ⟪u.val, n v⟫ = 1 - m := by
    rw [real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers v.val v.property).2.1 u.val (1 - m) huv.row_on_other
  have hro : ⟪r.val, Lp.const 2 μ (1 : ℝ)⟫ = 2 * (c - m * d) := by
    rw [real_inner_comm, KernelOperator.inner_constant_one]
    exact S.row_integral_of_stationary r hW
  have huo : ⟪u.val, Lp.const 2 μ (1 : ℝ)⟫ = 2 * (c - m * d) := by
    rw [real_inner_comm, KernelOperator.inner_constant_one]
    exact S.row_integral_of_stationary u hW
  have hoo : ⟪Lp.const 2 μ (1 : ℝ), Lp.const 2 μ (1 : ℝ)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, KernelOperator.constant_one_norm]
    norm_num
  have honu : ⟪Lp.const 2 μ (1 : ℝ), n u⟫ = 1 := S.normalized_atom_inner_one u
  have honv : ⟪Lp.const 2 μ (1 : ℝ), n v⟫ = 1 := S.normalized_atom_inner_one v
  rw [S.shiftedOperator_saturatedDirection r u hW, saturatedDirection]
  change ⟪r.val + u.val - (2 * (2 * (c - m * d))) • Lp.const 2 μ (1 : ℝ),
    n u + n v - (2 : ℝ) • Lp.const 2 μ (1 : ℝ)⟫ = _
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hru', hrv', huu, huv', hro, huo,
    hoo, honu, honv]
  ring

/-- Two actual saturated pairs sharing one head have the same other head.
The degree-neutral tangent is built from their actual degree variations. -/
theorem IsSaturatedAtomPair.other_head_eq
    {S : SelectedHighLowStructure W m} {r u v : S.I}
    (hru : S.IsSaturatedAtomPair r u) (huv : S.IsSaturatedAtomPair u v)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    r = v := by
  by_contra hrv
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let h₁ := S.saturatedDirection r u
  let h₂ := S.saturatedDirection u v
  let U₁ := ⟪g, h₁⟫
  let U₂ := ⟪g, h₂⟫
  let f := U₂ • h₁ - U₁ • h₂
  have hf : f ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem
      ((KernelOperator.boundedL2Submodule μ).smul_mem U₂ (S.saturatedDirection_bounded r u))
      ((KernelOperator.boundedL2Submodule μ).smul_mem U₁ (S.saturatedDirection_bounded u v))
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
  have hcross := shared_head_mixed_energy hru huv hrv hW hd hgap hell
  have hcross' : ⟪shiftedOperator W m h₂, h₁⟫ =
      2 * (1 - m - 2 * (2 * (c - m * d))) := by
    exact (hsym h₂ h₁).trans ((real_inner_comm _ _).trans hcross)
  change ⟪shiftedOperator W m (U₂ • h₁ - U₁ • h₂), U₂ • h₁ - U₁ • h₂⟫ ≤ 0 at hn
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right] at hn
  have he₁ := hru.shifted_energy hW
  have he₂ := huv.shifted_energy hW
  change ⟪shiftedOperator W m h₁, h₁⟫ = _ at he₁
  change ⟪shiftedOperator W m h₂, h₂⟫ = _ at he₂
  rw [he₁, he₂, hcross, hcross'] at hn
  have hDelta := hru.gap_pos hW hd hgap hell
  have hU : U₁ = U₂ := by
    have hsq : (U₁ - U₂) ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg (U₁ - U₂)]
    nlinarith [sq_nonneg (U₁ - U₂)]
  have hfirst := hru.adjacency_first_variation hW
  have hsecond := huv.adjacency_first_variation hW
  rw [← inner_eq_integral_mul] at hfirst hsecond
  change U₁ = _ at hfirst
  change U₂ = _ at hsecond
  have heq : wholeRowDegree r.val = wholeRowDegree v.val := by linarith
  have hIr := S.hfibers r.val r.property
  have hIv := S.hfibers v.val v.property
  have hrows := hru.outer_block_zero huv hrv hW hd hgap hell
  have hfalse : ∀ᵐ p ∂(μ.restrict {x | S.ρ x = r.val}).prod
      (μ.restrict {x | S.ρ x = v.val}), False := by
    filter_upwards [hrows.2.2,
      ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) S.hdegreeNe,
      Measure.quasiMeasurePreserving_fst.ae
        (wholeRowFiber_degree W m S.ρ r.val hIr.2.2.2),
      Measure.quasiMeasurePreserving_snd.ae
        (wholeRowFiber_degree W m S.ρ v.val hIv.2.2.2),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hIr.1),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hIv.1)] with p hz hn hgr hgv hr hv
    have hrel : p ∈ actualZeroRelation W m S.ρ := by
      exact ⟨hz.1, by simpa only [hr, hv] using (Subtype.coe_ne_coe.mpr hrv)⟩
    exact (hn hrel) (hgr.trans (heq.trans hgv.symm))
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hIr.2.1.ne'
    (Measure.ae_ae_of_ae_prod hfalse)
  obtain ⟨y, _, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hIv.2.1.ne' hx
  exact hy

/-- Any two actual saturated pairs are the same unordered pair or have
disjoint original heads. -/
theorem IsSaturatedAtomPair.eq_or_disjoint
    {S : SelectedHighLowStructure W m} {r u v w : S.I}
    (hru : S.IsSaturatedAtomPair r u) (hvw : S.IsSaturatedAtomPair v w)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    (r = v ∧ u = w) ∨ (r = w ∧ u = v) ∨ (r ≠ v ∧ r ≠ w ∧ u ≠ v ∧ u ≠ w) := by
  by_cases hrv : r = v
  · subst v
    exact Or.inl ⟨rfl, hru.symm.other_head_eq hvw hW hd hgap hell⟩
  by_cases hrw : r = w
  · subst w
    exact Or.inr (Or.inl ⟨rfl, hru.symm.other_head_eq hvw.symm hW hd hgap hell⟩)
  by_cases huv : u = v
  · subst v
    exact False.elim (hrw (hru.other_head_eq hvw hW hd hgap hell))
  by_cases huw : u = w
  · subst w
    exact False.elim (hrv (hru.other_head_eq hvw.symm hW hd hgap hell))
  exact Or.inr (Or.inr ⟨hrv, hrw, huv, huw⟩)

end Erdos1017.CappedModel.SelectedHighLowStructure
