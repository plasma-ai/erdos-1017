module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairStrict

/-!
# Score comparison across a missing rectangle

For a saturated atom pair, a missing rectangle whose first side has larger
degree has strictly smaller saturated-head score on that side.
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

/-- A genuine missing rectangle with larger original degree on its first
side has strictly smaller saturated-head score on that side. The sets and
their original zero-block and degree hypotheses are explicit case data. -/
theorem IsSaturatedAtomPair.score_increases_across_missing_sets
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (H L : Set Ω) (hH : MeasurableSet H) (hL : MeasurableSet L)
    (hHpos : 0 < μ H) (hLpos : 0 < μ L)
    (hzero : ∀ᵐ p ∂(μ.restrict H).prod (μ.restrict L), shiftedKernel W m p.1 p.2 = 0)
    (hdegree : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 L hL⟫ <
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 H hH⟫) :
    ⟪r.val + u.val, KernelOperator.normalizedSetL2 H hH⟫ <
      ⟪r.val + u.val, KernelOperator.normalizedSetL2 L hL⟫ := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let nH : Lp ℝ 2 μ := KernelOperator.normalizedSetL2 H hH
  let nL : Lp ℝ 2 μ := KernelOperator.normalizedSetL2 L hL
  let f := nL - nH
  let h := S.saturatedDirection r u
  let U := ⟪g, h⟫
  let V := ⟪g, f⟫
  have hf : f ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem
      (KernelOperator.normalizedSetL2_bounded L hL) (KernelOperator.normalizedSetL2_bounded H hH)
  have hfm : (∫ x, f x ∂μ) = 0 := by
    rw [← KernelOperator.inner_constant_one]
    change ⟪Lp.const 2 μ (1 : ℝ), nL - nH⟫ = 0
    rw [inner_sub_right, KernelOperator.inner_constant_one, KernelOperator.inner_constant_one,
      KernelOperator.normalizedSetL2_integral L hL hLpos,
      KernelOperator.normalizedSetL2_integral H hH hHpos, sub_self]
  have hV : V < 0 := by
    change ⟪g, nL - nH⟫ < 0
    rw [inner_sub_right]
    exact sub_neg.mpr hdegree
  have hU : U < 0 := hpair.degree_inner_neg hW hd hgap hell
  have hsym : (shiftedOperator W m).toLinearMap.IsSymmetric :=
    KernelOperator.operator_symmetric (shiftedKernel W m) (by positivity)
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
      ((shiftedMoment_symm W m).mono (fun _ hx => hx.symm))
  have hdiag (T : Set Ω) (hT : MeasurableSet T) :
      0 ≤ ⟪shiftedOperator W m (KernelOperator.normalizedSetL2 T hT),
        KernelOperator.normalizedSetL2 T hT⟫ := by
    rw [show ⟪shiftedOperator W m (KernelOperator.normalizedSetL2 T hT),
      KernelOperator.normalizedSetL2 T hT⟫ = _ from
      KernelOperator.operator_inner_normalizedSetL2 (shiftedKernel W m) (by positivity)
        (shiftedKernel_measurable W m) (shiftedKernel_bound W m) T T hT hT]
    apply mul_nonneg (by positivity)
    apply integral_nonneg_of_ae
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
      Measure.restrict_le_self) hW.moment_mem] with p hp
    exact hp.1
  have hcross : ⟪shiftedOperator W m nL, nH⟫ = 0 :=
    KernelOperator.operator_inner_normalizedSetL2_eq_zero (shiftedKernel W m)
      (by positivity) (shiftedKernel_measurable W m) (shiftedKernel_bound W m) H L hH hL hzero
  have hcross' : ⟪shiftedOperator W m nH, nL⟫ = 0 :=
    (hsym nH nL).trans ((real_inner_comm _ _).trans hcross)
  have hef : 0 ≤ ⟪shiftedOperator W m f, f⟫ := by
    change 0 ≤ ⟪shiftedOperator W m (nL - nH), nL - nH⟫
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hcross, hcross']
    linarith [hdiag H hH, hdiag L hL]
  have heh : 0 < ⟪shiftedOperator W m h, h⟫ := hpair.shifted_energy_pos hW hd hgap hell
  have hB : 0 < ⟪shiftedOperator W m h, f⟫ := by
    by_contra hnot
    have hBnonpos := le_of_not_gt hnot
    let k := V • h - U • f
    have hk : k ∈ KernelOperator.boundedL2Submodule μ :=
      (KernelOperator.boundedL2Submodule μ).sub_mem
        ((KernelOperator.boundedL2Submodule μ).smul_mem V (S.saturatedDirection_bounded r u))
        ((KernelOperator.boundedL2Submodule μ).smul_mem U hf)
    have hkm : (∫ x, k x ∂μ) = 0 := by
      rw [← KernelOperator.inner_constant_one]
      change ⟪Lp.const 2 μ (1 : ℝ), V • h - U • f⟫ = 0
      rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
        KernelOperator.inner_constant_one, KernelOperator.inner_constant_one, hfm]
      change V * (∫ x, S.saturatedDirection r u x ∂μ) - U * 0 = 0
      rw [S.saturatedDirection_integral]
      ring
    have hkd : ⟪g, k⟫ = 0 := by
      change ⟪g, V • h - U • f⟫ = 0
      rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right]
      change V * U - U * V = 0
      ring
    have hn := hW.bounded_tangent_nonpositive (hW.strict_gap_structure hd hgap).regular
      k hk hkm hkd
    have hBsym : ⟪shiftedOperator W m f, h⟫ = ⟪shiftedOperator W m h, f⟫ :=
      (hsym f h).trans (real_inner_comm _ _)
    change ⟪shiftedOperator W m (V • h - U • f), V • h - U • f⟫ ≤ 0 at hn
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right] at hn
    rw [hBsym] at hn
    have hp : 0 < V ^ 2 * ⟪shiftedOperator W m h, h⟫ :=
      mul_pos (sq_pos_of_neg hV) heh
    have hq : 0 ≤ U ^ 2 * ⟪shiftedOperator W m f, f⟫ :=
      mul_nonneg (sq_nonneg _) hef
    have hc : 0 ≤ -(V * U * ⟪shiftedOperator W m h, f⟫) :=
      neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg_of_nonpos_of_nonpos hV.le hU.le) hBnonpos)
    nlinarith
  have hconst : ⟪Lp.const 2 μ (1 : ℝ), f⟫ = 0 := by
    rw [KernelOperator.inner_constant_one, hfm]
  rw [S.shiftedOperator_saturatedDirection r u hW, inner_sub_left,
    real_inner_smul_left, hconst, mul_zero, sub_zero] at hB
  change 0 < ⟪r.val + u.val, nL - nH⟫ at hB
  rw [inner_sub_right] at hB
  exact sub_pos.mp hB

end Erdos1017.CappedModel.SelectedHighLowStructure
