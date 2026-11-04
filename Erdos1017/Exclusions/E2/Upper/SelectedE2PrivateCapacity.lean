module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterHeadDegree
public import Erdos1017.Exclusions.Common.Flows.SourceRestrictedReverseFlow

/-!
# Partition capacity under the partial reverse direction

The two-head baseline and the partial reverse direction lie in the same original
degree cone with nonnegative shifted pairing, a retained original-law partition
pays its source deficit and weighted outside mass
(`weighted_partition_capacity`), and the original shifted deficit has no larger
integral under the partial reverse endpoint.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem inner_eq_integral_mul (f g : Lp ℝ 2 μ) :
    ⟪f, g⟫ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by simp only [RCLike.inner_apply, conj_trivial]; ring)

/-- The actual two-head baseline and the actual partial reverse direction
lie in the same original degree cone. Their original shifted pairing is
nonnegative, including the zero partial-flow case. -/
theorem retained_direction_head_pairing_nonnegative
    (r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hdegree0 : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) -
        Lp.const 2 μ (1 : ℝ)⟫ < 0) :
    0 ≤ KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
      (((1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) -
        Lp.const 2 μ (1 : ℝ) : Lp ℝ 2 μ) : Ω → ℝ)
      (MissingFlow.direction μ
        (MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau)ᶜ R.flow)) := by
  let a := S.normalizedHead r
  let b := S.normalizedHead u
  let e := Lp.const 2 μ (1 : ℝ)
  let f : Lp ℝ 2 μ := (1 / 2 : ℝ) • (a + b) - e
  let ν := 2 * (c - m * d)
  let B := schurForm W m
  let q := MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau)ᶜ R.flow
  let v := MissingFlow.direction μ q
  have hq : Integrable q (μ.prod μ) :=
    MissingFlow.integrable_sourceSlice R.isFullReverseFlow.integrable R.measurableSet_source.compl
  have hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p :=
    MissingFlow.nonnegative_sourceSlice R.isFullReverseFlow.nonnegative _
  have hv : Integrable v μ := MissingFlow.integrable_direction hq
  have hvm : (∫ x, v x ∂μ) = 0 := MissingFlow.integral_direction hq
  have hf : Integrable (f : Ω → ℝ) μ := (Lp.memLp f).integrable (by norm_num)
  have hfa : ⟪e, a⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral _ _ (S.hfibers r.val r.property).2.1
  have hfb : ⟪e, b⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral _ _ (S.hfibers u.val u.property).2.1
  have hee : ⟪e, e⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, KernelOperator.constant_one_norm]
    norm_num
  have hfm : (∫ x, f x ∂μ) = 0 := by
    rw [← KernelOperator.inner_constant_one]
    change ⟪e, f⟫ = 0
    simp only [f, inner_sub_right, real_inner_smul_right, inner_add_right, hfa, hfb, hee]
    ring
  have hκ : 2 * ν ≤ B a b :=
    R.headPairing_ge_two_stationary r u hru hW hd hgap hp hintercept
  have haa : B a a = 0 := S.schurForm_head_self r
  have hbb : B b b = 0 := S.schurForm_head_self u
  have hsym : ∀ x y, B x y = B y x := fun x y => schurForm_symm x y
  have haν : B e a = ν := S.schurForm_constant_head r hW
  have hbν : B e b = ν := S.schurForm_constant_head u hW
  have heν : B e e = ν := schurForm_constant_self hW
  have henergyF : 0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) f := by
    have heq : B f f = B a b / 2 - ν := by
      simp only [f, map_sub, map_add, map_smul, LinearMap.add_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [haa, hbb, hsym b a, haν, hbν, heν, hsym a e, hsym b e, haν, hbν]
      ring
    have hnonneg : 0 ≤ B f f := by rw [heq]; linarith
    rw [show B f f = KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) f from
      schurForm_eq_kernelPairing f f] at hnonneg
    exact hnonneg
  have henergyV : 0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) v :=
    R.isFullReverseFlow.sourceSlice_energy_nonnegative hW hd hgap R.measurableSet_source.compl
  by_cases hpos : 0 < ∫ p, q p ∂μ.prod μ
  · let g := adjacencyOperator W e
    have hgBound : g ∈ KernelOperator.boundedL2Submodule μ :=
      KernelOperator.operator_range_bounded _ _ _ _ _
    obtain ⟨Cg, _, hgBound⟩ := hgBound
    have hvdeg : (∫ x, g x * v x ∂μ) < 0 :=
      MissingFlow.degree_pairing_neg hq hq0 hpos g (Lp.memLp g).aestronglyMeasurable
        hgBound ((R.isFullReverseFlow.sourceSlice_oriented_support _).mono
          (fun _ hx hne => (hx hne).2))
    have hfdeg : (∫ x, g x * f x ∂μ) < 0 := by
      rw [← inner_eq_integral_mul]
      exact hdegree0
    exact (hW.integrable_degree_cone_reverse_cauchy hd hgap f v hf hv hfm hvm
      henergyF henergyV (mul_pos_of_neg_of_neg hfdeg hvdeg)).1
  · have hz : q =ᵐ[μ.prod μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hq0 hq).mp
        (le_antisymm (le_of_not_gt hpos) (integral_nonneg_of_ae hq0))
    have hvzero : v =ᵐ[μ] 0 := MissingFlow.direction_eq_zero_of_ae_zero hz
    have heq : KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m) f v = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hvzero] with p hp
      change shiftedKernel W m p.1 p.2 * f p.2 * v p.1 = 0
      rw [hp, Pi.zero_apply, mul_zero]
    rw [heq]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem kernelPairing_eq_integral_operator (f : Lp ℝ 2 μ)
    (v : Ω → ℝ) (hv : Integrable v μ) :
    KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m) f v =
      ∫ x, shiftedOperator W m f x * v x ∂μ := by
  have hf : Integrable (f : Ω → ℝ) μ := (Lp.memLp f).integrable (by norm_num)
  rw [KernelOperator.kernelPairing, integral_prod _
    (KernelOperator.integrable_kernel_bilinear (shiftedKernel_measurable W m)
      (shiftedKernel_bound W m) hf hv)]
  apply integral_congr_ae
  filter_upwards [KernelOperator.onL2_coe (shiftedKernel W m)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) f] with x hx
  rw [integral_mul_const]
  change KernelOperator.applyKernel (μ := μ) (shiftedKernel W m) f x * v x = _
  exact congrArg (fun z => z * v x) hx.symm

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem original_row_bounded (r : S.I) :
    r.val ∈ KernelOperator.boundedL2Submodule μ := by
  rw [← S.operator_normalizedHead r]
  exact KernelOperator.operator_range_bounded _ _ _ _ _

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integrable_row_mul (r : S.I) (v : Ω → ℝ) (hv : Integrable v μ) :
    Integrable (fun x => r.val x * v x) μ := by
  obtain ⟨B, _, hB⟩ := original_row_bounded (S := S) r
  exact KernelOperator.integrable_bounded_mul (Lp.memLp r.val).aestronglyMeasurable hB hv

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A retained original-law partition pays its source deficit and weighted
outside mass, with all measure and integrability premises explicit. -/
theorem weighted_partition_capacity
    (H C O : Set Ω) (hH : MeasurableSet H) (hC : MeasurableSet C)
    (f w : Ω → ℝ) (ζ : ℝ) (hf : Integrable f μ) (hw : Integrable w μ)
    (hfw : Integrable (fun x => f x * w x) μ)
    (hwn : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hwmean : (∫ x, w x ∂μ) = 1)
    (hHC : ∀ᵐ x ∂μ, x ∈ C → x ∉ H)
    (hheads : ∀ᵐ x ∂μ, x ∈ H → f x = 0 ∧ w x = 1)
    (hsource : ∀ᵐ x ∂μ, x ∈ C → w x = 1)
    (hother : ∀ᵐ x ∂μ, x ∈ O → ζ ≤ f x)
    (hoff : ∀ᵐ x ∂μ, x ∉ H ∪ C ∪ O → w x = 0) :
    (∫ x in C, f x ∂μ) + ζ * (1 - (μ.real H + μ.real C)) ≤
      ∫ x, f x * w x ∂μ := by
  classical
  have hiH : Integrable (H.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hH
  have hiC : Integrable (C.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hC
  have hwsub := (hw.sub hiH).sub hiC
  have hpoint : ∀ᵐ x ∂μ,
      C.indicator f x + ζ * (w x - H.indicator (fun _ => (1 : ℝ)) x -
        C.indicator (fun _ => (1 : ℝ)) x) ≤ f x * w x := by
    filter_upwards [hwn, hHC, hheads, hsource, hother, hoff]
      with x hn hd hh hc ho hz
    by_cases hxC : x ∈ C
    · have hxH : x ∉ H := hd hxC
      simp only [indicator_of_mem hxC, indicator_of_notMem hxH, hc hxC,
        sub_zero, sub_self, mul_zero, add_zero, mul_one, le_refl]
    · by_cases hxH : x ∈ H
      · obtain ⟨hfzero, hwone⟩ := hh hxH
        simp only [indicator_of_notMem hxC, indicator_of_mem hxH, hfzero,
          hwone, sub_self, mul_zero, zero_mul, zero_add, le_refl]
      · by_cases hxO : x ∈ O
        · simpa only [indicator_of_notMem hxC, indicator_of_notMem hxH,
            sub_zero, zero_add] using mul_le_mul_of_nonneg_right (ho hxO) hn
        · have hnot : x ∉ H ∪ C ∪ O := by
            simpa only [mem_union, not_or] using (And.intro (And.intro hxH hxC) hxO)
          have hzero : w x = 0 := hz hnot
          simp only [indicator_of_notMem hxC, indicator_of_notMem hxH,
            hzero, sub_zero, mul_zero, zero_add, le_refl]
  have hbound := integral_mono_ae ((hf.indicator hC).add (hwsub.const_mul ζ)) hfw hpoint
  rw [integral_add' (hf.indicator hC) (hwsub.const_mul ζ), integral_const_mul,
    integral_sub' (hw.sub hiH) hiC, integral_sub' hw hiH,
    integral_indicator hC, integral_indicator_const (1 : ℝ) hH,
    integral_indicator_const (1 : ℝ) hC, hwmean] at hbound
  simp only [smul_eq_mul, mul_one] at hbound
  convert hbound using 1
  ring

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Original homogeneous head deficits remain integrable against every
integrable original-law weight. -/
theorem integrable_head_deficit_mul (r u : S.I) (κ : ℝ)
    (w : Ω → ℝ) (hw : Integrable w μ) :
    Integrable (fun x => (κ - r.val x - u.val x) * w x) μ := by
  have hi := ((hw.const_mul κ).sub (integrable_row_mul r w hw)).sub
    (integrable_row_mul u w hw)
  apply hi.congr
  exact Eventually.of_forall (fun _ => by simp only [Pi.sub_apply]; ring)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem original_row_integral (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    (∫ x, r.val x ∂μ) = 2 * (c - m * d) := by
  have h := S.schurForm_constant_head r hW
  rw [schurForm_symm] at h
  change ⟪shiftedOperator W m (S.normalizedHead r), Lp.const 2 μ (1 : ℝ)⟫ = _ at h
  rwa [S.operator_normalizedHead r, real_inner_comm, KernelOperator.inner_constant_one] at h

/-- The old shifted deficit has no larger integral under the actual
partial reverse endpoint. The cone comparison is evaluated under the
original measure and preserves the signed old head-row corrections. -/
theorem retained_deficit_integral_le_original
    (r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hdegree0 : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) -
        Lp.const 2 μ (1 : ℝ)⟫ < 0) :
    (∫ x, (S.headPairing r u - r.val x - u.val x) * R.retainedWeight x ∂μ) ≤
      S.headPairing r u - 2 * (2 * (c - m * d)) := by
  let e := Lp.const 2 μ (1 : ℝ)
  let f₀ : Lp ℝ 2 μ := (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) - e
  let ν := 2 * (c - m * d)
  let κ := S.headPairing r u
  let q := MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau)ᶜ R.flow
  let v := MissingFlow.direction μ q
  let f : Ω → ℝ := fun x => κ - r.val x - u.val x
  have hq : Integrable q (μ.prod μ) :=
    MissingFlow.integrable_sourceSlice R.isFullReverseFlow.integrable R.measurableSet_source.compl
  have hv : Integrable v μ := MissingFlow.integrable_direction hq
  have hvm : (∫ x, v x ∂μ) = 0 := MissingFlow.integral_direction hq
  have hstationary := KernelOperator.constant_one_eigenvector_of_stationary
    (shiftedKernel W m) (by positivity) (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) _ hW.stationary
  change shiftedOperator W m e = ν • e at hstationary
  have hop : shiftedOperator W m f₀ = (1 / 2 : ℝ) • (r.val + u.val) - ν • e := by
    rw [show f₀ = (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) - e from rfl,
      map_sub, map_smul, map_add, S.operator_normalizedHead r,
      S.operator_normalizedHead u, hstationary]
  have hcoe : (shiftedOperator W m f₀ : Ω → ℝ) =ᵐ[μ]
      fun x => (r.val x + u.val x) / 2 - ν := by
    rw [hop]
    filter_upwards [Lp.coeFn_sub ((1 / 2 : ℝ) • (r.val + u.val)) (ν • e),
      Lp.coeFn_smul (1 / 2 : ℝ) (r.val + u.val), Lp.coeFn_add r.val u.val,
      Lp.coeFn_smul ν e, Lp.coeFn_const 2 μ (1 : ℝ)] with x ha hb hc hd he
    change e x = 1 at he
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at ha hb hc hd
    rw [ha, hb, hc, hd, he]
    ring
  have hpair := R.retained_direction_head_pairing_nonnegative
    r u hru hW hd hgap hp hintercept hdegree0
  change 0 ≤ KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m) f₀ v at hpair
  have hpairInt := kernelPairing_eq_integral_operator (W := W) (m := m) f₀ v hv
  obtain ⟨B, _, hB⟩ := (show shiftedOperator W m f₀ ∈
      KernelOperator.boundedL2Submodule μ from KernelOperator.operator_range_bounded _ _ _ _ _)
  have hopv : Integrable (fun x => shiftedOperator W m f₀ x * v x) μ :=
    KernelOperator.integrable_bounded_mul (Lp.memLp _).aestronglyMeasurable hB hv
  have hf : Integrable f μ :=
    ((integrable_const κ).sub ((Lp.memLp r.val).integrable (by norm_num))).sub
      ((Lp.memLp u.val).integrable (by norm_num))
  have hfv : Integrable (fun x => f x * v x) μ := integrable_head_deficit_mul r u κ v hv
  have hfv_eq : (∫ x, f x * v x ∂μ) =
      -2 * KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m) f₀ v := by
    have heq : (fun x => f x * v x) =ᵐ[μ]
        fun x => (κ - 2 * ν) * v x - 2 * (shiftedOperator W m f₀ x * v x) := by
      filter_upwards [hcoe] with x hx
      dsimp only [f]
      rw [hx]
      ring
    rw [integral_congr_ae heq,
      integral_sub (hv.const_mul (κ - 2 * ν)) (hopv.const_mul 2),
      integral_const_mul, integral_const_mul, hvm, mul_zero, zero_sub, ← hpairInt]
    ring
  have hweight : R.retainedWeight = fun x => 1 + v x := by
    funext x
    dsimp only [retainedWeight, integrableTiltWeight, v, q]
    ring
  have hweighted : (∫ x, f x * R.retainedWeight x ∂μ) =
      (∫ x, f x ∂μ) + (∫ x, f x * v x ∂μ) := by
    rw [hweight]
    have heq : (fun x => f x * (1 + v x)) = fun x => f x + f x * v x := by
      funext x
      ring
    rw [heq, integral_add hf hfv]
  have htotal : (∫ x, f x ∂μ) = κ - 2 * ν := by
    have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
    have hu : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
    have hfirst := integral_sub ((integrable_const κ).sub hr) hu
    have hsecond := integral_sub (integrable_const κ) hr
    simp only [Pi.sub_apply] at hfirst hsecond
    change (∫ x, κ - r.val x - u.val x ∂μ) = _
    rw [hfirst, hsecond, integral_const, probReal_univ, one_smul,
      original_row_integral r hW, original_row_integral u hW]
    ring
  change (∫ x, f x * R.retainedWeight x ∂μ) ≤ κ - 2 * ν
  rw [hweighted, htotal, hfv_eq]
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
