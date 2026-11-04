module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSchurEnergy
public import Erdos1017.Exclusions.Common.SelectedReverseSingletonGeometry
public import Erdos1017.SelectedModel.Structure.DegreeSetAverages
public import Erdos1017.SelectedModel.Structure.DegreeStraddle

/-!
# Private-source deficits of a two-center recovery

The stationary tangent excludes a positive private-source excess against the
other head, with the private degree sign and the Gram entries derived, and the
opposite-head row leaves a nonnegative shifted deficit almost everywhere on the
private source.
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

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Every positive measurable part of a private source has strictly larger
original average degree than the head it misses. The order comes from the
actual selected zero relation. -/
private theorem private_degree_gt_head (r u : S.I) (hr : r ∈ R.plateau)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < μ C)
    (hCprivate : C ⊆ S.twoCenterPrivate r u) :
    wholeRowDegree r.val < ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      KernelOperator.normalizedSetL2 C hC⟫ := by
  let I := {x | S.ρ x = r.val}
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hI := (S.hfibers r.val r.property).1
  have hIpos := (S.hfibers r.val r.property).2.1
  have hCmiss : C ⊆ KernelOperator.wholeFiberMissingSet S.ρ r.val :=
    fun x hx => (hCprivate hx).1.2
  have hzero := KernelOperator.ae_zero_fiber_prod_missingSet (shiftedKernel W m)
    S.ρ S.hρ r.val ((S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.1))
    (shiftedKernel_measurable W m) (hW.moment_mem.mono (fun _ hp => hp.1))
  have hzeroC : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict C),
      shiftedKernel W m p.1 p.2 = 0 :=
    ae_mono (Measure.prod_mono le_rfl (Measure.restrict_mono hCmiss le_rfl)) hzero
  have hdegreeI := wholeRowFiber_degree W m S.ρ r.val
    (S.hfibers r.val r.property).2.2.2
  have hhighiff := ae_fiber_high_iff (S := S)
  have hcover := S.hcoverage
  have hrelation := S.hrelation
  have hgood : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict C),
      wholeRowDegree r.val < g p.2 := by
    filter_upwards [hzeroC,
      ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) hcover,
      ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) hrelation,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hC),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae hhighiff),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae hhighiff),
      Measure.quasiMeasurePreserving_fst.ae hdegreeI]
      with p hz hc hrel hx hy hfirst hsecond hdegree
    have hrx : S.ρ p.1 = r.val := hx
    have hhigh : p.2 ∈ S.H := (hCprivate hy).1.1.1
    have hyne : S.ρ p.2 ≠ r.val := by
      intro hρ
      exact ((hsecond r hρ).mp hhigh) (R.plateau_eligible r hr)
    have hactual : p ∈ actualZeroRelation W m S.ρ := by
      rcases hc hz with hsame | hactual
      · obtain ⟨v, _, hvx, hvy⟩ := hsame
        have hvr : v = r.val := hvx.symm.trans hrx
        exact False.elim (hyne (hvy.trans hvr))
      · exact hactual
    rcases hrel hactual with h | h
    · exact False.elim (((hfirst r hrx).mp h.1) (R.plateau_eligible r hr))
    · exact hdegree ▸ h.2.2
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hIpos.ne'
    (Measure.ae_ae_of_ae_prod hgood)
  exact KernelOperator.normalizedSetL2_inner_gt_of_ae_gt C hC hCpos g _ hx

/-- The original stationary tangent excludes a positive private-source excess
against its other head. The private degree sign and every Gram entry are
derived from the actual selected model. -/
theorem private_cross_le_headPairing (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hdegree0 : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) -
        Lp.const 2 μ (1 : ℝ)⟫ < 0)
    (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < μ C)
    (hCprivate : C ⊆ S.twoCenterPrivate r u) :
    schurForm W m (S.normalizedHead u) (KernelOperator.normalizedSetL2 C hC) ≤
      S.headPairing r u := by
  let a := S.normalizedHead r
  let b := S.normalizedHead u
  let z := KernelOperator.normalizedSetL2 (μ := μ) C hC
  let e := Lp.const 2 μ (1 : ℝ)
  let g := adjacencyOperator W e
  let B := schurForm W m
  let ν := 2 * (c - m * d)
  let f₀ := (1 / 2 : ℝ) • (a + b) - e
  let fC := z - a
  have hr : r ∈ R.plateau := by rw [hp]; simp
  have hdegreeHead : ⟪g, a⟫ = wholeRowDegree r.val := by
    change ⟪g, KernelOperator.normalizedSetL2 _ _⟫ = _
    exact KernelOperator.normalizedSetL2_inner_eq_of_ae_eq _ _
      (S.hfibers r.val r.property).2.1 g _
      (wholeRowFiber_degree W m S.ρ r.val (S.hfibers r.val r.property).2.2.2)
  have hdegreeC : 0 < ⟪g, fC⟫ := by
    change 0 < ⟪g, z - a⟫
    rw [inner_sub_right, hdegreeHead]
    exact sub_pos.mpr (R.private_degree_gt_head r u hr hW C hC hCpos hCprivate)
  have hκ : 2 * ν ≤ B a b := by
    change 2 * (2 * (c - m * d)) ≤ S.headPairing r u
    exact R.headPairing_ge_two_stationary r u hru hW hd hgap hp hintercept
  have haa : B a a = 0 := S.schurForm_head_self r
  have hbb : B b b = 0 := S.schurForm_head_self u
  have hab : B a b = S.headPairing r u := rfl
  have hsym : ∀ x y, B x y = B y x := fun x y => schurForm_symm x y
  have haν : B e a = ν := by
    change schurForm W m (Lp.const 2 μ (1 : ℝ)) (S.normalizedHead r) = _
    exact S.schurForm_constant_head r hW
  have hbν : B e b = ν := by
    change schurForm W m (Lp.const 2 μ (1 : ℝ)) (S.normalizedHead u) = _
    exact S.schurForm_constant_head u hW
  have heν : B e e = ν := schurForm_constant_self hW
  have hzν : B e z = ν := by
    rw [schurForm_constant hW, KernelOperator.normalizedSetL2_integral C hC hCpos]
    ring
  have haz : B a z = 0 := by
    change B a ((μ.real C)⁻¹ • indicatorVector C hC) = 0
    rw [map_smul, smul_eq_mul,
      S.schurForm_head_indicator_zero_of_missing r C hC
        (fun x hx => (hCprivate hx).1.2) hW, mul_zero]
  have hzz : 0 ≤ B z z := by
    have hdiag := schurForm_indicator_nonnegative (W := W) (m := m) C hC hW
    have hmass : 0 ≤ (μ.real C)⁻¹ := inv_nonneg.mpr measureReal_nonneg
    change 0 ≤ B ((μ.real C)⁻¹ • indicatorVector C hC)
      ((μ.real C)⁻¹ • indicatorVector C hC)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hmass (mul_nonneg hmass hdiag)
  have h0 : 0 ≤ B f₀ f₀ := by
    have hba : B b a = B a b := hsym b a
    have heq : B f₀ f₀ = (B a b) / 2 - ν := by
      simp only [f₀, map_sub, map_add, map_smul, LinearMap.add_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [haa, hbb, hba, haν, hbν, heν, hsym a e, hsym b e, haν, hbν]
      ring
    rw [heq]
    linarith
  have hCquad : 0 ≤ B fC fC := by
    have hza : B z a = 0 := (hsym z a).trans haz
    have heq : B fC fC = B z z := by
      simp only [fC, map_sub, LinearMap.sub_apply]
      rw [haz, hza, haa]
      ring
    rw [heq]
    exact hzz
  have hcross : B f₀ fC = (B b z - B a b) / 2 := by
    simp only [f₀, fC, map_sub, map_add, map_smul, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [haz, haa, hsym b a, haν, hzν]
    ring
  have hmeanA : (∫ x, a x ∂μ) = 1 :=
    KernelOperator.normalizedSetL2_integral _ _ (S.hfibers r.val r.property).2.1
  have hmeanB : (∫ x, b x ∂μ) = 1 :=
    KernelOperator.normalizedSetL2_integral _ _ (S.hfibers u.val u.property).2.1
  have hmeanZ : (∫ x, z x ∂μ) = 1 :=
    KernelOperator.normalizedSetL2_integral C hC hCpos
  have heA : ⟪e, a⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact hmeanA
  have heB : ⟪e, b⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact hmeanB
  have heZ : ⟪e, z⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact hmeanZ
  have hee : ⟪e, e⟫ = 1 := by
    change ⟪Lp.const 2 μ (1 : ℝ), Lp.const 2 μ (1 : ℝ)⟫ = 1
    rw [real_inner_self_eq_norm_sq, KernelOperator.constant_one_norm]
    norm_num
  have hmean0 : (∫ x, f₀ x ∂μ) = 0 := by
    rw [← KernelOperator.inner_constant_one]
    change ⟪e, f₀⟫ = 0
    simp only [f₀, inner_sub_right, real_inner_smul_right, inner_add_right,
      heA, heB, hee]
    ring
  have hmeanC : (∫ x, fC x ∂μ) = 0 := by
    rw [← KernelOperator.inner_constant_one]
    change ⟪e, fC⟫ = 0
    simp only [fC, inner_sub_right, heZ, heA]
    ring
  have hbounded0 : f₀ ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem
      ((KernelOperator.boundedL2Submodule μ).smul_mem (1 / 2 : ℝ)
        ((KernelOperator.boundedL2Submodule μ).add_mem
          (KernelOperator.normalizedSetL2_bounded _ _)
          (KernelOperator.normalizedSetL2_bounded _ _)))
      Variation.constant_one_bounded
  have hboundedC : fC ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem
      (KernelOperator.normalizedSetL2_bounded C hC)
      (KernelOperator.normalizedSetL2_bounded _ _)
  let t := ⟪g, fC⟫ / (-⟪g, f₀⟫)
  have hdegree0' : ⟪g, f₀⟫ < 0 := hdegree0
  have ht : 0 < t := div_pos hdegreeC (neg_pos.mpr hdegree0')
  have htd : t * ⟪g, f₀⟫ = -⟪g, fC⟫ := by
    dsimp only [t]
    field_simp [ne_of_lt hdegree0']
  let v := fC + t • f₀
  have hvbound : v ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).add_mem hboundedC
      ((KernelOperator.boundedL2Submodule μ).smul_mem t hbounded0)
  have hvmean : (∫ x, v x ∂μ) = 0 := by
    rw [← KernelOperator.inner_constant_one]
    change ⟪e, fC + t • f₀⟫ = 0
    rw [inner_add_right, real_inner_smul_right,
      KernelOperator.inner_constant_one, KernelOperator.inner_constant_one, hmeanC, hmean0]
    ring
  have hvdegree : ⟪g, v⟫ = 0 := by
    change ⟪g, fC + t • f₀⟫ = 0
    rw [inner_add_right, real_inner_smul_right]
    linarith only [htd]
  have hQ : B v v ≤ 0 :=
    hW.bounded_tangent_nonpositive (hW.strict_gap_structure hd hgap).regular
      v hvbound hvmean hvdegree
  have hQexp : B v v = B fC fC + 2 * t * B f₀ fC + t ^ 2 * B f₀ f₀ := by
    have hswap : B fC f₀ = B f₀ fC := hsym fC f₀
    simp only [v, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hswap]
    ring
  by_contra hnot
  have hbad : B a b < B b z := by
    change ¬ B b z ≤ B a b at hnot
    exact lt_of_not_ge hnot
  have hcrosspos : 0 < B f₀ fC := by rw [hcross]; linarith
  have hpart1 : 0 < 2 * t * B f₀ fC := by positivity
  have hpart2 : 0 ≤ t ^ 2 * B f₀ f₀ := mul_nonneg (sq_nonneg _) h0
  rw [hQexp] at hQ
  linarith only [hQ, hCquad, hpart1, hpart2]

/-- The original opposite-head row leaves a nonnegative shifted deficit on
the entire private source, almost everywhere under its original measure. -/
theorem ae_private_head_deficit_nonnegative (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hdegree0 : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) -
        Lp.const 2 μ (1 : ℝ)⟫ < 0) :
    ∀ᵐ x ∂μ.restrict (S.twoCenterPrivate r u),
      0 ≤ S.headPairing r u - r.val x - u.val x := by
  let P := S.twoCenterPrivate r u
  let κ := S.headPairing r u
  let E := P ∩ {x | κ < u.val x}
  have hP : MeasurableSet P := (R.measurableSet_twoCenter_patterns r u hp).1
  have hE : MeasurableSet E := hP.inter
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable u.val).measurable)
  have hEzero : μ E = 0 := by
    by_contra hn
    have hEpos : 0 < μ E := pos_iff_ne_zero.mpr hn
    have hcross := R.private_cross_le_headPairing r u hru hW hd hgap hp hintercept
      hdegree0 E hE hEpos (fun _ hx => hx.1)
    have hstrict : κ < ⟪u.val, KernelOperator.normalizedSetL2 E hE⟫ :=
      KernelOperator.normalizedSetL2_inner_gt_of_ae_gt E hE hEpos u.val κ
        ((ae_restrict_mem hE).mono (fun _ hx => hx.2))
    have heq : schurForm W m (S.normalizedHead u)
        (KernelOperator.normalizedSetL2 E hE) =
        ⟪u.val, KernelOperator.normalizedSetL2 E hE⟫ := by
      change ⟪shiftedOperator W m (S.normalizedHead u), _⟫ = _
      rw [S.operator_normalizedHead u]
    rw [heq] at hcross
    exact (not_lt_of_ge hcross) hstrict
  have hPmiss : P ⊆ KernelOperator.wholeFiberMissingSet S.ρ r.val :=
    fun _ hx => hx.1.2
  have hzero := KernelOperator.ae_zero_fiber_prod_missingSet (shiftedKernel W m)
    S.ρ S.hρ r.val ((S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.1))
    (shiftedKernel_measurable W m) (hW.moment_mem.mono (fun _ hp => hp.1))
  have hzeroP : ∀ᵐ p ∂(μ.restrict {x | S.ρ x = r.val}).prod (μ.restrict P),
      shiftedKernel W m p.1 p.2 = 0 :=
    ae_mono (Measure.prod_mono le_rfl (Measure.restrict_mono hPmiss le_rfl)) hzero
  have hrzero : ∀ᵐ x ∂μ.restrict P, r.val x = 0 :=
    KernelOperator.homogeneous_row_zero_of_zero_rectangle (shiftedKernel W m)
      {x | S.ρ x = r.val} P (S.hfibers r.val r.property).2.1 r.val
      ((S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.1)) hzeroP
  have hnot := measure_eq_zero_iff_ae_notMem.mp hEzero
  filter_upwards [ae_restrict_of_ae hnot, ae_restrict_mem hP, hrzero]
    with x hnot hx hrzero
  have hu : u.val x ≤ κ := le_of_not_gt (fun h => hnot ⟨hx, h⟩)
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
