module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairOrientation
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedCommonNeighbors
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedSources
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedExtraHoleGeometry

/-!
# Score floor outside the saturated heads

Whole shifted rows are nonnegative, non-high points outside the two head fibers
pay the three-clique score cap, and outside the two saturated heads and their
entire singleton compulsory sources the shifted-score deficit is at least
`1 + m`.
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

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem normalizedSetL2_inner_le_of_ae_le (s : Set Ω)
    (hs : MeasurableSet s) (hspos : 0 < μ s) (f : Lp ℝ 2 μ) (a : ℝ)
    (hf : ∀ᵐ x ∂μ.restrict s, f x ≤ a) :
    ⟪f, KernelOperator.normalizedSetL2 s hs⟫ ≤ a := by
  have hi : Integrable (fun x => f x) (μ.restrict s) :=
    ((Lp.memLp f).integrable (by norm_num)).integrableOn
  have hint := integral_mono_ae hi (integrable_const a) hf
  have hmasspos : 0 < μ.real s := ENNReal.toReal_pos hspos.ne' (measure_ne_top μ _)
  rw [setIntegral_const, smul_eq_mul] at hint
  rw [real_inner_comm, KernelOperator.normalizedSetL2_inner]
  calc
    _ ≤ (μ.real s)⁻¹ * (μ.real s * a) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hmasspos.le)
    _ = a := by field_simp

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Original whole shifted rows inherit nonnegativity from the actual
model moment on one positive root fiber. -/
theorem ae_whole_row_nonneg (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ∀ᵐ x ∂μ, 0 ≤ r.val x := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → 0 ≤ r.val p.2 := by
    filter_upwards [S.ae_kernel_eq_fiber_row r.val r.property, hW.moment_mem]
      with p hp hn hIr
    exact (hp hIr) ▸ hn.1
  obtain ⟨x, hx, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair))
  exact hsection.mono (fun _ hy => hy hx)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Almost every non-HIGH point outside a non-HIGH whole atom has a
strictly positive original shifted row from that atom. -/
theorem ae_row_pos_of_nonhigh_head
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hhead : μ ({x | S.ρ x = r.val} ∩ S.H) = 0) :
    ∀ᵐ x ∂μ, x ∉ S.H → S.ρ x ≠ r.val → 0 < r.val x := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hhead' : ∀ᵐ x ∂μ, x ∈ Ir → x ∉ S.H := by
    filter_upwards [compl_mem_ae_iff.mpr hhead] with x hx hr hh
    exact hx ⟨hr, hh⟩
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → p.2 ∉ S.H →
      S.ρ p.2 ≠ r.val → 0 < r.val p.2 := by
    filter_upwards [S.ae_kernel_eq_fiber_row r.val r.property, hW.moment_mem,
      S.hcoverage, S.hrelation, Measure.quasiMeasurePreserving_fst.ae hhead']
      with p hrow hnonneg hcover hrelation hn hr hnotH hdiff
    have hfirst : p.1 ∉ S.H := hn hr
    have hK : shiftedKernel W m p.1 p.2 = r.val p.2 := hrow hr
    have hnonneg' : 0 ≤ r.val p.2 := hK ▸ hnonneg.1
    by_contra hnotpos
    have hzero : shiftedKernel W m p.1 p.2 = 0 := by
      rw [hK]
      exact le_antisymm (le_of_not_gt hnotpos) hnonneg'
    rcases hcover hzero with ⟨q, _, hq1, hq2⟩ | hZ
    · exact hdiff (hq2.trans (hq1.symm.trans hr))
    · rcases hrelation hZ with h | h
      · exact hfirst h.1
      · exact hnotH h.1
  have hsections := Measure.ae_ae_of_ae_prod hpair
  obtain ⟨y, hy, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne' (ae_restrict_of_ae hsections)
  filter_upwards [hgood] with x hx hnotH hdiff
  exact hx hy hnotH hdiff

/-- Every non-HIGH point outside the two original head fibers is a
common neighbor and therefore pays the actual three-clique score cap. -/
theorem IsSaturatedAtomPair.ae_score_le_neg_two_m_of_not_high
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ, x ∉ S.H → S.ρ x ≠ r.val → S.ρ x ≠ u.val →
      r.val x + u.val x ≤ -2 * m := by
  filter_upwards [S.ae_row_pos_of_nonhigh_head r hW
    (hpair.high_head_null hW hd hgap hell),
    S.ae_row_pos_of_nonhigh_head u hW
      (hpair.symm.high_head_null hW hd hgap hell),
    hpair.ae_common_neighbor_score_le hW hd hgap]
    with x hr hu hcommon hnotH hnotr hnotu
  exact hcommon (hr hnotH hnotr) (hu hnotH hnotu)

/-- The only possible residual violations lie in one of the two
one-head missing HIGH regions. This is used after the actual extra-hole
geometry rules out positive subsets of those regions. -/
private theorem ae_score_floor_of_extra_hole_null
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (R : Set Ω)
    (hRmeas : MeasurableSet R)
    (hR : R ⊆ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val})ᶜ)
    (hnullr : μ (R ∩ S.H ∩ KernelOperator.wholeFiberMissingSet S.ρ r.val ∩
      (KernelOperator.wholeFiberMissingSet S.ρ u.val)ᶜ ∩
      {x | -2 * m < r.val x + u.val x}) = 0)
    (hnullu : μ (R ∩ S.H ∩ KernelOperator.wholeFiberMissingSet S.ρ u.val ∩
      (KernelOperator.wholeFiberMissingSet S.ρ r.val)ᶜ ∩
      {x | -2 * m < r.val x + u.val x}) = 0) :
    ∀ᵐ x ∂μ.restrict R, r.val x + u.val x ≤ -2 * m := by
  have hm : m < 0 := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hnotr := compl_mem_ae_iff.mpr hnullr
  have hnotu := compl_mem_ae_iff.mpr hnullu
  filter_upwards [ae_restrict_of_ae hnotr, ae_restrict_of_ae hnotu,
    ae_restrict_of_ae (S.ae_whole_row_nonneg r hW),
    ae_restrict_of_ae (S.ae_whole_row_nonneg u hW),
    ae_restrict_of_ae (hpair.ae_common_neighbor_score_le hW hd hgap),
    ae_restrict_of_ae (hpair.ae_score_le_neg_two_m_of_not_high hW hd hgap hell),
    ae_restrict_mem hRmeas]
    with x hnoR hnoU hrnonneg hunonneg hcommon hnonhigh hxR
  have hnotIr : S.ρ x ≠ r.val := by
    intro hx
    exact hR hxR (Or.inl hx)
  have hnotIu : S.ρ x ≠ u.val := by
    intro hx
    exact hR hxR (Or.inr hx)
  by_contra hbad
  have hbad' : -2 * m < r.val x + u.val x := lt_of_not_ge hbad
  have hxH : x ∈ S.H := by
    by_contra hn
    exact (not_lt_of_ge (hnonhigh hn hnotIr hnotIu)) hbad'
  by_cases hrpos : 0 < r.val x
  · by_cases hupos : 0 < u.val x
    · exact (not_lt_of_ge (hcommon hrpos hupos)) hbad'
    · have huzero : u.val x = 0 := le_antisymm (le_of_not_gt hupos) hunonneg
      have hNu : x ∈ KernelOperator.wholeFiberMissingSet S.ρ u.val :=
        ⟨hnotIu, by simp [huzero]⟩
      have hnotNr : x ∉ KernelOperator.wholeFiberMissingSet S.ρ r.val :=
        fun hx => not_lt_of_ge hx.2 hrpos
      exact hnoU ⟨⟨⟨⟨hxR, hxH⟩, hNu⟩, hnotNr⟩, hbad'⟩
  · by_cases hupos : 0 < u.val x
    · have hrzero : r.val x = 0 := le_antisymm (le_of_not_gt hrpos) hrnonneg
      have hNr : x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val :=
        ⟨hnotIr, by simp [hrzero]⟩
      have hnotNu : x ∉ KernelOperator.wholeFiberMissingSet S.ρ u.val :=
        fun hx => not_lt_of_ge hx.2 hupos
      exact hnoR ⟨⟨⟨⟨hxR, hxH⟩, hNr⟩, hnotNu⟩, hbad'⟩
    · have hrzero : r.val x = 0 := le_antisymm (le_of_not_gt hrpos) hrnonneg
      have huzero : u.val x = 0 := le_antisymm (le_of_not_gt hupos) hunonneg
      rw [hrzero, huzero] at hbad'
      linarith

/-- An actual strict-degree missing rectangle cannot carry a positive
region whose original saturated-head score exceeds the triangle cap. -/
private theorem no_positive_bad_region_with_zero_rectangle
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (E H L : Set Ω) (hH : MeasurableSet H) (hL : MeasurableSet L)
    (hHpos : 0 < μ H) (hLpos : 0 < μ L)
    (hHE : H ⊆ E) (hEbad : E ⊆ {x | -2 * m < r.val x + u.val x})
    (hLLow : L ⊆ S.L)
    (hLr : L ⊆ {x | S.ρ x ≠ r.val})
    (hLu : L ⊆ {x | S.ρ x ≠ u.val})
    (hzero : ∀ᵐ p ∂(μ.restrict H).prod (μ.restrict L),
      shiftedKernel W m p.1 p.2 = 0)
    (hdegree : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 L hL⟫ <
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 H hH⟫) : False := by
  let score : Lp ℝ 2 μ := r.val + u.val
  have hHscore : ∀ᵐ x ∂μ.restrict H, -2 * m < score x := by
    filter_upwards [ae_restrict_mem hH,
      ae_restrict_of_ae (Lp.coeFn_add r.val u.val)] with x hx hs
    change (r.val + u.val) x = r.val x + u.val x at hs
    have hbad := hEbad (hHE hx)
    change -2 * m < r.val x + u.val x at hbad
    simpa only [score, hs] using hbad
  have hLscore : ∀ᵐ x ∂μ.restrict L, score x ≤ -2 * m := by
    filter_upwards [ae_restrict_mem hL,
      ae_restrict_of_ae (hpair.ae_score_le_neg_two_m_of_not_high hW hd hgap hell),
      ae_restrict_of_ae (Lp.coeFn_add r.val u.val)] with x hx hs hc
    have hnotH : x ∉ S.H :=
      fun hh => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hh (hLLow hx)
    change (r.val + u.val) x = r.val x + u.val x at hc
    simpa only [score, hc] using hs hnotH (hLr hx) (hLu hx)
  have hHavg := KernelOperator.normalizedSetL2_inner_gt_of_ae_gt
    H hH hHpos score (-2 * m) hHscore
  have hLavg := normalizedSetL2_inner_le_of_ae_le
    L hL hLpos score (-2 * m) hLscore
  have hstrict := hpair.score_increases_across_missing_sets hW hd hgap hell
    H L hH hL hHpos hLpos hzero hdegree
  change ⟪score, KernelOperator.normalizedSetL2 H hH⟫ <
    ⟪score, KernelOperator.normalizedSetL2 L hL⟫ at hstrict
  linarith

/-- Outside the two original saturated heads and their entire original
singleton compulsory sources, the actual shifted-score deficit is at
least `1 + m`. The extra-hole cases use an original HIGH-to-LOW zero
rectangle and the actual tangent comparison. -/
theorem IsSaturatedAtomPair.ae_entire_source_score_floor
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict
      ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val} ∪
        S.reverseCompulsorySource {r} ∪ S.reverseCompulsorySource {u})ᶜ,
      1 + m ≤ 1 - m - r.val x - u.val x := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Iu : Set Ω := {x | S.ρ x = u.val}
  let SA := S.reverseCompulsorySource {r}
  let SB := S.reverseCompulsorySource {u}
  let R := (Ir ∪ Iu ∪ SA ∪ SB)ᶜ
  let Nr := KernelOperator.wholeFiberMissingSet S.ρ r.val
  let Nu := KernelOperator.wholeFiberMissingSet S.ρ u.val
  let bad : Set Ω := {x | -2 * m < r.val x + u.val x}
  let Er := R ∩ S.H ∩ Nr ∩ Nuᶜ ∩ bad
  let Eu := R ∩ S.H ∩ Nu ∩ Nrᶜ ∩ bad
  have hIr : MeasurableSet Ir := (S.hfibers r.val r.property).1
  have hIu : MeasurableSet Iu := (S.hfibers u.val u.property).1
  have hSA : MeasurableSet SA := S.measurableSet_reverseCompulsorySource {r}
  have hSB : MeasurableSet SB := S.measurableSet_reverseCompulsorySource {u}
  have hR : MeasurableSet R := (((hIr.union hIu).union hSA).union hSB).compl
  have hNr : MeasurableSet Nr :=
    KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ r.val
  have hNu : MeasurableSet Nu :=
    KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ u.val
  have hbad : MeasurableSet bad := measurableSet_lt measurable_const
    ((Lp.stronglyMeasurable r.val).measurable.add
      (Lp.stronglyMeasurable u.val).measurable)
  have hEr : MeasurableSet Er :=
    (((hR.inter S.hpartition.1).inter hNr).inter hNu.compl).inter hbad
  have hEu : MeasurableSet Eu :=
    (((hR.inter S.hpartition.1).inter hNu).inter hNr.compl).inter hbad
  have hRsub : R ⊆ (Ir ∪ Iu)ᶜ := by
    intro x hx h
    exact hx (Or.inl (Or.inl h))
  have hErzero : μ Er = 0 := by
    by_contra hne
    have hpos : 0 < μ Er := pos_iff_ne_zero.mpr hne
    obtain ⟨H, L, hH, hL, hHpos, hHE, hLpos, hLLow, hLout, hzero, hdegree⟩ :=
      hpair.exists_low_extra_hole_witness hW hd hgap hell Er hEr hpos
        (fun x hx => hx.1.1.1.2) (fun x hx => hx.1.1.2)
        (fun x hx => hx.1.2)
        (fun x hx hs => hx.1.1.1.1 (Or.inl (Or.inr hs)))
        (fun x hx => hRsub hx.1.1.1.1)
    exact no_positive_bad_region_with_zero_rectangle hpair hW hd hgap hell
      Er H L hH hL hHpos hLpos hHE (fun x hx => hx.2) hLLow
      (fun x hx hr => hLout hx (Or.inl hr))
      (fun x hx hu => hLout hx (Or.inr hu)) hzero hdegree
  have hEuzero : μ Eu = 0 := by
    by_contra hne
    have hpos : 0 < μ Eu := pos_iff_ne_zero.mpr hne
    obtain ⟨H, L, hH, hL, hHpos, hHE, hLpos, hLLow, hLout, hzero, hdegree⟩ :=
      hpair.symm.exists_low_extra_hole_witness hW hd hgap hell Eu hEu hpos
        (fun x hx => hx.1.1.1.2) (fun x hx => hx.1.1.2)
        (fun x hx => hx.1.2)
        (fun x hx hs => hx.1.1.1.1 (Or.inr hs))
        (fun x hx h => hRsub hx.1.1.1.1 h.symm)
    exact no_positive_bad_region_with_zero_rectangle hpair hW hd hgap hell
      Eu H L hH hL hHpos hLpos hHE (fun x hx => hx.2) hLLow
      (fun x hx hr => hLout hx (Or.inr hr))
      (fun x hx hu => hLout hx (Or.inl hu)) hzero hdegree
  have hscore := ae_score_floor_of_extra_hole_null hpair hW hd hgap hell
    R hR hRsub hErzero hEuzero
  filter_upwards [hscore] with x hx
  change r.val x + u.val x ≤ -2 * m at hx
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure
