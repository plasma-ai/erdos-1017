module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalBadTopology
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedScoreFloor
public import Erdos1017.SelectedModel.Structure.DegreeSetAverages

/-!
# Low holes of bad vertices in the universal primal

A bad vertex in the high region has no low outside-own hole, since the strict
degree order conflicts with its saturated score, and every bad outside-own hole
lies in the good high region with root charge at least `theta`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r p : S.I}

private theorem no_zero_rectangle_from_score_level_to_sublevel
    (hpair : S.IsSaturatedAtomPair r p)
    {d c t : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (H L : Set Ω) (hH : MeasurableSet H) (hL : MeasurableSet L)
    (hHpos : 0 < μ H) (hLpos : 0 < μ L)
    (hscoreH : ∀ᵐ x ∂μ.restrict H, (r.val + p.val : Lp ℝ 2 μ) x = t)
    (hscoreL : ∀ᵐ x ∂μ.restrict L, (r.val + p.val : Lp ℝ 2 μ) x ≤ t)
    (hzero : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict L), shiftedKernel W m q.1 q.2 = 0)
    (hdegree : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 L hL⟫ <
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 H hH⟫) : False := by
  have hstrict := hpair.score_increases_across_missing_sets hW hd hgap hell
    H L hH hL hHpos hLpos hzero hdegree
  rw [KernelOperator.normalizedSetL2_inner_eq_of_ae_eq H hH hHpos _ t hscoreH] at hstrict
  have hi : Integrable (fun x => (r.val + p.val : Lp ℝ 2 μ) x) (μ.restrict L) :=
    ((Lp.memLp (r.val + p.val)).integrable (by norm_num)).integrableOn
  have hint := integral_mono_ae hi (integrable_const t) hscoreL
  have hmass : 0 < μ.real L := ENNReal.toReal_pos hLpos.ne' (measure_ne_top μ _)
  rw [setIntegral_const, smul_eq_mul] at hint
  have haverage : ⟪r.val + p.val, KernelOperator.normalizedSetL2 L hL⟫ ≤ t := by
    rw [real_inner_comm, KernelOperator.normalizedSetL2_inner]
    calc
      _ ≤ (μ.real L)⁻¹ * (μ.real L * t) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hmass.le)
      _ = t := by field_simp
  exact (not_lt_of_ge haverage) hstrict

private theorem high_level_atom_low_sublevel_missing_null
    (hpair : S.IsSaturatedAtomPair r p) (k : S.I)
    {d c t : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (E F : Set Ω) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEH : E ⊆ S.H)
    (hscoreE : ∀ᵐ x ∂μ.restrict E, (r.val + p.val : Lp ℝ 2 μ) x = t)
    (hscoreF : ∀ᵐ x ∂μ.restrict F, (r.val + p.val : Lp ℝ 2 μ) x ≤ t)
    (hpos : 0 < μ (E ∩ {x | S.ρ x = k.val})) :
    μ (F ∩ KernelOperator.wholeFiberMissingSet S.ρ k.val) = 0 := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let H := E ∩ {x | S.ρ x = k.val}
  let N := KernelOperator.wholeFiberMissingSet S.ρ k.val
  let L := F ∩ N
  have hH : MeasurableSet H := hE.inter (S.hfibers k.val k.property).1
  have hN : MeasurableSet N :=
    KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ k.val
  have hL : MeasurableSet L := hF.inter hN
  by_contra hn
  have hLpos : 0 < μ L := pos_iff_ne_zero.mpr hn
  have hzero : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict L),
      shiftedKernel W m q.1 q.2 = 0 :=
    ae_mono (Measure.prod_mono (Measure.restrict_mono inter_subset_right le_rfl)
      (Measure.restrict_mono inter_subset_right le_rfl))
      (KernelOperator.ae_zero_fiber_prod_missingSet (shiftedKernel W m) S.ρ S.hρ k.val
        ((S.hfibers k.val k.property).2.2.2.rows.mono (fun _ hx => hx.1))
        (shiftedKernel_measurable W m) (hW.moment_mem.mono (fun _ hx => hx.1)))
  have hdegreeH : ∀ᵐ x ∂μ.restrict H, g x = wholeRowDegree k.val :=
    ae_mono (Measure.restrict_mono inter_subset_right le_rfl)
      (wholeRowFiber_degree W m S.ρ k.val (S.hfibers k.val k.property).2.2.2)
  have horder : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict L), g q.2 < g q.1 := by
    filter_upwards [hzero,
      ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) S.hrelation,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hH),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hL)] with q hz hr hx hy
    have hZ : q ∈ actualZeroRelation W m S.ρ :=
      ⟨hz, fun he => hy.2.1 (he.symm.trans hx.2)⟩
    rcases hr hZ with h | h
    · exact h.2.2
    · exact (disjoint_left.mp S.hpartition.2.2.2.2.1 (hEH hx.1) h.2.1).elim
  obtain ⟨x, _, hxg, hxl⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (hdegreeH.and (Measure.ae_ae_of_ae_prod horder))
  have hdegreeL : ∀ᵐ z ∂μ.restrict L, g z < wholeRowDegree k.val :=
    hxl.mono (fun _ hz => hz.trans_eq hxg)
  have haverageH := KernelOperator.normalizedSetL2_inner_eq_of_ae_eq H hH hpos g _ hdegreeH
  have haverageL := KernelOperator.normalizedSetL2_inner_lt_of_ae_lt L hL hLpos g _ hdegreeL
  have hdegree : ⟪g, KernelOperator.normalizedSetL2 L hL⟫ <
      ⟪g, KernelOperator.normalizedSetL2 H hH⟫ := by rwa [haverageH]
  exact no_zero_rectangle_from_score_level_to_sublevel hpair hW hd hgap hell
    H L hH hL hpos hLpos
    (ae_mono (Measure.restrict_mono inter_subset_left le_rfl) hscoreE)
    (ae_mono (Measure.restrict_mono inter_subset_left le_rfl) hscoreF) hzero hdegree

private theorem low_sublevel_atom_high_level_missing_null
    (hpair : S.IsSaturatedAtomPair r p) (k : S.I)
    {d c t : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (E F : Set Ω) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEH : E ⊆ S.H)
    (hscoreE : ∀ᵐ x ∂μ.restrict E, (r.val + p.val : Lp ℝ 2 μ) x = t)
    (hscoreF : ∀ᵐ x ∂μ.restrict F, (r.val + p.val : Lp ℝ 2 μ) x ≤ t)
    (hpos : 0 < μ (F ∩ {x | S.ρ x = k.val})) :
    μ (E ∩ KernelOperator.wholeFiberMissingSet S.ρ k.val) = 0 := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let N := KernelOperator.wholeFiberMissingSet S.ρ k.val
  let H := E ∩ N
  let L := F ∩ {x | S.ρ x = k.val}
  have hN : MeasurableSet N :=
    KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ k.val
  have hH : MeasurableSet H := hE.inter hN
  have hL : MeasurableSet L := hF.inter (S.hfibers k.val k.property).1
  by_contra hn
  have hHpos : 0 < μ H := pos_iff_ne_zero.mpr hn
  have hzeroLH : ∀ᵐ q ∂(μ.restrict L).prod (μ.restrict H),
      shiftedKernel W m q.1 q.2 = 0 :=
    ae_mono (Measure.prod_mono (Measure.restrict_mono inter_subset_right le_rfl)
      (Measure.restrict_mono inter_subset_right le_rfl))
      (KernelOperator.ae_zero_fiber_prod_missingSet (shiftedKernel W m) S.ρ S.hρ k.val
        ((S.hfibers k.val k.property).2.2.2.rows.mono (fun _ hx => hx.1))
        (shiftedKernel_measurable W m) (hW.moment_mem.mono (fun _ hx => hx.1)))
  have hzero : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict L),
      shiftedKernel W m q.1 q.2 = 0 := by
    filter_upwards [(Measure.measurePreserving_swap
      (μ := μ.restrict H) (ν := μ.restrict L)).quasiMeasurePreserving.ae hzeroLH,
      ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
        (shiftedMoment_symm W m)] with q hz hs
    change shiftedKernel W m q.2 q.1 = 0 at hz
    exact hs.symm.trans hz
  have hdegreeL : ∀ᵐ x ∂μ.restrict L, g x = wholeRowDegree k.val :=
    ae_mono (Measure.restrict_mono inter_subset_right le_rfl)
      (wholeRowFiber_degree W m S.ρ k.val (S.hfibers k.val k.property).2.2.2)
  have horder : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict L), g q.2 < g q.1 := by
    filter_upwards [hzero,
      ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) S.hrelation,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hH),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hL)] with q hz hr hx hy
    have hZ : q ∈ actualZeroRelation W m S.ρ :=
      ⟨hz, fun he => hx.2.1 (he.trans hy.2)⟩
    rcases hr hZ with h | h
    · exact h.2.2
    · exact (disjoint_left.mp S.hpartition.2.2.2.2.1 (hEH hx.1) h.2.1).elim
  have horderSwap := (Measure.measurePreserving_swap
    (μ := μ.restrict L) (ν := μ.restrict H)).quasiMeasurePreserving.ae horder
  obtain ⟨y, _, hyg, hyh⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (hdegreeL.and (Measure.ae_ae_of_ae_prod horderSwap))
  have hdegreeH : ∀ᵐ x ∂μ.restrict H, wholeRowDegree k.val < g x :=
    hyh.mono (fun _ hx => hyg ▸ hx)
  have haverageL := KernelOperator.normalizedSetL2_inner_eq_of_ae_eq L hL hpos g _ hdegreeL
  have haverageH := KernelOperator.normalizedSetL2_inner_gt_of_ae_gt H hH hHpos g _ hdegreeH
  have hdegree : ⟪g, KernelOperator.normalizedSetL2 L hL⟫ <
      ⟪g, KernelOperator.normalizedSetL2 H hH⟫ := by rwa [haverageL]
  exact no_zero_rectangle_from_score_level_to_sublevel hpair hW hd hgap hell
    H L hH hL hHpos hpos
    (ae_mono (Measure.restrict_mono inter_subset_left le_rfl) hscoreE)
    (ae_mono (Measure.restrict_mono inter_subset_left le_rfl) hscoreF) hzero hdegree

private theorem ae_high_level_low_sublevel_no_zero_relation
    (hpair : S.IsSaturatedAtomPair r p)
    {d c t : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (E F : Set Ω) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEH : E ⊆ S.H)
    (hscoreE : ∀ᵐ x ∂μ.restrict E, (r.val + p.val : Lp ℝ 2 μ) x = t)
    (hscoreF : ∀ᵐ x ∂μ.restrict F, (r.val + p.val : Lp ℝ 2 μ) x ≤ t) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ E → q.2 ∈ F → q ∉ actualZeroRelation W m S.ρ := by
  let : Countable S.I := S.hI.to_subtype
  have hatomH : ∀ᵐ q ∂μ.prod μ, ∀ k : S.I,
      q.1 ∈ E → S.ρ q.1 = k.val → q.2 ∈ F → q ∉ actualZeroRelation W m S.ρ := by
    apply ae_all_iff.mpr
    intro k
    by_cases hpos : 0 < μ (E ∩ {x | S.ρ x = k.val})
    · have hnull := high_level_atom_low_sublevel_missing_null hpair k hW hd hgap
        hell E F hE hF hEH hscoreE hscoreF hpos
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae
        (measure_eq_zero_iff_ae_notMem.mp hnull),
        S.ae_kernel_eq_fiber_row k.val k.property] with q hn hk hx hlabel hy hZ
      exact hn ⟨hy, ⟨fun he => hZ.2 (hlabel.trans he.symm),
        le_of_eq ((hk hlabel).symm.trans hZ.1)⟩⟩
    · have hnull : μ (E ∩ {x | S.ρ x = k.val}) = 0 :=
        le_antisymm (le_of_not_gt hpos) bot_le
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (measure_eq_zero_iff_ae_notMem.mp hnull)] with q hn hx hk _ _
      exact hn ⟨hx, hk⟩
  have hatomL : ∀ᵐ q ∂μ.prod μ, ∀ k : S.I,
      q.1 ∈ E → q.2 ∈ F → S.ρ q.2 = k.val → q ∉ actualZeroRelation W m S.ρ := by
    apply ae_all_iff.mpr
    intro k
    by_cases hpos : 0 < μ (F ∩ {x | S.ρ x = k.val})
    · have hnull := low_sublevel_atom_high_level_missing_null hpair k hW hd hgap
        hell E F hE hF hEH hscoreE hscoreF hpos
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (measure_eq_zero_iff_ae_notMem.mp hnull),
        (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
          (S.ae_kernel_eq_fiber_row k.val k.property), shiftedMoment_symm W m]
        with q hn hk hs hx hy hlabel hZ
      have hz : k.val q.1 = 0 := (hk hlabel).symm.trans (hs.trans hZ.1)
      exact hn ⟨hx, ⟨fun he => hZ.2 (he.trans hlabel.symm), hz.le⟩⟩
    · have hnull : μ (F ∩ {x | S.ρ x = k.val}) = 0 :=
        le_antisymm (le_of_not_gt hpos) bot_le
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae
        (measure_eq_zero_iff_ae_notMem.mp hnull)] with q hn _ hy hk _
      exact hn ⟨hy, hk⟩
  filter_upwards [hatomH, hatomL, S.hDcomplete,
    (hW.strict_gap_structure hd hgap).strict_support] with q ha hb hD hs hx hy hZ
  by_cases hxD : q.1 ∈ S.D
  · by_cases hyD : q.2 ∈ S.D
    · have hone := hD hxD hyD
      have hz : shiftedMoment W m q = 0 := hZ.1
      rw [hz] at hs
      simp only [lt_self_iff_false, ↓reduceIte] at hs
      linarith only [hone, hs]
    · have hat : q.2 ∈ ⋃ k ∈ S.I, {z | S.ρ z = k} := by
        simpa only [S.hDeq, mem_compl_iff, not_not] using hyD
      obtain ⟨k, hk⟩ := mem_iUnion.mp hat
      obtain ⟨hkI, hlabel⟩ := mem_iUnion.mp hk
      exact hb ⟨k, hkI⟩ hx hy hlabel hZ
  · have hat : q.1 ∈ ⋃ k ∈ S.I, {z | S.ρ z = k} := by
      simpa only [S.hDeq, mem_compl_iff, not_not] using hxD
    obtain ⟨k, hk⟩ := mem_iUnion.mp hat
    obtain ⟨hkI, hlabel⟩ := mem_iUnion.mp hk
    exact ha ⟨k, hkI⟩ hx hlabel hy hZ

private theorem UniversalPhysicalPrimal.ae_bad_shifted_score
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalUpperE2BadRegion r p d c),
      (r.val + p.val : Lp ℝ 2 μ) x = -2 * m := by
  have hcommon := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  have hpPos := (ae_restrict_iff' (S.measurableSet_universalPartnerCommonRegion r p)).mp
    (S.ae_partner_row_pos_on_universalCommon r p)
  filter_upwards [P.ae_universalUpperE2Bad_partner_charge S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin,
    ae_restrict_mem (S.measurableSet_universalUpperE2BadRegion r p d c),
    ae_restrict_of_ae hcommon, ae_restrict_of_ae hpPos,
    ae_restrict_of_ae (S.ae_universal_row_pos_on_outside r hW hd hgap hN),
    ae_restrict_of_ae (S.ae_universalRootDeficit_eq_shifted_row r hW hd hgap),
    ae_restrict_of_ae (S.ae_universalRootDeficit_eq_shifted_row p hW hd hgap),
    ae_restrict_of_ae (Lp.coeFn_add r.val p.val)] with x hcharge hx hc hp hr heR heP hcoe
  have hxr : S.ρ x ≠ r.val := fun he => hx.1 (Or.inl he)
  have hrpos := hr hxr
  have hppos := hp (hc hx)
  simp only [universalRootDeficit, ite_eq_left hrpos, ite_eq_left hppos, mul_one] at heR heP
  rw [hcoe]
  change r.val x + p.val x = -2 * m
  linarith only [hcharge, heR, heP]

/-- A HIGH bad vertex has no original outside-own LOW hole. The strict
original degree order conflicts with its actual saturated score. -/
theorem UniversalPhysicalPrimal.ae_bad_high_low_join
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.universalUpperE2BadRegion r p d c →
      q.1 ∈ S.H → q.2 ∈ S.L → q ∉ S.sameAtomRelation →
        adjacencyKernel W q.1 q.2 = 1 := by
  let B := S.universalUpperE2BadRegion r p d c
  let E := B ∩ S.H
  let F := S.L ∩ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ
  have hE : MeasurableSet E :=
    (S.measurableSet_universalUpperE2BadRegion r p d c).inter S.hpartition.1
  have hF : MeasurableSet F := S.hpartition.2.1.inter
    (((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).compl)
  have hscoreE : ∀ᵐ x ∂μ.restrict E, (r.val + p.val : Lp ℝ 2 μ) x = -2 * m :=
    ae_mono (Measure.restrict_mono inter_subset_left le_rfl)
      (P.ae_bad_shifted_score S r p hpair hW hd hgap hN hA hAhalf hell hmargin)
  have hscoreF : ∀ᵐ x ∂μ.restrict F, (r.val + p.val : Lp ℝ 2 μ) x ≤ -2 * m := by
    filter_upwards [ae_restrict_mem hF,
      ae_restrict_of_ae (hpair.ae_score_le_neg_two_m_of_not_high hW hd hgap hell.2),
      ae_restrict_of_ae (Lp.coeFn_add r.val p.val)] with x hx hs hcoe
    rw [hcoe]
    exact hs (fun hh => disjoint_left.mp S.hpartition.2.2.2.2.1 hh hx.1)
      (fun h => hx.2 (Or.inl h)) (fun h => hx.2 (Or.inr h))
  have hnoZ := ae_high_level_low_sublevel_no_zero_relation hpair hW hd hgap hell.2
    E F hE hF inter_subset_right hscoreE hscoreF
  have hcommon := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  have hppos := (ae_restrict_iff' (S.measurableSet_universalPartnerCommonRegion r p)).mp
    (S.ae_partner_row_pos_on_universalCommon r p)
  have hneutral := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hN
  filter_upwards [hnoZ, S.ae_zero_iff_sameAtom_or_relation hW hd hgap,
    (hW.strict_gap_structure hd hgap).strict_support, hW.moment_mem,
    Measure.quasiMeasurePreserving_fst.ae hcommon,
    Measure.quasiMeasurePreserving_fst.ae hppos,
    Measure.quasiMeasurePreserving_snd.ae hneutral,
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (S.ae_kernel_eq_fiber_row p.val p.property), shiftedMoment_symm W m]
    with q hn hz hs hm hc hp hNq hrow hsym hx hh hl hnotSame
  have hnotZ : q ∉ actualZeroRelation W m S.ρ := by
    intro hZ
    by_cases hyr : S.ρ q.2 = r.val
    · exact disjoint_left.mp S.hpartition.2.2.2.2.2.2 hl (hNq hyr)
    by_cases hyp : S.ρ q.2 = p.val
    · have hzero : p.val q.1 = 0 := (hrow hyp).symm.trans (hsym.trans hZ.1)
      exact (ne_of_gt (hp (hc hx))) hzero
    exact hn ⟨hx, hh⟩ ⟨hl, fun h => h.elim hyr hyp⟩ hZ
  have hnotK : shiftedKernel W m q.1 q.2 ≠ 0 := fun h =>
    (hz.mp h).elim hnotSame hnotZ
  have hpos : 0 < shiftedMoment W m q := lt_of_le_of_ne hm.1 (Ne.symm hnotK)
  change adjacencyKernel W q.1 q.2 = (if 0 < shiftedMoment W m q then 1 else 0) at hs
  simpa only [ite_eq_left hpos] using hs

/-- Every actual bad outside-own hole lies in the HIGH good region on the
original law. In particular its signed root charge is at least theta. -/
theorem UniversalPhysicalPrimal.ae_bad_outside_own_missing_high_good
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.universalUpperE2BadRegion r p d c →
      PhysicalRepresentative.adjacency W m q.1 q.2 = false → q ∉ S.sameAtomRelation →
        q.2 ∈ (S.universalPartnerCommonRegion r p \ S.universalUpperE2BadRegion r p d c) ∩
          S.H := by
  have hbadSame := P.ae_universalUpperE2Bad_missing_iff_sameAtom S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  have hlowJoin := P.ae_bad_high_low_join S r p hpair hW hd hgap hN hA hAhalf hell hmargin
  have hcommon := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  have hppos := (ae_restrict_iff' (S.measurableSet_universalPartnerCommonRegion r p)).mp
    (S.ae_partner_row_pos_on_universalCommon r p)
  have hroot := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.neutral_atom_physical_adjacency r hW hd hgap hN)
  have hpartner := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_adjacency p hW hd hgap)
  have hholeJoin := (Measure.measurePreserving_swap
    (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (P.ae_universalUpperE2_hole_bad_join S r p hpair hW hd hgap hN
        hA hAhalf hell hmargin)
  filter_upwards [hbadSame, hlowJoin, hroot, hpartner, hholeJoin,
    Measure.quasiMeasurePreserving_fst.ae hcommon,
    Measure.quasiMeasurePreserving_fst.ae hppos,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support,
    (hW.strict_gap_structure hd hgap).strict_support, hW.moment_mem,
    S.ae_zero_iff_sameAtom_or_relation hW hd hgap, S.hrelation, adjacencyKernel_symm W]
    with q hbad hlow hr hp hH hc hpp ha hs hm hz hrel hsym hx hmissing hnotSame
  have hAdj : adjacencyKernel W q.1 q.2 = 0 := by
    change adjacencyKernel W q.1 q.2 = _ at ha
    rw [ha, hmissing]
    norm_num
  have hK : shiftedKernel W m q.1 q.2 = 0 := by
    apply le_antisymm _ hm.1
    exact le_of_not_gt (fun hpos => by
      have hone : adjacencyKernel W q.1 q.2 = 1 := by
        change adjacencyKernel W q.1 q.2 = (if 0 < shiftedMoment W m q then 1 else 0) at hs
        simpa only [ite_eq_left hpos] using hs
      linarith only [hAdj, hone])
  have hZ : q ∈ actualZeroRelation W m S.ρ := (hz.mp hK).resolve_left hnotSame
  have hHigh : q.2 ∈ S.H := by
    rcases hrel hZ with h | h
    · have hone := hlow hx h.1 h.2.1 hnotSame
      exact False.elim (by linarith only [hAdj, hone])
    · exact h.1
  have hnotBad : q.2 ∉ S.universalUpperE2BadRegion r p d c :=
    fun h => hnotSame ((hbad hx h).mp hAdj)
  have hnotRoot : S.ρ q.2 ≠ r.val := by
    intro h
    have hxr : S.ρ q.1 ≠ r.val := fun h => hx.1 (Or.inl h)
    have ht : PhysicalRepresentative.adjacency W m q.2 q.1 = true := (hr h).mpr hxr
    rw [PhysicalRepresentative.adjacency_symm W m, hmissing] at ht
    cases ht
  have hnotPartner : S.ρ q.2 ≠ p.val := by
    intro h
    have hNp : q.1 ∈ S.rootNeighborhood p :=
      ⟨fun h => hx.1 (Or.inr h), hpp (hc hx)⟩
    have ht : PhysicalRepresentative.adjacency W m q.2 q.1 = true := (hp h).mpr hNp
    rw [PhysicalRepresentative.adjacency_symm W m, hmissing] at ht
    cases ht
  have hnotHole : q.2 ∉ S.universalPartnerHoleRegion r p := by
    intro h
    have hone : adjacencyKernel W q.2 q.1 = 1 := hH h hx
    rw [hsym] at hAdj
    linarith only [hAdj, hone]
  refine ⟨⟨?_, hnotBad⟩, hHigh⟩
  intro h
  rcases h with (h | h) | h
  · exact hnotRoot h
  · exact hnotPartner h
  · exact hnotHole h

end Erdos1017.CappedModel.SelectedHighLowStructure
