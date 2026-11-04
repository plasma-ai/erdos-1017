module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalGeometry
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalTwoHeadClique
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedMissingScore
public import Erdos1017.SelectedModel.Structure.DegreeSetAverages

/-!
# Multipartite topology of the bad region

Every level set of the saturated shifted score is multipartite, its only missing
pairs lying inside whole atoms, and since bad points share the same saturated
shifted score, the bad support of the tight primal is multipartite.
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

private theorem no_zero_rectangle_at_equal_saturated_score
    (hpair : S.IsSaturatedAtomPair r p)
    {d c t : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (H L : Set Ω) (hH : MeasurableSet H) (hL : MeasurableSet L)
    (hHpos : 0 < μ H) (hLpos : 0 < μ L)
    (hscoreH : ∀ᵐ x ∂μ.restrict H, (r.val + p.val : Lp ℝ 2 μ) x = t)
    (hscoreL : ∀ᵐ x ∂μ.restrict L, (r.val + p.val : Lp ℝ 2 μ) x = t)
    (hzero : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict L), shiftedKernel W m q.1 q.2 = 0)
    (hdegree : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 L hL⟫ <
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 H hH⟫) : False := by
  have hstrict := hpair.score_increases_across_missing_sets hW hd hgap hell
    H L hH hL hHpos hLpos hzero hdegree
  rw [KernelOperator.normalizedSetL2_inner_eq_of_ae_eq H hH hHpos _ t hscoreH,
    KernelOperator.normalizedSetL2_inner_eq_of_ae_eq L hL hLpos _ t hscoreL] at hstrict
  exact (lt_irrefl t) hstrict

/-- One actual positive atom in a saturated-score level set cannot miss
another point of that level outside its own whole fiber. The strict
degree ordering is tested on genuine original zero rectangles. -/
private theorem equal_saturated_score_atom_missing_null
    (hpair : S.IsSaturatedAtomPair r p) (k : S.I)
    {d c t : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (E : Set Ω) (hE : MeasurableSet E)
    (hscore : ∀ᵐ x ∂μ.restrict E, (r.val + p.val : Lp ℝ 2 μ) x = t)
    (hpos : 0 < μ (E ∩ {x | S.ρ x = k.val})) :
    μ (E ∩ KernelOperator.wholeFiberMissingSet S.ρ k.val) = 0 := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let v := wholeRowDegree k.val
  let F := E ∩ {x | S.ρ x = k.val}
  let N := KernelOperator.wholeFiberMissingSet S.ρ k.val
  let T := E ∩ N
  let Llo := T ∩ {x | g x < v}
  let Lhi := T ∩ {x | v < g x}
  have hF : MeasurableSet F := hE.inter (S.hfibers k.val k.property).1
  have hN : MeasurableSet N :=
    KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ k.val
  have hT : MeasurableSet T := hE.inter hN
  have hLlo : MeasurableSet Llo := hT.inter
    (measurableSet_lt (Lp.stronglyMeasurable g).measurable measurable_const)
  have hLhi : MeasurableSet Lhi := hT.inter
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable g).measurable)
  have hscoreF : ∀ᵐ x ∂μ.restrict F, (r.val + p.val : Lp ℝ 2 μ) x = t :=
    ae_mono (Measure.restrict_mono inter_subset_left le_rfl) hscore
  have hscoreLo : ∀ᵐ x ∂μ.restrict Llo, (r.val + p.val : Lp ℝ 2 μ) x = t :=
    ae_mono (Measure.restrict_mono (fun _ hx => hx.1.1) le_rfl) hscore
  have hscoreHi : ∀ᵐ x ∂μ.restrict Lhi, (r.val + p.val : Lp ℝ 2 μ) x = t :=
    ae_mono (Measure.restrict_mono (fun _ hx => hx.1.1) le_rfl) hscore
  have hdegreeF : ∀ᵐ x ∂μ.restrict F, g x = v :=
    ae_mono (Measure.restrict_mono inter_subset_right le_rfl)
      (wholeRowFiber_degree W m S.ρ k.val (S.hfibers k.val k.property).2.2.2)
  have haverageF := KernelOperator.normalizedSetL2_inner_eq_of_ae_eq F hF hpos g v hdegreeF
  have hzeroFull := KernelOperator.ae_zero_fiber_prod_missingSet
    (shiftedKernel W m) S.ρ S.hρ k.val
    ((S.hfibers k.val k.property).2.2.2.rows.mono (fun _ hx => hx.1))
    (shiftedKernel_measurable W m) (hW.moment_mem.mono (fun _ hx => hx.1))
  have hzeroF (L : Set Ω) (hLN : L ⊆ N) :
      ∀ᵐ q ∂(μ.restrict F).prod (μ.restrict L), shiftedKernel W m q.1 q.2 = 0 :=
    ae_mono (Measure.prod_mono (Measure.restrict_mono inter_subset_right le_rfl)
      (Measure.restrict_mono hLN le_rfl)) hzeroFull
  have hLoNull : μ Llo = 0 := by
    by_contra hn
    have hLpos : 0 < μ Llo := pos_iff_ne_zero.mpr hn
    have hlt := KernelOperator.normalizedSetL2_inner_lt_of_ae_lt Llo hLlo hLpos g v
      ((ae_restrict_mem hLlo).mono (fun _ hx => hx.2))
    have hdegree : ⟪g, KernelOperator.normalizedSetL2 Llo hLlo⟫ <
        ⟪g, KernelOperator.normalizedSetL2 F hF⟫ := by rwa [haverageF]
    exact no_zero_rectangle_at_equal_saturated_score hpair hW hd hgap hell
      F Llo hF hLlo hpos hLpos hscoreF hscoreLo
      (hzeroF Llo (fun _ hx => hx.1.2)) hdegree
  have hHiNull : μ Lhi = 0 := by
    by_contra hn
    have hLpos : 0 < μ Lhi := pos_iff_ne_zero.mpr hn
    have hgt := KernelOperator.normalizedSetL2_inner_gt_of_ae_gt Lhi hLhi hLpos g v
      ((ae_restrict_mem hLhi).mono (fun _ hx => hx.2))
    have hdegree : ⟪g, KernelOperator.normalizedSetL2 F hF⟫ <
        ⟪g, KernelOperator.normalizedSetL2 Lhi hLhi⟫ := by rwa [haverageF]
    have hzero : ∀ᵐ q ∂(μ.restrict Lhi).prod (μ.restrict F),
        shiftedKernel W m q.1 q.2 = 0 := by
      filter_upwards [(Measure.measurePreserving_swap
        (μ := μ.restrict Lhi) (ν := μ.restrict F)).quasiMeasurePreserving.ae
          (hzeroF Lhi (fun _ hx => hx.1.2)),
        ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
          (shiftedMoment_symm W m)] with q hz hs
      change shiftedKernel W m q.2 q.1 = 0 at hz
      exact hs.symm.trans hz
    exact no_zero_rectangle_at_equal_saturated_score hpair hW hd hgap hell
      Lhi F hLhi hF hLpos hpos hscoreHi hscoreF hzero hdegree
  have hzeroT := hzeroF T inter_subset_right
  have hne : ∀ᵐ q ∂(μ.restrict F).prod (μ.restrict T), g q.1 ≠ g q.2 := by
    filter_upwards [hzeroT,
      ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) S.hdegreeNe,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hF),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hT)] with q hz hn hx hy
    exact hn ⟨hz, fun he => hy.2.1 (he.symm.trans hx.2)⟩
  obtain ⟨x, _, hxg, hxne⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (hdegreeF.and (Measure.ae_ae_of_ae_prod hne))
  have hcover : ∀ᵐ z ∂μ, z ∈ T → z ∈ Llo ∪ Lhi := by
    apply (ae_restrict_iff' hT).mp
    filter_upwards [hxne, ae_restrict_mem hT] with z hz hTz
    change g x ≠ g z at hz
    have hneq : g z ≠ v := fun he => hz (hxg.trans he.symm)
    exact (lt_or_gt_of_ne hneq).elim (fun h => Or.inl ⟨hTz, h⟩) (fun h => Or.inr ⟨hTz, h⟩)
  have hle := (measure_mono_ae hcover).trans (measure_union_le Llo Lhi)
  rw [hLoNull, hHiNull, zero_add] at hle
  exact le_antisymm hle bot_le

/-- Every level set of the original saturated shifted score is genuinely
multipartite: its only missing pairs lie inside original whole atoms.
Countably many positive fibers and true diffuse dust are retained. -/
theorem ae_equal_saturated_score_missing_iff_sameAtom
    (hpair : S.IsSaturatedAtomPair r p)
    {d c t : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (E : Set Ω) (hE : MeasurableSet E)
    (hscore : ∀ᵐ x ∂μ.restrict E, (r.val + p.val : Lp ℝ 2 μ) x = t) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ E → q.2 ∈ E →
      (adjacencyKernel W q.1 q.2 = 0 ↔ q ∈ S.sameAtomRelation) := by
  let : Countable S.I := S.hI.to_subtype
  have hatom : ∀ᵐ q ∂μ.prod μ, ∀ k : S.I, q.1 ∈ E → S.ρ q.1 = k.val →
      q.2 ∈ E → q ∉ actualZeroRelation W m S.ρ := by
    apply ae_all_iff.mpr
    intro k
    by_cases hpos : 0 < μ (E ∩ {x | S.ρ x = k.val})
    · have hnull := equal_saturated_score_atom_missing_null hpair k hW hd hgap hell E hE hscore hpos
      have hnot := measure_eq_zero_iff_ae_notMem.mp hnull
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae hnot,
        S.ae_kernel_eq_fiber_row k.val k.property] with q hn hk hx hlabel hy hZ
      apply hn
      refine ⟨hy, ?_⟩
      have hne : S.ρ q.2 ≠ k.val := fun he => hZ.2 (hlabel.trans he.symm)
      have hz : k.val q.2 = 0 := (hk hlabel).symm.trans hZ.1
      exact ⟨hne, hz.le⟩
    · have hnull : μ (E ∩ {x | S.ρ x = k.val}) = 0 :=
        le_antisymm (le_of_not_gt hpos) bot_le
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (measure_eq_zero_iff_ae_notMem.mp hnull)] with q hn hx hk _ _
      exact hn ⟨hx, hk⟩
  have hnoZ : ∀ᵐ q ∂μ.prod μ, q.1 ∈ E → q.2 ∈ E →
      q ∉ actualZeroRelation W m S.ρ := by
    filter_upwards [hatom,
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hatom,
      S.hDcomplete, (hW.strict_gap_structure hd hgap).strict_support,
      actualZeroRelation_symm W m S.ρ] with q ha hb hD hs hsym hx hy hZ
    by_cases hxD : q.1 ∈ S.D
    · by_cases hyD : q.2 ∈ S.D
      · have hone := hD hxD hyD
        have hz : shiftedMoment W m q = 0 := hZ.1
        rw [hz] at hs
        simp only [lt_self_iff_false, ↓reduceIte] at hs
        linarith
      · have hat : q.2 ∈ ⋃ k ∈ S.I, {z | S.ρ z = k} := by
          simpa only [S.hDeq, mem_compl_iff, not_not] using hyD
        obtain ⟨k, hk⟩ := mem_iUnion.mp hat
        obtain ⟨hkI, hlabel⟩ := mem_iUnion.mp hk
        exact hb ⟨k, hkI⟩ hy hlabel hx (hsym.mp hZ)
    · have hat : q.1 ∈ ⋃ k ∈ S.I, {z | S.ρ z = k} := by
        simpa only [S.hDeq, mem_compl_iff, not_not] using hxD
      obtain ⟨k, hk⟩ := mem_iUnion.mp hat
      obtain ⟨hkI, hlabel⟩ := mem_iUnion.mp hk
      exact ha ⟨k, hkI⟩ hx hlabel hy hZ
  filter_upwards [hnoZ, S.ae_zero_iff_sameAtom_or_relation hW hd hgap,
    (hW.strict_gap_structure hd hgap).strict_support, hW.moment_mem] with q hn hz hs hm hx hy
  constructor
  · intro hG
    have hM : shiftedKernel W m q.1 q.2 = 0 := by
      apply le_antisymm _ hm.1
      by_contra hnot
      have hpos : 0 < shiftedMoment W m q := lt_of_not_ge hnot
      rw [ite_eq_left hpos] at hs
      change adjacencyKernel W q.1 q.2 = 1 at hs
      linarith
    exact (hz.mp hM).resolve_right (hn hx hy)
  · intro hsame
    have hM : shiftedMoment W m q = 0 := hz.mpr (Or.inl hsame)
    rw [hM] at hs
    simpa only [adjacencyKernel, Prod.mk.eta, lt_self_iff_false, ↓reduceIte] using hs

/-- Actual bad points have equal saturated shifted score. The same
original tight primal therefore gives multipartite bad support, with no
supplied cross-half or missing-pair topology certificate. -/
theorem UniversalPhysicalPrimal.ae_universalUpperE2Bad_missing_iff_sameAtom
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) < 3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.universalUpperE2BadRegion r p d c →
      q.2 ∈ S.universalUpperE2BadRegion r p d c →
        (adjacencyKernel W q.1 q.2 = 0 ↔ q ∈ S.sameAtomRelation) := by
  let B := S.universalUpperE2BadRegion r p d c
  have hB : MeasurableSet B := S.measurableSet_universalUpperE2BadRegion r p d c
  have hU : MeasurableSet (S.universalPartnerCommonRegion r p) :=
    S.measurableSet_universalPartnerCommonRegion r p
  have hcommon := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap hN hA
    hAhalf hell hmargin
  have hpPos := (ae_restrict_iff' hU).mp (S.ae_partner_row_pos_on_universalCommon r p)
  have hscore : ∀ᵐ x ∂μ.restrict B, (r.val + p.val : Lp ℝ 2 μ) x = -2 * m := by
    filter_upwards [P.ae_universalUpperE2Bad_partner_charge S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin, ae_restrict_mem hB,
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
    linarith
  exact ae_equal_saturated_score_missing_iff_sameAtom hpair hW hd hgap hell.2 B hB hscore

end Erdos1017.CappedModel.SelectedHighLowStructure
