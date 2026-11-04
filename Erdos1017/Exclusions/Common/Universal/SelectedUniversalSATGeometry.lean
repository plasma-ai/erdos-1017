module

public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedSourceBudget
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalRootDegree
public import Erdos1017.SelectedModel.Structure.WholeRowMissingMass
public import Erdos1017.Exclusions.Common.SelectedAtomicChargeBlocks
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairUniqueness
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateRootStar

/-!
# Geometry of the saturated partner of a universal root

This module defines the partner's outside hole and the universal root deficit:
the hole has degree at least twice its mass, the partner's compulsory source has
no missing edge into the common region, and positive missing mass there forces
the strict deficit floor.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The entire original outside region missed by the saturated partner,
with both original head fibers excluded. -/
def universalPartnerHoleRegion (S : SelectedHighLowStructure W m) (r p : S.I) : Set Ω :=
  ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪ S.rootNeighborhood p)ᶜ

/-- The common region after removing the two original heads and the
partner's entire outside hole region. -/
def universalPartnerCommonRegion (S : SelectedHighLowStructure W m)
    (r p : S.I) : Set Ω :=
  ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪
    S.universalPartnerHoleRegion r p)ᶜ

/-- The original physical charge deficit from the universal whole fiber. -/
def universalRootDeficit (S : SelectedHighLowStructure W m) (r : S.I) (x : Ω) : ℝ :=
  1 - S.rootChargeRow r x

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The partner's entire outside missing region is measurable. -/
theorem measurableSet_universalPartnerHoleRegion (S : SelectedHighLowStructure W m)
    (r p : S.I) : MeasurableSet (S.universalPartnerHoleRegion r p) :=
  (((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).union
    (S.measurableSet_rootNeighborhood p)).compl

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The partner's common outside region is measurable. -/
theorem measurableSet_universalPartnerCommonRegion (S : SelectedHighLowStructure W m)
    (r p : S.I) : MeasurableSet (S.universalPartnerCommonRegion r p) :=
  (((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).union
    (S.measurableSet_universalPartnerHoleRegion r p)).compl

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The original head fibers, entire partner hole, and common outside
region partition the carrier exactly, including exceptional points. -/
theorem universalPartner_regions_partition (S : SelectedHighLowStructure W m)
    (r p : S.I) :
    {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪
      S.universalPartnerHoleRegion r p ∪ S.universalPartnerCommonRegion r p = univ := by
  ext x
  simp only [universalPartnerCommonRegion, mem_union, mem_ofPred_eq,
    mem_univ, iff_true]
  tauto

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The partner's hole and common regions are disjoint even before
passing to almost-everywhere kernel representatives. -/
theorem universalPartner_regions_disjoint (S : SelectedHighLowStructure W m)
    (r p : S.I) :
    Disjoint (S.universalPartnerHoleRegion r p)
      (S.universalPartnerCommonRegion r p) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact hy (Or.inr hx)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The universal original row leaves no positive entire compulsory
source requiring that same atom as its sole missing recipient. -/
theorem universalRoot_compulsorySource_null (S : SelectedHighLowStructure W m)
    (r : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    μ (S.reverseCompulsorySource {r}) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [S.ae_universal_rootNeighborhood_iff r hW hd hgap hN]
    with x hx hs
  obtain ⟨v, hel, hv⟩ := hs.2.2.1
  have hvr : v = r := Finset.mem_singleton.mp (hs.2.2.2 v hel hv)
  rw [hvr] at hv
  exact (not_lt_of_ge hv.2) ((hx.mpr hv.1).2)

/-- The partner's entire compulsory source lies in its entire original
outside hole region almost everywhere, including diffuse source points. -/
theorem ae_partner_compulsorySource_subset_hole
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ, x ∈ S.reverseCompulsorySource {p} →
      x ∈ S.universalPartnerHoleRegion r p := by
  have hr := compl_mem_ae_iff.mpr (hpair.high_head_null hW hd hgap hell)
  have hp := compl_mem_ae_iff.mpr (hpair.symm.high_head_null hW hd hgap hell)
  filter_upwards [hr, hp] with x hxR hxP hs
  have hnotr : S.ρ x ≠ r.val := fun h => hxR ⟨h, hs.1⟩
  have hnotp : S.ρ x ≠ p.val := fun h => hxP ⟨h, hs.1⟩
  obtain ⟨v, hel, hv⟩ := hs.2.2.1
  have hvp : v = p := Finset.mem_singleton.mp (hs.2.2.2 v hel hv)
  rw [hvp] at hv
  change x ∉ {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪
    S.rootNeighborhood p
  intro hmem
  rcases hmem with (h | h) | h
  · exact hnotr h
  · exact hnotp h
  · exact (not_lt_of_ge hv.2) h.2

/-- The original averaged charge row is the homogeneous shifted row
with its actual adjacency charge. -/
theorem ae_universalRootDeficit_eq_shifted_row
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, S.universalRootDeficit r x =
      1 - r.val x - m * (if 0 < r.val x then 1 else 0) := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hIrpos : 0 < μ Ir := (S.hfibers r.val r.property).2.1
  have hrows : ∀ᵐ x ∂μ.restrict Ir,
      chargeKernel W x =ᵐ[μ]
        fun y => r.val y + m * (if 0 < r.val y then 1 else 0) :=
    (S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hs := hW.strict_gap_structure hd hgap
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir →
      PhysicalRepresentative.charge W m p.1 p.2 = S.rootChargeRow r p.2 ∧
      PhysicalRepresentative.charge W m p.1 p.2 = chargeKernel W p.1 p.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hroot hp hIr
    exact ⟨hroot hIr, hp⟩
  have hsections := Measure.ae_ae_of_ae_prod hpair
  obtain ⟨x, hxIr, hxrows, hxsection⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIrpos.ne'
      (hrows.and (ae_restrict_of_ae hsections))
  filter_upwards [hxrows, hxsection] with y hy hp
  have heq := (hp hxIr).1.symm.trans ((hp hxIr).2.trans hy)
  change 1 - S.rootChargeRow r y = _
  rw [heq]
  ring

/-- Every original outside nonneighbor of the saturated partner is HIGH
almost everywhere. The partner is non-HIGH, and a distinct-row zero
pair crosses from LOW to HIGH in the selected model. -/
theorem ae_universalPartnerHole_high
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p), x ∈ S.H := by
  let Ip : Set Ω := {x | S.ρ x = p.val}
  let H := S.universalPartnerHoleRegion r p
  have hIp : MeasurableSet Ip := (S.hfibers p.val p.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hnotP : ∀ᵐ x ∂μ, x ∈ Ip → x ∉ S.H := by
    filter_upwards [compl_mem_ae_iff.mpr
      (hpair.symm.high_head_null hW hd hgap hell)] with x hx hp hh
    exact hx ⟨hp, hh⟩
  have hprod : ∀ᵐ q ∂μ.prod μ, q.1 ∈ Ip → q.2 ∈ H → q.2 ∈ S.H := by
    filter_upwards [S.ae_kernel_eq_fiber_row p.val p.property,
      hW.moment_mem, S.hcoverage, S.hrelation,
      Measure.quasiMeasurePreserving_fst.ae hnotP,
      Measure.quasiMeasurePreserving_snd.ae (S.ae_whole_row_nonneg p hW)]
      with q hrow hnonneg hcover hrelation hnot hpos hqP hqH
    have hnothead : S.ρ q.2 ≠ p.val := by
      intro h
      exact hqH (Or.inl (Or.inr h))
    have hnotN : q.2 ∉ S.rootNeighborhood p := by
      intro h
      exact hqH (Or.inr h)
    have hle : p.val q.2 ≤ 0 := le_of_not_gt (fun h => hnotN ⟨hnothead, h⟩)
    have hpzero : p.val q.2 = 0 := le_antisymm hle hpos
    have hK : shiftedKernel W m q.1 q.2 = 0 := (hrow hqP).trans hpzero
    rcases hcover hK with ⟨v, _, hv1, hv2⟩ | hz
    · have hv : S.ρ q.2 = p.val := hv2.trans (hv1.symm.trans hqP)
      exact False.elim (hnothead hv)
    · rcases hrelation hz with h | h
      · exact False.elim ((hnot hqP) h.1)
      · exact h.1
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers p.val p.property).2.1.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hprod))
  exact (ae_restrict_iff' hH).mpr (hx.mono (fun _ hy hH' => hy (by
    change x ∈ Ip
    exact ‹x ∈ Ip›) hH'))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The saturated partner's original shifted row vanishes throughout
its entire outside hole region, modulo the original law. -/
theorem ae_partner_row_zero_on_universalHole
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p), p.val x = 0 := by
  filter_upwards [ae_restrict_of_ae (S.ae_whole_row_nonneg p hW),
    ae_restrict_mem (S.measurableSet_universalPartnerHoleRegion r p)]
    with x hnonneg hx
  have hnotp : S.ρ x ≠ p.val := by
    intro h
    exact hx (Or.inl (Or.inr h))
  have hnotN : x ∉ S.rootNeighborhood p := by
    intro h
    exact hx (Or.inr h)
  exact le_antisymm (le_of_not_gt (fun h => hnotN ⟨hnotp, h⟩)) hnonneg

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The partner's original shifted row is positive on the common
outside region, before any score or deficit inequality is used. -/
theorem ae_partner_row_pos_on_universalCommon
    (S : SelectedHighLowStructure W m) (r p : S.I) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerCommonRegion r p), 0 < p.val x := by
  filter_upwards [ae_restrict_mem
    (S.measurableSet_universalPartnerCommonRegion r p)] with x hx
  have hnotr : S.ρ x ≠ r.val := by
    intro h
    exact hx (Or.inl (Or.inl h))
  have hnotp : S.ρ x ≠ p.val := by
    intro h
    exact hx (Or.inl (Or.inr h))
  have hnotH : x ∉ S.universalPartnerHoleRegion r p := by
    intro h
    exact hx (Or.inr h)
  have hN : x ∈ S.rootNeighborhood p := by
    by_contra hn
    exact hnotH (by
      change x ∉ {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪
        S.rootNeighborhood p
      intro h
      rcases h with (h | h) | h
      · exact hnotr h
      · exact hnotp h
      · exact hn h)
  exact hN.2

/-- The universal root's original shifted row is positive on both
outside regions under its actual neutral/universal row law. -/
theorem ae_universal_row_pos_on_outside
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ, S.ρ x ≠ r.val → 0 < r.val x := by
  filter_upwards [S.ae_universal_rootNeighborhood_iff r hW hd hgap hN]
    with x hx hnotr
  exact (hx.mpr hnotr).2

/-- On the partner's entire outside hole, the universal root deficit
is exactly the two-head shifted-score deficit. -/
theorem ae_universalRootDeficit_eq_score_on_hole
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalRootDeficit r x = 1 - m - r.val x - p.val x := by
  filter_upwards [ae_restrict_of_ae (S.ae_universalRootDeficit_eq_shifted_row r hW hd hgap),
    ae_restrict_of_ae (S.ae_universal_row_pos_on_outside r hW hd hgap hN),
    S.ae_partner_row_zero_on_universalHole r p hW,
    ae_restrict_mem (S.measurableSet_universalPartnerHoleRegion r p)]
    with x hroot hrpos hpzero hx
  have hnotr : S.ρ x ≠ r.val := by
    intro h
    exact hx (Or.inl (Or.inl h))
  rw [hroot, hpzero]
  simp only [ite_eq_left (hrpos hnotr)]
  ring

/-- On the common outside region, the universal deficit exceeds the
two-head score by the positive partner row. -/
theorem ae_universalRootDeficit_gt_score_on_common
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerCommonRegion r p),
      1 - m - r.val x - p.val x < S.universalRootDeficit r x := by
  filter_upwards [ae_restrict_of_ae (S.ae_universalRootDeficit_eq_shifted_row r hW hd hgap),
    ae_restrict_of_ae (S.ae_universal_row_pos_on_outside r hW hd hgap hN),
    S.ae_partner_row_pos_on_universalCommon r p,
    ae_restrict_mem (S.measurableSet_universalPartnerCommonRegion r p)]
    with x hroot hrpos hppos hx
  have hnotr : S.ρ x ≠ r.val := by
    intro h
    exact hx (Or.inl (Or.inl h))
  rw [hroot]
  simp only [ite_eq_left (hrpos hnotr)]
  linarith

/-- On the partner hole outside its entire original compulsory source,
the selected two-head score floor becomes the universal root deficit
floor. -/
theorem ae_universalRootDeficit_ge_floor_on_hole_compl_source
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict
      (S.universalPartnerHoleRegion r p \ S.reverseCompulsorySource {p}),
      1 + m ≤ S.universalRootDeficit r x := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Ip : Set Ω := {x | S.ρ x = p.val}
  let Sr := S.reverseCompulsorySource {r}
  let Sp := S.reverseCompulsorySource {p}
  let R := (Ir ∪ Ip ∪ Sr ∪ Sp)ᶜ
  let H := S.universalPartnerHoleRegion r p
  have hR : MeasurableSet R :=
    ((((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).union
      (S.measurableSet_reverseCompulsorySource {r})).union
      (S.measurableSet_reverseCompulsorySource {p})).compl
  have hset : MeasurableSet (H \ Sp) :=
    (S.measurableSet_universalPartnerHoleRegion r p).diff
      (S.measurableSet_reverseCompulsorySource {p})
  have hfloor := (ae_restrict_iff' hR).mp
    (hpair.ae_entire_source_score_floor hW hd hgap hell)
  have hnull : ∀ᵐ x ∂μ, x ∉ Sr :=
    compl_mem_ae_iff.mpr (S.universalRoot_compulsorySource_null r hW hd hgap hN)
  have hdef := (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mp
    (S.ae_universalRootDeficit_eq_score_on_hole r p hW hd hgap hN)
  apply (ae_restrict_iff' hset).mpr
  filter_upwards [hfloor, hnull, hdef] with x hf hn hd hx
  have hIr : x ∉ Ir := fun h => hx.1 (Or.inl (Or.inl h))
  have hIp : x ∉ Ip := fun h => hx.1 (Or.inl (Or.inr h))
  have hRmem : x ∈ R := by
    intro h
    rcases h with ((h | h) | h) | h
    · exact hIr h
    · exact hIp h
    · exact hn h
    · exact hx.2 h
  rw [hd hx.1]
  exact hf hRmem

/-- On the common outside region, the original universal deficit has
a strictly stronger floor than the two-head residual score. -/
theorem ae_universalRootDeficit_gt_floor_on_common
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerCommonRegion r p),
      1 + m < S.universalRootDeficit r x := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Ip : Set Ω := {x | S.ρ x = p.val}
  let Sr := S.reverseCompulsorySource {r}
  let Sp := S.reverseCompulsorySource {p}
  let R := (Ir ∪ Ip ∪ Sr ∪ Sp)ᶜ
  let U := S.universalPartnerCommonRegion r p
  have hR : MeasurableSet R :=
    ((((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).union
      (S.measurableSet_reverseCompulsorySource {r})).union
      (S.measurableSet_reverseCompulsorySource {p})).compl
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hfloor := (ae_restrict_iff' hR).mp
    (hpair.ae_entire_source_score_floor hW hd hgap hell)
  have hnull : ∀ᵐ x ∂μ, x ∉ Sr :=
    compl_mem_ae_iff.mpr (S.universalRoot_compulsorySource_null r hW hd hgap hN)
  have hSp := S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell
  have hdef := (ae_restrict_iff' hU).mp
    (S.ae_universalRootDeficit_gt_score_on_common r p hW hd hgap hN)
  apply (ae_restrict_iff' hU).mpr
  filter_upwards [hfloor, hnull, hSp, hdef] with x hf hn hs hd hx
  have hIr : x ∉ Ir := fun h => hx (Or.inl (Or.inl h))
  have hIp : x ∉ Ip := fun h => hx (Or.inl (Or.inr h))
  have hSpnot : x ∉ Sp := fun h => hx (Or.inr (hs h))
  have hRmem : x ∈ R := by
    intro h
    rcases h with ((h | h) | h) | h
    · exact hIr h
    · exact hIp h
    · exact hn h
    · exact hSpnot h
  exact (hf hRmem).trans_lt (hd hx)

/-- A positive original whole atom inside the partner hole has strictly
higher original degree than the saturated partner. The comparison is
obtained from their actual shifted-zero rectangle and HIGH/LOW order. -/
theorem universalPartnerHole_atom_degree_gt
    (S : SelectedHighLowStructure W m) (r p j : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hj : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      x ∈ S.universalPartnerHoleRegion r p) :
    wholeRowDegree p.val < wholeRowDegree j.val := by
  let Ip : Set Ω := {x | S.ρ x = p.val}
  let Ij : Set Ω := {x | S.ρ x = j.val}
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hIp : MeasurableSet Ip := (S.hfibers p.val p.property).1
  have hIj : MeasurableSet Ij := (S.hfibers j.val j.property).1
  have hnotP : ∀ᵐ x ∂μ, x ∈ Ip → x ∉ S.H := by
    filter_upwards [compl_mem_ae_iff.mpr
      (hpair.symm.high_head_null hW hd hgap hell)] with x hx hp hh
    exact hx ⟨hp, hh⟩
  have hdegP := (ae_restrict_iff' hIp).mp
    (wholeRowFiber_degree W m S.ρ p.val (S.hfibers p.val p.property).2.2.2)
  have hdegJ := (ae_restrict_iff' hIj).mp
    (wholeRowFiber_degree W m S.ρ j.val (S.hfibers j.val j.property).2.2.2)
  have hJ := (ae_restrict_iff' hIj).mp hj
  have hprod : ∀ᵐ q ∂μ.prod μ, q.1 ∈ Ip → q.2 ∈ Ij →
      wholeRowDegree p.val < wholeRowDegree j.val := by
    filter_upwards [S.ae_kernel_eq_fiber_row p.val p.property,
      hW.moment_mem, S.hcoverage, S.hrelation,
      Measure.quasiMeasurePreserving_fst.ae hnotP,
      Measure.quasiMeasurePreserving_fst.ae hdegP,
      Measure.quasiMeasurePreserving_snd.ae hdegJ,
      Measure.quasiMeasurePreserving_snd.ae hJ,
      Measure.quasiMeasurePreserving_snd.ae (S.ae_whole_row_nonneg p hW)]
      with q hrow hnonneg hcover hrel hnot hdp hdj hJ' hpos hqP hqJ
    have hqH : q.2 ∈ S.universalPartnerHoleRegion r p := hJ' hqJ
    have hnothead : S.ρ q.2 ≠ p.val := by
      intro h
      exact hqH (Or.inl (Or.inr h))
    have hnotN : q.2 ∉ S.rootNeighborhood p := fun h => hqH (Or.inr h)
    have hle : p.val q.2 ≤ 0 := le_of_not_gt (fun h => hnotN ⟨hnothead, h⟩)
    have hpzero : p.val q.2 = 0 := le_antisymm hle hpos
    have hK : shiftedKernel W m q.1 q.2 = 0 := (hrow hqP).trans hpzero
    rcases hcover hK with ⟨v, _, hv1, hv2⟩ | hz
    · have hv : S.ρ q.2 = p.val := hv2.trans (hv1.symm.trans hqP)
      exact False.elim (hnothead hv)
    · rcases hrel hz with h | h
      · exact False.elim ((hnot hqP) h.1)
      · rw [hdp hqP, hdj hqJ] at h
        exact h.2.2
  obtain ⟨x, hxIp, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers p.val p.property).2.1.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hprod))
  obtain ⟨y, hy, hresult⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers j.val j.property).2.1.ne'
      (ae_restrict_of_ae (hx.mono (fun _ hy => hy hxIp)))
  exact hresult hy

/-- Inside the HIGH partner-hole region, an original missing pair is
exactly a pair in the same positive whole independent fiber. -/
theorem ae_universalPartnerHole_missing_iff_sameAtom
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerHoleRegion r p →
        q.2 ∈ S.universalPartnerHoleRegion r p →
          (adjacencyKernel W q.1 q.2 = 0 ↔ q ∈ S.sameAtomRelation) := by
  let H := S.universalPartnerHoleRegion r p
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hHigh := (ae_restrict_iff' hH).mp
    (S.ae_universalPartnerHole_high r p hpair hW hd hgap hell)
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  filter_upwards [S.ae_zero_iff_sameAtom_or_relation hW hd hgap,
    S.hrelation, hW.moment_mem, hs,
    Measure.quasiMeasurePreserving_fst.ae hHigh,
    Measure.quasiMeasurePreserving_snd.ae hHigh]
    with q hzero hrelation hmem hsupport hhx hhy hx hy
  have hxH : q.1 ∈ S.H := hhx hx
  have hyH : q.2 ∈ S.H := hhy hy
  have hnoRelation : q ∉ actualZeroRelation W m S.ρ := by
    intro hz
    rcases hrelation hz with h | h
    · exact (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hyH h.2.1).elim
    · exact (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hxH h.2.1).elim
  have hzero' : shiftedKernel W m q.1 q.2 = 0 ↔ q ∈ S.sameAtomRelation := by
    constructor
    · intro hK
      rcases hzero.mp hK with h | h
      · exact h
      · exact False.elim (hnoRelation h)
    · exact hzero.mpr ∘ Or.inl
  have hsupport' : adjacencyKernel W q.1 q.2 =
      if 0 < shiftedKernel W m q.1 q.2 then 1 else 0 := hsupport
  constructor
  · intro hA
    have hnpos : ¬0 < shiftedKernel W m q.1 q.2 := by
      intro hpos
      rw [ite_eq_left hpos] at hsupport'
      linarith
    have hK : shiftedKernel W m q.1 q.2 = 0 :=
      le_antisymm (le_of_not_gt hnpos) hmem.1
    exact hzero'.mp hK
  · intro hsame
    have hK := hzero'.mpr hsame
    rw [hsupport', hK]
    norm_num

/-- The original universal-root charge deficit is constant almost
everywhere on each positive whole independent fiber. -/
theorem ae_universalRootDeficit_eq_on_sameAtom
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ q ∂μ.prod μ, q ∈ S.sameAtomRelation →
      S.universalRootDeficit r q.1 = S.universalRootDeficit r q.2 := by
  let : Countable S.I := S.hI.to_subtype
  have hall : ∀ᵐ x ∂μ, ∀ j : S.I, S.ρ x = j.val →
      S.rootChargeRow r x =
        S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl j) := by
    apply ae_all_iff.mpr
    intro j
    exact (ae_restrict_iff' (S.hfibers j.val j.property).1).mp
      (S.ae_atomic_rootChargeRow r j hW hd hgap)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hall,
    Measure.quasiMeasurePreserving_snd.ae hall] with q hx hy hsame
  let j : S.I := ⟨S.ρ q.1, hsame.2⟩
  have hfirst := hx j rfl
  have hsecond := hy j hsame.1.symm
  change 1 - S.rootChargeRow r q.1 = 1 - S.rootChargeRow r q.2
  rw [hfirst, hsecond]

/-- The actual missing H-row deficit is the missing H mass times the
same original whole-part deficit, including the diffuse dust case. -/
theorem ae_universalPartnerHole_missing_deficit_eq_mass_mul
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      (∫ z in S.universalPartnerHoleRegion r p,
        (1 - adjacencyKernel W x z) * S.universalRootDeficit r z ∂μ) =
      (∫ z in S.universalPartnerHoleRegion r p,
        1 - adjacencyKernel W x z ∂μ) * S.universalRootDeficit r x := by
  let H := S.universalPartnerHoleRegion r p
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have hprod : ∀ᵐ q ∂μ.prod μ, q.1 ∈ H → q.2 ∈ H →
      (1 - adjacencyKernel W q.1 q.2) * S.universalRootDeficit r q.2 =
        (1 - adjacencyKernel W q.1 q.2) * S.universalRootDeficit r q.1 := by
    filter_upwards [S.ae_universalPartnerHole_missing_iff_sameAtom
      r p hpair hW hd hgap hell,
      S.ae_universalRootDeficit_eq_on_sameAtom r hW hd hgap, hs]
      with q hmissing hD hsupport hx hy
    by_cases hzero : adjacencyKernel W q.1 q.2 = 0
    · rw [hD ((hmissing hx hy).mp hzero)]
    · have hone : adjacencyKernel W q.1 q.2 = 1 := by
        change adjacencyKernel W q.1 q.2 =
          if 0 < shiftedKernel W m q.1 q.2 then 1 else 0 at hsupport
        by_cases hk : 0 < shiftedKernel W m q.1 q.2
        · simpa only [ite_eq_left hk] using hsupport
        · have hA : adjacencyKernel W q.1 q.2 = 0 := by
            simpa only [ite_eq_right hk] using hsupport
          exact False.elim (hzero hA)
      rw [hone]
      ring
  have hsections := Measure.ae_ae_of_ae_prod hprod
  apply (ae_restrict_iff' hH).mpr
  filter_upwards [hsections] with x hx hxH
  have hrow : ∀ᵐ z ∂μ.restrict H,
      (1 - adjacencyKernel W x z) * S.universalRootDeficit r z =
        (1 - adjacencyKernel W x z) * S.universalRootDeficit r x :=
    (ae_restrict_iff' hH).mpr (hx.mono (fun _ hz hZ => hz hxH hZ))
  rw [integral_congr_ae hrow, integral_mul_const]

/-- The universal root has strict original charge slack on the partner's
entire outside hole. The saturated partner is excluded by definition. -/
theorem ae_rootChargeRow_lt_one_on_universalPartnerHole
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.rootChargeRow r x < 1 := by
  let : Countable S.I := S.hI.to_subtype
  let Ir := {x | S.ρ x = r.val}
  have hIr := S.hfibers r.val r.property
  have hnot (u : S.I) (hru : r ≠ u) (hpu : p ≠ u) :
      ¬S.IsSaturatedAtomPair r u := by
    intro hru'
    rcases hpair.unique hru' hW hd hgap hell with ⟨_, h⟩ | ⟨h, _⟩
    · exact hpu h
    · exact hru h
  have hatom : ∀ᵐ x ∂μ, ∀ u : S.I,
      S.ρ x = u.val →
        x ∈ S.universalPartnerHoleRegion r p → S.rootChargeRow r x < 1 := by
    apply ae_all_iff.mpr
    intro u
    by_cases hru : r = u
    · subst u
      filter_upwards [S.rootChargeRow_zero_off_neighborhood r hW hd hgap] with x hx hxr hh
      exact False.elim (hh (Or.inl (Or.inl hxr)))
    · by_cases hpu : p = u
      · subst u
        filter_upwards [S.rootChargeRow_zero_off_neighborhood r hW hd hgap] with x hx hxp hh
        exact False.elim (hh (Or.inl (Or.inr hxp)))
      · exact (ae_restrict_iff' (S.hfibers u.val u.property).1).mp
          (S.ae_rootChargeRow_lt_one_of_not_saturated r u hru hW hd hgap
            (hnot u hru hpu)) |>.mono (fun _ hx hu hh => hx hu)
  have hdiff : ∀ᵐ x ∂μ, x ∈ S.D → S.rootChargeRow r x < 1 := by
    have hp : ∀ᵐ q ∂μ.prod μ, q.1 ∈ Ir → q.2 ∈ S.D →
        S.rootChargeRow r q.2 < 1 := by
      filter_upwards [S.ae_root_charge r hW hd hgap,
        PhysicalRepresentative.charge_ae_eq W m
          (hW.strict_gap_structure hd hgap).strict_support,
        S.charge_lt_one_on_atom_diffuse hW hd hgap hell r] with q hr he hc hx hy
      rw [← hr hx, he]
      exact hc hx hy
    obtain ⟨x, hx, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hIr.2.1.ne' ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hp)).and
        (ae_restrict_mem hIr.1))
    exact hrow.1.mono (fun _ hy hD => hy hrow.2 hD)
  apply (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mpr
  filter_upwards [hatom, hdiff] with x ha hD hx
  by_cases hxD : x ∈ S.D
  · exact hD hxD
  · have hu : x ∈ ⋃ u ∈ S.I, {y | S.ρ y = u} := by
      simpa only [S.hDeq, mem_compl_iff, not_not] using hxD
    obtain ⟨u, hxu⟩ := mem_iUnion.mp hu
    obtain ⟨huI, hxu⟩ := mem_iUnion.mp hxu
    exact ha ⟨u, huI⟩ hxu hx

/-- On the partner's entire outside hole, original root repricing and
the universal root block give original degree at least twice its mass. -/
theorem ae_universalPartnerHole_degree_ge_twice_mass
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      2 * μ.real {z | S.ρ z = r.val} ≤ ∫ z, adjacencyKernel W x z ∂μ := by
  let I := {x | S.ρ x = r.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hn := S.ae_universal_rootNeighborhood_iff r hW hd hgap hN
  have hsets : S.rootNeighborhood r =ᵐ[μ] Iᶜ := hn.mono (fun _ hx => propext hx)
  have hrow := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.neutral_atom_adjacency r hW hd hgap hN)
  have hsym := adjacencyKernel_symm W
  apply (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mpr
  filter_upwards [S.ae_original_root_degree_ge_mass r hW hd hgap, hn,
    (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mp
      (S.ae_rootChargeRow_lt_one_on_universalPartnerHole r p hpair hW hd hgap hell),
    Measure.ae_ae_of_ae_prod (hrow.and hsym)] with x hl hn hs hr hH
  have hxI : S.ρ x ≠ r.val := by
    intro he
    exact hH (Or.inl (Or.inl he))
  have hbound := hl (hn.mpr hxI) (hs hH)
  rw [Measure.restrict_congr_set hsets] at hbound
  have hroot : (∫ z in I, adjacencyKernel W x z ∂μ) = μ.real I := by
    have heq : ∀ᵐ z ∂μ.restrict I, adjacencyKernel W x z = 1 := by
      filter_upwards [ae_restrict_of_ae hr, ae_restrict_mem hI] with z hz hm
      have he := hz.1 hm
      change adjacencyKernel W z x = (if S.ρ x = r.val then 0 else 1) at he
      exact hz.2.trans (by simpa only [hxI, ite_false] using he)
    rw [integral_congr_ae heq, setIntegral_const, smul_eq_mul, mul_one]
  have hi : Integrable (adjacencyKernel W x) μ := Integrable.of_bound
    ((W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    (Eventually.of_forall (fun z => by
      change ‖W.moment CappedColor.adjacency (x, z)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, z)).1]
      exact (adjacency_moment_mem W (x, z)).2))
  have he := integral_add_compl hI hi
  rw [hroot] at he
  change μ.real I ≤ ∫ z in Iᶜ, adjacencyKernel W x z ∂μ at hbound
  linarith

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem normalizedSetL2_inner_le_of_ae_le_universalHole (s : Set Ω)
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

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem normalizedSetL2_inner_ge_of_ae_ge_universalHole (s : Set Ω)
    (hs : MeasurableSet s) (hspos : 0 < μ s) (f : Lp ℝ 2 μ) (a : ℝ)
    (hf : ∀ᵐ x ∂μ.restrict s, a ≤ f x) :
    a ≤ ⟪f, KernelOperator.normalizedSetL2 s hs⟫ := by
  have hi : Integrable (fun x => f x) (μ.restrict s) :=
    ((Lp.memLp f).integrable (by norm_num)).integrableOn
  have hint := integral_mono_ae (integrable_const a) hi hf
  have hmasspos : 0 < μ.real s := ENNReal.toReal_pos hspos.ne' (measure_ne_top μ _)
  rw [setIntegral_const, smul_eq_mul] at hint
  rw [real_inner_comm, KernelOperator.normalizedSetL2_inner]
  calc
    a = (μ.real s)⁻¹ * (μ.real s * a) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hmasspos.le)

/-- Away from the partner's entire compulsory source, equality in the
universal hole score floor would create a genuine HIGH-to-LOW missing
rectangle and violate the selected strict score comparison. -/
theorem ae_universalRootDeficit_gt_floor_on_hole_compl_source
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict
      (S.universalPartnerHoleRegion r p \ S.reverseCompulsorySource {p}),
      1 + m < S.universalRootDeficit r x := by
  let H := S.universalPartnerHoleRegion r p
  let Sp := S.reverseCompulsorySource {p}
  let R := H \ Sp
  let E := R ∩ S.H ∩ {x | p.val x = 0} ∩ {x | 0 < r.val x} ∩
    {x | -2 * m ≤ p.val x + r.val x}
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hR : MeasurableSet R := hH.diff (S.measurableSet_reverseCompulsorySource {p})
  have hE : MeasurableSet E :=
    ((((hR.inter S.hpartition.1).inter
      (measurableSet_eq_fun (Lp.stronglyMeasurable p.val).measurable measurable_const)).inter
      (measurableSet_lt measurable_const (Lp.stronglyMeasurable r.val).measurable)).inter
      (measurableSet_le measurable_const
        ((Lp.stronglyMeasurable p.val).measurable.add
          (Lp.stronglyMeasurable r.val).measurable)))
  have hEnull : μ E = 0 := by
    by_contra hne
    have hEpos : 0 < μ E := pos_iff_ne_zero.mpr hne
    obtain ⟨H₀, L₀, hH₀, hL₀, hHpos, hHsub, hLpos, hLLow,
      hLheads, hzero, hdegree⟩ :=
      hpair.symm.exists_low_extra_hole_witness hW hd hgap hell E hE hEpos
        (fun x hx => hx.1.1.1.2)
        (fun x hx => by
          have hh := hx.1.1.1.1.1
          have hnotp : S.ρ x ≠ p.val := by
            intro he
            exact hh (Or.inl (Or.inr he))
          refine ⟨hnotp, ?_⟩
          change p.val x ≤ 0
          rw [hx.1.1.2])
        (fun x hx hmissing => not_lt_of_ge hmissing.2 hx.1.2)
        (fun x hx => hx.1.1.1.1.2)
        (fun x hx hhead => by
          have hh := hx.1.1.1.1.1
          rcases hhead with h | h
          · exact hh (Or.inl (Or.inr h))
          · exact hh (Or.inl (Or.inl h)))
    let score : Lp ℝ 2 μ := p.val + r.val
    have hHscore : ∀ᵐ x ∂μ.restrict H₀, -2 * m ≤ score x := by
      filter_upwards [ae_restrict_mem hH₀,
        ae_restrict_of_ae (Lp.coeFn_add p.val r.val)] with x hx hc
      have hs := (hHsub hx).2
      change (p.val + r.val) x = p.val x + r.val x at hc
      change -2 * m ≤ p.val x + r.val x at hs
      simpa only [score, hc] using hs
    have hLscore : ∀ᵐ x ∂μ.restrict L₀, score x ≤ -2 * m := by
      filter_upwards [ae_restrict_mem hL₀,
        ae_restrict_of_ae
          (hpair.symm.ae_score_le_neg_two_m_of_not_high hW hd hgap hell),
        ae_restrict_of_ae (Lp.coeFn_add p.val r.val)] with x hx hs hc
      have hnotH : x ∉ S.H :=
        fun hh => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hh (hLLow hx)
      have hnotp : S.ρ x ≠ p.val := by
        intro h
        exact hLheads hx (Or.inl h)
      have hnotr : S.ρ x ≠ r.val := by
        intro h
        exact hLheads hx (Or.inr h)
      change (p.val + r.val) x = p.val x + r.val x at hc
      simpa only [score, hc] using hs hnotH hnotp hnotr
    have hHavg := normalizedSetL2_inner_ge_of_ae_ge_universalHole
      H₀ hH₀ hHpos score (-2 * m) hHscore
    have hLavg := normalizedSetL2_inner_le_of_ae_le_universalHole
      L₀ hL₀ hLpos score (-2 * m) hLscore
    have hstrict := hpair.symm.score_increases_across_missing_sets hW hd hgap hell
      H₀ L₀ hH₀ hL₀ hHpos hLpos hzero hdegree
    change ⟪score, KernelOperator.normalizedSetL2 H₀ hH₀⟫ <
      ⟪score, KernelOperator.normalizedSetL2 L₀ hL₀⟫ at hstrict
    linarith
  have hnull : ∀ᵐ x ∂μ, x ∉ E := measure_eq_zero_iff_ae_notMem.mp hEnull
  have hhigh := (ae_restrict_iff' hH).mp
    (S.ae_universalPartnerHole_high r p hpair hW hd hgap hell)
  have hdef := (ae_restrict_iff' hH).mp
    (S.ae_universalRootDeficit_eq_score_on_hole r p hW hd hgap hN)
  have hrpos := S.ae_universal_row_pos_on_outside r hW hd hgap hN
  have hpzero := (ae_restrict_iff' hH).mp
    (S.ae_partner_row_zero_on_universalHole r p hW)
  apply (ae_restrict_iff' hR).mpr
  filter_upwards [hnull, hhigh, hdef, hrpos, hpzero] with x hnot hh hd hr hp hx
  have hnotr : S.ρ x ≠ r.val := by
    intro he
    exact hx.1 (Or.inl (Or.inl he))
  have hscore : S.universalRootDeficit r x = 1 - m - p.val x - r.val x := by
    rw [hd hx.1]
    ring
  by_contra hnotgt
  have hmem : x ∈ E := by
    refine ⟨⟨⟨⟨hx, hh hx.1⟩, hp hx.1⟩, hr hnotr⟩, ?_⟩
    rw [hscore] at hnotgt
    change -2 * m ≤ p.val x + r.val x
    linarith
  exact hnot hmem

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- A reverse zero pair into a literal singleton compulsory source can
only come from that original whole atom, including the diffuse case. -/
private theorem ae_reverse_pair_to_singleton_compulsorySource
    (S : SelectedHighLowStructure W m) (p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ∀ᵐ q ∂μ.prod μ, q.2 ∈ S.reverseCompulsorySource {p} →
      q ∈ S.reverseAssignmentRelation → S.ρ q.1 = p.val := by
  let : Countable S.I := S.hI.to_subtype
  let C := S.reverseCompulsorySource {p}
  let Z := (S.D ×ˢ C) ∩ S.reverseAssignmentRelation
  have hZ : MeasurableSet Z :=
    (S.hD.prod (S.measurableSet_reverseCompulsorySource {p})).inter
      S.measurable_oriented_relations.2
  have hsec := (ae_restrict_iff' S.hpartition.1).mp
    S.ae_reverseRawDiffuse_eq_reverseDiffuseSupply
  have hzero : ∀ᵐ x ∂μ, μ {y | (y, x) ∈ Z} = 0 := by
    filter_upwards [hsec] with x hx
    by_cases hc : x ∈ C
    · have hm : μ.real {y | y ∈ S.D ∧ (y, x) ∈ S.reverseAssignmentRelation} = 0 :=
        (hx hc.1).trans hc.2.1
      have hz : μ {y | y ∈ S.D ∧ (y, x) ∈ S.reverseAssignmentRelation} = 0 :=
        (ENNReal.toReal_eq_zero_iff _).mp hm |>.resolve_right (measure_ne_top _ _)
      have he : {y | (y, x) ∈ Z} =
          {y | y ∈ S.D ∧ (y, x) ∈ S.reverseAssignmentRelation} := by
        ext y
        simp only [Z, mem_inter_iff, mem_prod, hc, and_true, mem_ofPred_eq]
      rw [he, hz]
    · have he : {y | (y, x) ∈ Z} = ∅ := by
        ext y
        simp only [Z, mem_inter_iff, mem_prod, hc, and_false, false_and,
          mem_ofPred_eq, mem_empty_iff_false]
      rw [he, measure_empty]
  have hswap : (μ.prod μ) (Prod.swap ⁻¹' Z) = 0 :=
    (Measure.measure_prod_null (measurable_swap hZ)).mpr hzero
  have hz : (μ.prod μ) Z = 0 := by
    simpa only [Measure.measurePreserving_swap.measure_preimage hZ.nullMeasurableSet] using hswap
  have hdiff : ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.D → q.2 ∈ C →
      q ∉ S.reverseAssignmentRelation := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with q hq hD hC hR
    exact hq ⟨⟨hD, hC⟩, hR⟩
  have hrows : ∀ᵐ q ∂μ.prod μ, ∀ u : S.I,
      S.ρ q.1 = u.val → q.2 ∈ S.H →
        (q ∈ S.reverseAssignmentRelation ↔
          q.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ u.val) :=
    ae_all_iff.mpr (fun u => S.ae_reverse_fiber_relation_iff_missing u.val u.property
      (hW.moment_mem.mono (fun _ hp => hp.1)))
  have heligible : ∀ᵐ x ∂μ, ∀ u : S.I,
      u ∉ S.eligibleReverseAtom → S.ρ x = u.val → x ∈ S.H :=
    ae_all_iff.mpr (fun u => by
      by_cases hu : u ∈ S.eligibleReverseAtom
      · exact Eventually.of_forall (fun _ h => False.elim (h hu))
      · filter_upwards [(ae_restrict_iff' (S.hfibers u.val u.property).1).mp
          (S.ae_high_of_not_eligibleReverseAtom u hu)] with x hx _ hxu
        exact hx hxu)
  filter_upwards [hrows, Measure.quasiMeasurePreserving_fst.ae heligible,
    hdiff, S.hrelation] with q hrow hel hd hrel hC hR
  have hnD : q.1 ∉ S.D := fun h => hd h hC hR
  have hU : q.1 ∈ ⋃ u ∈ S.I, {x | S.ρ x = u} := by
    by_contra h
    exact hnD (by rw [S.hDeq]; exact h)
  obtain ⟨u, hu, hqu⟩ := mem_iUnion₂.mp hU
  let v : S.I := ⟨u, hu⟩
  have hv : v ∈ S.eligibleReverseAtom := by
    by_contra hnot
    have hH := hel v hnot hqu
    rcases hrel hR.1 with h | h
    · exact (not_lt_of_ge h.2.2.le) hR.2
    · exact disjoint_left.mp S.hpartition.2.2.2.2.1 hH h.2.1
  have hmissing := (hrow v hqu hC.1).mp hR
  have hvp : v = p := Finset.mem_singleton.mp (hC.2.2.2 v hv hmissing)
  exact hqu.trans (congrArg Subtype.val hvp)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The partner's actual shifted row is constant on each original
positive whole fiber, hence agrees across an old same-atom pair. -/
private theorem ae_partner_row_eq_on_sameAtom
    (S : SelectedHighLowStructure W m) (p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ∀ᵐ q ∂μ.prod μ, q ∈ S.sameAtomRelation → p.val q.1 = p.val q.2 := by
  let : Countable S.I := S.hI.to_subtype
  have hall : ∀ᵐ x ∂μ, ∀ j : S.I,
      S.ρ x = j.val →
        ∃ a : ℝ, p.val x = a ∧
          ∀ᵐ y ∂μ.restrict {y | S.ρ y = j.val}, p.val y = a := by
    apply ae_all_iff.mpr
    intro j
    obtain ⟨a, _, hpa, _, _⟩ := KernelOperator.exists_whole_row_cross_block
      (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ p.val j.val
      (S.hfibers p.val p.property).2.1 (S.hfibers j.val j.property).2.1
      (S.hfibers p.val p.property).2.2.2 (S.hfibers j.val j.property).2.2.2
      (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
      (chargeKernel_measurable W)
      ((shiftedMoment_symm W m).mono (fun _ hp => hp.symm)) hW.moment_mem
    exact ((ae_restrict_iff' (S.hfibers j.val j.property).1).mp hpa).mono
      (fun _ hx hmem => ⟨a, hx hmem, hpa⟩)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hall,
    Measure.quasiMeasurePreserving_snd.ae hall] with q hx hy hsame
  let j : S.I := ⟨S.ρ q.1, hsame.2⟩
  obtain ⟨a, hxa, hyae⟩ := hx j rfl
  have hboth : ∀ᵐ z ∂μ, S.ρ z = j.val → p.val z = a :=
    (ae_restrict_iff' (S.hfibers j.val j.property).1).mp hyae
  have hya := hy j hsame.1.symm
  obtain ⟨b, hyb, hybae⟩ := hya
  have hba : a = b := by
    obtain ⟨z, hz, hza, hzb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers j.val j.property).2.1.ne'
      ((ae_restrict_of_ae hboth).and hybae |>.and
        (ae_restrict_mem (S.hfibers j.val j.property).1))
    exact (hza.1 hz).symm.trans hza.2
  rw [hxa, hyb, hba]

/-- The literal singleton source of the partner has no original missing
edge into the common outside region. This includes its HIGH whole atoms
and diffuse points, using the actual zero-relation cover. -/
theorem ae_partner_compulsorySource_joined_common
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.reverseCompulsorySource {p} →
      q.2 ∈ S.universalPartnerCommonRegion r p →
        adjacencyKernel W q.1 q.2 = 1 := by
  have hsrc := S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell
  have hzero := (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mp
    (S.ae_partner_row_zero_on_universalHole r p hW)
  have hpos := (ae_restrict_iff'
    (S.measurableSet_universalPartnerCommonRegion r p)).mp
      (S.ae_partner_row_pos_on_universalCommon r p)
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsrc,
    Measure.quasiMeasurePreserving_fst.ae hzero,
    Measure.quasiMeasurePreserving_snd.ae hpos,
    S.ae_partner_row_eq_on_sameAtom p hW,
    S.ae_zero_iff_sameAtom_or_relation hW hd hgap,
    S.hrelation,
    hswap.ae (S.ae_reverse_pair_to_singleton_compulsorySource p hW),
    actualZeroRelation_symm W m S.ρ, hW.moment_mem,
    (hW.strict_gap_structure hd hgap).strict_support]
    with q hs hp0 hppos hsame hcover hrel hrev hZsym hmem hsupport hx hy
  have hxH := hs hx
  have hxHigh : q.1 ∈ S.H := hx.1
  have hKpos : 0 < shiftedKernel W m q.1 q.2 := by
    apply lt_of_le_of_ne hmem.1
    intro he
    rcases hcover.mp he.symm with hA | hZ
    · have hpeq := hsame hA
      exact (not_lt_of_ge (by rw [← hpeq, hp0 hxH])) (hppos hy)
    · have hlt : adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) q.2 <
          adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) q.1 := by
        rcases hrel hZ with h | h
        · exact h.2.2
        · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1
            hxHigh h.2.1)
      have hR : (q.2, q.1) ∈ S.reverseAssignmentRelation := ⟨hZsym.mp hZ, hlt⟩
      have hqp := hrev hx hR
      exact hy (Or.inl (Or.inr hqp))
  change W.moment CappedColor.adjacency q = 1
  change 0 < shiftedMoment W m q at hKpos
  simpa only [hKpos, ite_true] using hsupport

/-- The partner's compulsory source has zero original missing mass in
the common outside region, with the recipient coordinate integrated. -/
theorem ae_partner_compulsorySource_commonMissing_zero
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ, x ∈ S.reverseCompulsorySource {p} →
      (∫ z in S.universalPartnerCommonRegion r p,
        1 - adjacencyKernel W x z ∂μ) = 0 := by
  have hjoined := Measure.ae_ae_of_ae_prod
    (S.ae_partner_compulsorySource_joined_common r p hpair hW hd hgap hell)
  filter_upwards [hjoined] with x hx hsource
  have hrow : ∀ᵐ z ∂μ.restrict (S.universalPartnerCommonRegion r p),
      1 - adjacencyKernel W x z = 0 := by
    filter_upwards [ae_restrict_of_ae hx,
      ae_restrict_mem (S.measurableSet_universalPartnerCommonRegion r p)] with z hz hm
    rw [hz hsource hm]
    ring
  rw [integral_congr_ae hrow, integral_zero]

/-- Positive original missing mass into the common outside region forces
the strict universal-root deficit floor on its HIGH hole source. -/
theorem ae_universalPartnerHole_commonMissing_pos_deficit_gt
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      0 < (∫ z in S.universalPartnerCommonRegion r p,
        1 - adjacencyKernel W x z ∂μ) →
          1 + m < S.universalRootDeficit r x := by
  let H := S.universalPartnerHoleRegion r p
  let Sp := S.reverseCompulsorySource {p}
  have hstrict := (ae_restrict_iff'
    ((S.measurableSet_universalPartnerHoleRegion r p).diff
      (S.measurableSet_reverseCompulsorySource {p}))).mp
        (S.ae_universalRootDeficit_gt_floor_on_hole_compl_source
          r p hpair hW hd hgap hell hN)
  have hzero := S.ae_partner_compulsorySource_commonMissing_zero
    r p hpair hW hd hgap hell
  apply (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mpr
  filter_upwards [hstrict, hzero] with x hs hz hx hpos
  by_cases hc : x ∈ Sp
  · rw [hz hc] at hpos
    exact False.elim (lt_irrefl 0 hpos)
  · exact hs ⟨hx, hc⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
