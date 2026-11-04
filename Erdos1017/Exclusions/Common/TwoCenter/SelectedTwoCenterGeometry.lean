module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterPatterns

/-!
# Retained-source geometry of a two-center recovery

This module defines the remaining reverse half after the finite plateau, shows
the plateau region is the union of the two head fibers, that the retained source
is joined to the remaining half with head/source blocks given by the whole-row
missing incidences, and packages this as retained-source data with receipt
balances.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- The remaining original reverse half after the actual finite plateau. -/
def plateauOther : Set Ω := S.Hᶜ \ R.plateauRegion

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The original reverse relation from the entire compulsory source has
no recipient outside the actual finite plateau. -/
theorem ae_reverse_pair_to_source_plateau {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ∀ᵐ p ∂μ.prod μ, p.2 ∈ S.reverseCompulsorySource R.plateau →
      p ∈ S.reverseAssignmentRelation → p.1 ∈ R.plateauRegion := by
  let : Countable S.I := S.hI.to_subtype
  have hrows : ∀ᵐ p ∂μ.prod μ, ∀ u : S.I,
      S.ρ p.1 = u.val → p.2 ∈ S.H →
        (p ∈ S.reverseAssignmentRelation ↔
          p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ u.val) :=
    ae_all_iff.mpr (fun u => S.ae_reverse_fiber_relation_iff_missing u.val u.property
      (hW.moment_mem.mono (fun _ hp => hp.1)))
  filter_upwards [hrows, Measure.quasiMeasurePreserving_fst.ae (ae_fiber_high_iff (S := S)),
    R.ae_no_diffuse_reverse_pair_to_source, S.hrelation] with p hp he hd hz hc hR
  have hnD : p.1 ∉ S.D := fun h => hd h hc hR
  have hU : p.1 ∈ ⋃ u ∈ S.I, {x | S.ρ x = u} := by
    by_contra h
    exact hnD (by rw [S.hDeq]; exact h)
  obtain ⟨u, hu, hpu⟩ := mem_iUnion₂.mp hU
  let v : S.I := ⟨u, hu⟩
  have hv : v ∈ S.eligibleReverseAtom := by
    by_contra hnot
    have hH := (he v hpu).mpr hnot
    rcases hz hR.1 with h | h
    · exact (not_lt_of_ge h.2.2.le) hR.2
    · exact disjoint_left.mp S.hpartition.2.2.2.2.1 hH h.2.1
  have hmissing := (hp v hpu hc.1).mp hR
  exact mem_iUnion₂.mpr ⟨v, hc.2.2.2 v hv hmissing, hpu⟩

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Every actual plateau fiber lies outside HIGH on a single original-law
common event. Source and heads are disjoint almost everywhere. -/
theorem ae_plateau_not_high : ∀ᵐ x ∂μ, x ∈ R.plateauRegion → x ∉ S.H := by
  filter_upwards [ae_fiber_high_iff (S := S)] with x hx hm
  obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hm
  intro hH
  exact ((hx r hxr).mp hH) (R.plateau_eligible r hr)

/-- The actual complementary-source endpoint keeps all original plateau
heads with their original unit density. -/
theorem retainedWeight_on_plateau {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ∀ᵐ x ∂μ, x ∈ R.plateauRegion → R.retainedWeight x = 1 := by
  have havoid : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R.plateauRegion →
      MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau)ᶜ R.flow p = 0 := by
    filter_upwards [R.ae_plateau_source_iff hW] with p hp hi
    by_cases hc : p.2 ∈ S.reverseCompulsorySource R.plateau
    · simp only [MissingFlow.sourceSlice, mem_compl_iff, hc, not_true_eq_false, ite_false]
    · have hz : R.flow p = 0 := by
        by_contra hne
        exact hc ((hp hne).mp hi)
      simp only [MissingFlow.sourceSlice, hz, ite_self]
  filter_upwards [Measure.ae_ae_of_ae_prod havoid, R.ae_plateau_not_high,
    R.isFullReverseFlow.sourceSlice_compl_supply (S.reverseCompulsorySource R.plateau)]
    with x hx hn hs hi
  have hreceipt : MissingFlow.receipt μ
      (MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau)ᶜ R.flow) x = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hx] with y hy
    exact hy hi
  have hns : x ∉ S.H \ S.reverseCompulsorySource R.plateau := fun h => hn hi h.1
  simp only [retainedWeight, integrableTiltWeight, one_mul]
  change 1 + (MissingFlow.receipt μ _ x - MissingFlow.supply μ _ x) = 1
  rw [hreceipt, hs, indicator_of_notMem hns]
  ring

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Only the original plateau, compulsory source and remaining reverse half
can have nonzero actual retained endpoint weight. -/
theorem retainedWeight_zero_off_plateau :
    ∀ᵐ x ∂μ, x ∉ R.plateauRegion ∪ S.reverseCompulsorySource R.plateau ∪ R.plateauOther →
      R.retainedWeight x = 0 := by
  filter_upwards [R.isFullReverseFlow.sourceSlice_receipt_zero_off_low
    (S.reverseCompulsorySource R.plateau)ᶜ,
    R.isFullReverseFlow.sourceSlice_compl_supply (S.reverseCompulsorySource R.plateau)]
    with x hx hs hnot
  have hni : x ∉ R.plateauRegion := fun h => hnot (Or.inl (Or.inl h))
  have hnC : x ∉ S.reverseCompulsorySource R.plateau := fun h => hnot (Or.inl (Or.inr h))
  have hxH : x ∈ S.H := by
    by_contra h
    exact hnot (Or.inr ⟨h, hni⟩)
  have hnL : x ∉ S.L := fun h => disjoint_left.mp S.hpartition.2.2.2.2.1 hxH h
  simp only [retainedWeight, integrableTiltWeight, one_mul]
  change 1 + (MissingFlow.receipt μ _ x - MissingFlow.supply μ _ x) = 0
  rw [hx hnL, hs, indicator_of_mem (show x ∈ S.H \ S.reverseCompulsorySource R.plateau from ⟨hxH, hnC⟩)]
  ring

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- A plateau head is joined to every different original row outside HIGH. -/
theorem plateau_head_joined_half (r : S.I) (hr : r ∈ R.plateau) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → p.2 ∉ S.H → S.ρ p.2 ≠ r.val →
      adjacencyKernel W p.1 p.2 = 1 := by
  have hel := R.plateau_eligible r hr
  have hnot := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hel
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnot, S.hcoverage, S.hrelation,
    hW.moment_mem, (hW.strict_gap_structure hd hgap).strict_support]
    with p hp hc hz hn hs hi ho hne
  have hpos : 0 < shiftedMoment W m p := by
    apply lt_of_le_of_ne hn.1
    intro he
    rcases hc he.symm with ⟨u, _, hxu, hyu⟩ | hZ
    · exact hne (hyu.trans (hxu.symm.trans hi))
    · rcases hz hZ with h | h
      · exact hp hi h.1
      · exact ho h.1
  change W.moment CappedColor.adjacency p = 1
  simpa only [hpos, ite_true] using hs

/-- The entire retained source is joined to the remaining reverse half.
No bound on its internal independent atoms or clique remainder is used. -/
theorem plateau_source_joined_other {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.reverseCompulsorySource R.plateau → p.2 ∈ R.plateauOther →
      adjacencyKernel W p.1 p.2 = 1 := by
  have hraw := Measure.measurePreserving_swap.quasiMeasurePreserving.ae
    (R.ae_reverse_pair_to_source_plateau hW)
  filter_upwards [hraw, Measure.quasiMeasurePreserving_fst.ae (ae_fiber_high_iff (S := S)),
    Measure.quasiMeasurePreserving_snd.ae (ae_fiber_high_iff (S := S)),
    S.hcoverage, S.hrelation, actualZeroRelation_symm W m S.ρ,
    hW.moment_mem, (hW.strict_gap_structure hd hgap).strict_support]
    with p hp hf hg hc hz hsym hn hs hC hO
  have hpos : 0 < shiftedMoment W m p := by
    apply lt_of_le_of_ne hn.1
    intro he
    rcases hc he.symm with ⟨u, hu, hxu, hyu⟩ | hZ
    · let v : S.I := ⟨u, hu⟩
      exact hO.1 ((hg v hyu).mpr ((hf v hxu).mp hC.1))
    · have hlt : adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 <
          adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 := by
        rcases hz hZ with h | h
        · exact h.2.2
        · exact False.elim (hO.1 h.1)
      have hR : (p.2, p.1) ∈ S.reverseAssignmentRelation := ⟨hsym.mp hZ, hlt⟩
      exact hO.2 (hp hC hR)
  change W.moment CappedColor.adjacency p = 1
  simpa only [hpos, ite_true] using hs

/-- The original head/source blocks are exactly the original whole-row
missing incidences on the entire compulsory source. -/
theorem plateau_head_source_blocks (r : S.I) (hr : r ∈ R.plateau) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → p.2 ∈ S.reverseCompulsorySource R.plateau →
      adjacencyKernel W p.1 p.2 =
        if p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val then 0 else 1 := by
  have hel := R.plateau_eligible r hr
  filter_upwards [S.ae_kernel_eq_fiber_row r.val r.property,
    Measure.quasiMeasurePreserving_snd.ae (ae_fiber_high_iff (S := S)),
    hW.moment_mem, (hW.strict_gap_structure hd hgap).strict_support]
    with p he hf hn hs hi hc
  have hne : S.ρ p.2 ≠ r.val := fun h => ((hf r h).mp hc.1) hel
  by_cases hN : p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val
  · have hzero : shiftedMoment W m p = 0 := le_antisymm ((he hi).trans_le hN.2) hn.1
    change W.moment CappedColor.adjacency p = _
    simpa only [hzero, hN, lt_self_iff_false, ite_false, ite_true] using hs
  · have hpos : 0 < shiftedMoment W m p := by
      apply lt_of_le_of_ne hn.1
      intro hzero
      exact hN ⟨hne, (he hi).symm.trans_le hzero.symm.le⟩
    change W.moment CappedColor.adjacency p = _
    simpa only [hpos, hN, ite_true, ite_false] using hs

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The actual plateau region is the union of the two original head fibers. -/
theorem plateauRegion_eq_pair (r u : S.I) (hp : R.plateau = {r, u}) :
    R.plateauRegion = {x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val} := by
  ext x
  simp only [plateauRegion, hp, Finset.mem_insert, Finset.mem_singleton,
    iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left, mem_union, mem_ofPred_eq]

/-- Concrete retained-source data for the same original two-head recovery.
The three patterns may be null and need not be independent sets. -/
structure TwoCenterRetainedGeometry (r u : S.I) : Prop where
  measurable_patterns : MeasurableSet (S.twoCenterPrivate r u) ∧
    MeasurableSet (S.twoCenterPrivate u r) ∧ MeasurableSet (S.twoCenterShared r u)
  measurable_other : MeasurableSet R.plateauOther
  source_partition : S.reverseCompulsorySource {r, u} =
    S.twoCenterPrivate r u ∪ S.twoCenterPrivate u r ∪ S.twoCenterShared r u
  patterns_disjoint : Disjoint (S.twoCenterPrivate r u) (S.twoCenterPrivate u r) ∧
    Disjoint (S.twoCenterPrivate r u) (S.twoCenterShared r u) ∧
    Disjoint (S.twoCenterPrivate u r) (S.twoCenterShared r u)
  heads_disjoint : Disjoint {x | S.ρ x = r.val} {x | S.ρ x = u.val}
  head_source_disjoint_ae : ∀ᵐ x ∂μ, x ∈ S.reverseCompulsorySource {r, u} →
    S.ρ x ≠ r.val ∧ S.ρ x ≠ u.val
  integrable_weight : Integrable R.retainedWeight μ
  weight_heads : ∀ᵐ x ∂μ, S.ρ x = r.val ∨ S.ρ x = u.val → R.retainedWeight x = 1
  weight_source : ∀ᵐ x ∂μ, x ∈ S.reverseCompulsorySource {r, u} → R.retainedWeight x = 1
  weight_off : ∀ᵐ x ∂μ,
    x ∉ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val}) ∪
      S.reverseCompulsorySource {r, u} ∪ R.plateauOther → R.retainedWeight x = 0
  zero_first_head : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = r.val →
    adjacencyKernel W p.1 p.2 = 0
  zero_second_head : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → S.ρ p.2 = u.val →
    adjacencyKernel W p.1 p.2 = 0
  joined_heads : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = u.val →
    adjacencyKernel W p.1 p.2 = 1
  first_head_source : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
    p.2 ∈ S.reverseCompulsorySource {r, u} → adjacencyKernel W p.1 p.2 =
      if p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val then 0 else 1
  second_head_source : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val →
    p.2 ∈ S.reverseCompulsorySource {r, u} → adjacencyKernel W p.1 p.2 =
      if p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ u.val then 0 else 1
  joined_heads_other : ∀ᵐ p ∂μ.prod μ, (S.ρ p.1 = r.val ∨ S.ρ p.1 = u.val) →
    p.2 ∈ R.plateauOther → adjacencyKernel W p.1 p.2 = 1
  joined_source_other : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.reverseCompulsorySource {r, u} →
    p.2 ∈ R.plateauOther → adjacencyKernel W p.1 p.2 = 1
  receipt_balances : 0 ≤ R.sharedReceipt r u ∧ 0 ≤ R.sharedReceipt u r ∧
    R.sharedReceipt r u + R.sharedReceipt u r = μ.real (S.twoCenterShared r u) ∧
    μ.real {x | S.ρ x = r.val} + μ.real (S.twoCenterPrivate r u) + R.sharedReceipt r u = R.height ∧
    μ.real {x | S.ρ x = u.val} + μ.real (S.twoCenterPrivate u r) + R.sharedReceipt u r = R.height

/-- All two-center retained-source geometry and actual receipt balances
are derived from the original selected recovery. -/
theorem twoCenter_retained_geometry (r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u}) : R.TwoCenterRetainedGeometry r u := by
  have hr : r ∈ R.plateau := by rw [hp]; simp
  have hu : u ∈ R.plateau := by rw [hp]; simp
  have hregion := R.plateauRegion_eq_pair r u hp
  have hregion_mem (x : Ω) (hx : S.ρ x = r.val ∨ S.ρ x = u.val) : x ∈ R.plateauRegion := by
    rw [hregion]
    exact hx
  have hweight_source : ∀ᵐ x ∂μ, x ∈ S.reverseCompulsorySource {r, u} → R.retainedWeight x = 1 := by
    simpa only [hp] using R.retainedWeight_on_source
  have hhead_disjoint : Disjoint {x | S.ρ x = r.val} {x | S.ρ x = u.val} := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hru (Subtype.ext (hx.symm.trans hy))
  refine {
    measurable_patterns := R.measurableSet_twoCenter_patterns r u hp
    measurable_other := S.hpartition.1.compl.diff R.measurableSet_plateauRegion
    source_partition := S.twoCenter_source_partition r u
    patterns_disjoint := S.twoCenter_patterns_disjoint r u
    heads_disjoint := hhead_disjoint
    head_source_disjoint_ae := ?_
    integrable_weight := integrableTiltWeight_integrable _
      (MissingFlow.integrable_direction (MissingFlow.integrable_sourceSlice
        R.isFullReverseFlow.integrable R.measurableSet_source.compl)) 1
    weight_heads := ?_
    weight_source := hweight_source
    weight_off := ?_
    zero_first_head := singleton_zero_II r
    zero_second_head := singleton_zero_II u
    joined_heads := ?_
    first_head_source := ?_
    second_head_source := ?_
    joined_heads_other := ?_
    joined_source_other := ?_
    receipt_balances := R.twoCenter_receipt_balances r u hru hp
  }
  · filter_upwards [R.ae_plateau_not_high] with x hx hc
    have hxH : x ∈ S.H := hc.1
    exact ⟨fun h => hx (hregion_mem x (Or.inl h)) hxH,
      fun h => hx (hregion_mem x (Or.inr h)) hxH⟩
  · filter_upwards [R.retainedWeight_on_plateau hW] with x hx hi
    exact hx (hregion_mem x hi)
  · simpa only [hregion, hp] using R.retainedWeight_zero_off_plateau
  · filter_upwards [R.plateau_head_joined_half r hr hW hd hgap,
      Measure.quasiMeasurePreserving_snd.ae R.ae_plateau_not_high] with p hG hn hx hy
    exact hG hx (hn (hregion_mem p.2 (Or.inr hy)))
      (fun h => hru (Subtype.ext (h.symm.trans hy)))
  · simpa only [hp] using R.plateau_head_source_blocks r hr hW hd hgap
  · simpa only [hp] using R.plateau_head_source_blocks u hu hW hd hgap
  · filter_upwards [R.plateau_head_joined_half r hr hW hd hgap,
      R.plateau_head_joined_half u hu hW hd hgap] with p hR hU hx hy
    rcases hx with hx | hx
    · exact hR hx hy.1 (fun h => hy.2 (hregion_mem p.2 (Or.inl h)))
    · exact hU hx hy.1 (fun h => hy.2 (hregion_mem p.2 (Or.inr h)))
  · simpa only [hp] using R.plateau_source_joined_other hW hd hgap

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
