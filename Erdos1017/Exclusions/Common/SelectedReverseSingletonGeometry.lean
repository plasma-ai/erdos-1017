module

public import Erdos1017.Exclusions.Common.SelectedReverseSourceColumns
public import Erdos1017.Exclusions.Common.TwoCenter.OneCenterSourceCredit

/-!
# Geometry of a singleton reverse source

The entire singleton compulsory source misses its atom pointwise and is disjoint
from it, the atom and that source are joined to the rest of the reverse half,
and the complementary flow retains both with weight one while removing every
other high point.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The entire singleton source misses that same original atom pointwise.
The nonempty allowed-neighbor clause is essential here. -/
theorem mem_singleton_compulsorySource_missing (r : S.I) {x : Ω}
    (hx : x ∈ S.reverseCompulsorySource {r}) :
    x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val := by
  obtain ⟨u, hu, hxu⟩ := hx.2.2.1
  have hur : u = r := Finset.mem_singleton.mp (hx.2.2.2 u hu hxu)
  exact hur ▸ hxu

/-- The literal singleton source and its original atom are disjoint,
including their exceptional null points. -/
theorem disjoint_singleton_fiber_source (r : S.I) :
    Disjoint {x | S.ρ x = r.val} (S.reverseCompulsorySource {r}) := by
  apply disjoint_left.mpr
  intro x hx hc
  exact (S.mem_singleton_compulsorySource_missing r hc).1 hx

namespace ReverseRecovery

variable (R : S.ReverseRecovery)

/-- The remainder of the original reverse half, after the retained atom. -/
def singletonOther (r : S.I) : Set Ω := S.Hᶜ \ {x | S.ρ x = r.val}

/-- The actual unchanged original-law endpoint weight after removing every
source outside the compulsory source and retaining the source itself. -/
def retainedWeight : Ω → ℝ :=
  integrableTiltWeight (MissingFlow.direction μ
    (MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau)ᶜ R.flow)) 1

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Zero diffuse section mass eliminates actual reverse-relation pairs
from the diffuse remainder into the entire compulsory source. -/
theorem ae_no_diffuse_reverse_pair_to_source :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.reverseCompulsorySource R.plateau →
      p ∉ S.reverseAssignmentRelation := by
  let Z := (S.D ×ˢ S.reverseCompulsorySource R.plateau) ∩ S.reverseAssignmentRelation
  have hZ : MeasurableSet Z :=
    (S.hD.prod R.measurableSet_source).inter S.measurable_oriented_relations.2
  have hsec := (ae_restrict_iff' S.hpartition.1).mp
    S.ae_reverseRawDiffuse_eq_reverseDiffuseSupply
  have hzero : ∀ᵐ x ∂μ, μ {y | (y, x) ∈ Z} = 0 := by
    filter_upwards [hsec] with x hx
    by_cases hc : x ∈ S.reverseCompulsorySource R.plateau
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
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with p hp hD hC hR
  exact hp ⟨⟨hD, hC⟩, hR⟩

/-- Every actual reverse-relation pair from the entire singleton source
has its recipient in that original atom. No flow-support hypothesis is used. -/
theorem ae_reverse_pair_to_singleton_source (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) (hr : R.plateau = {r}) :
    ∀ᵐ p ∂μ.prod μ, p.2 ∈ S.reverseCompulsorySource {r} →
      p ∈ S.reverseAssignmentRelation → S.ρ p.1 = r.val := by
  let : Countable S.I := S.hI.to_subtype
  have hrows : ∀ᵐ p ∂μ.prod μ, ∀ u : S.I,
      S.ρ p.1 = u.val → p.2 ∈ S.H →
        (p ∈ S.reverseAssignmentRelation ↔
          p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ u.val) :=
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
    R.ae_no_diffuse_reverse_pair_to_source, S.hrelation] with p hp he hd hz hc hR
  have hC : p.2 ∈ S.reverseCompulsorySource R.plateau := by simpa only [hr] using hc
  have hnD : p.1 ∉ S.D := fun h => hd h hC hR
  have hU : p.1 ∈ ⋃ u ∈ S.I, {x | S.ρ x = u} := by
    by_contra h
    exact hnD (by rw [S.hDeq]; exact h)
  obtain ⟨u, hu, hpu⟩ := mem_iUnion₂.mp hU
  let v : S.I := ⟨u, hu⟩
  have hv : v ∈ S.eligibleReverseAtom := by
    by_contra hnot
    have hH := he v hnot hpu
    rcases hz hR.1 with h | h
    · exact (not_lt_of_ge h.2.2.le) hR.2
    · exact disjoint_left.mp S.hpartition.2.2.2.2.1 hH h.2.1
  have hmissing := (hp v hpu hc.1).mp hR
  have hvr : v = r := Finset.mem_singleton.mp (hc.2.2.2 v hv hmissing)
  exact hpu.trans (congrArg Subtype.val hvr)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- On one original-law common event, HIGH membership is constant on every
positive whole fiber, and is exactly ineligibility for reverse recipients. -/
theorem ae_fiber_high_iff :
    ∀ᵐ x ∂μ, ∀ u : S.I, S.ρ x = u.val →
      (x ∈ S.H ↔ u ∉ S.eligibleReverseAtom) := by
  let : Countable S.I := S.hI.to_subtype
  apply ae_all_iff.mpr
  intro u
  by_cases hu : u ∈ S.eligibleReverseAtom
  · filter_upwards [(ae_restrict_iff' (S.hfibers u.val u.property).1).mp hu] with x hx hxu
    exact ⟨fun h => False.elim (hx hxu h), fun h => False.elim (h hu)⟩
  · filter_upwards [(ae_restrict_iff' (S.hfibers u.val u.property).1).mp
      (S.ae_high_of_not_eligibleReverseAtom u hu)] with x hx hxu
    exact ⟨fun _ => hu, fun _ => hx hxu⟩

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The actual original atom remains an independent block. -/
theorem singleton_zero_II (r : S.I) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = 0 := by
  have h := (S.hfibers r.val r.property).2.2.1
  rw [Measure.prod_restrict] at h
  exact (ae_restrict_iff' ((S.hfibers r.val r.property).1.prod
    (S.hfibers r.val r.property).1)).mp h |>.mono (fun _ hp hx hy => hp ⟨hx, hy⟩)

/-- The entire singleton compulsory source is missing from its original
atom; nonnegativity converts the actual homogeneous row bound to zero. -/
theorem singleton_zero_IC (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → p.2 ∈ S.reverseCompulsorySource {r} →
      adjacencyKernel W p.1 p.2 = 0 := by
  filter_upwards [S.ae_kernel_eq_fiber_row r.val r.property, hW.moment_mem,
    (hW.strict_gap_structure hd hgap).strict_support] with p hp hn hs hi hc
  have hzero : shiftedMoment W m p = 0 :=
    le_antisymm ((hp hi).trans_le (S.mem_singleton_compulsorySource_missing r hc).2) hn.1
  change W.moment CappedColor.adjacency p = 0
  simpa only [hzero, lt_self_iff_false, ite_false] using hs

/-- The eligible original atom is joined to every other point of the
reverse half, modulo original product null sets. -/
theorem singleton_joined_IO (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hr : R.plateau = {r}) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → p.2 ∈ singletonOther (S := S) r →
      adjacencyKernel W p.1 p.2 = 1 := by
  have hel := R.plateau_eligible r (by rw [hr]; exact Finset.mem_singleton_self _)
  have hnot := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hel
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnot, S.hcoverage, S.hrelation,
    hW.moment_mem, (hW.strict_gap_structure hd hgap).strict_support]
    with p hp hc hz hn hs hi ho
  have hpnot := hp hi
  have hpos : 0 < shiftedMoment W m p := by
    apply lt_of_le_of_ne hn.1
    intro he
    rcases hc he.symm with ⟨u, _, hxu, hyu⟩ | hZ
    · exact ho.2 (hyu.trans (hxu.symm.trans hi))
    · rcases hz hZ with h | h
      · exact hpnot h.1
      · exact ho.1 h.1
  change W.moment CappedColor.adjacency p = 1
  simpa only [hpos, ite_true] using hs

/-- The entire singleton source is joined to the remaining reverse half.
Both countable atoms and the actual diffuse remainder have been exhausted. -/
theorem singleton_joined_CO (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hr : R.plateau = {r}) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.reverseCompulsorySource {r} →
      p.2 ∈ singletonOther (S := S) r → adjacencyKernel W p.1 p.2 = 1 := by
  have hraw := Measure.measurePreserving_swap.quasiMeasurePreserving.ae
    (R.ae_reverse_pair_to_singleton_source r hW hr)
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

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The complementary-source endpoint retains the original atom with
weight exactly one; the complementary flow cannot receive there. -/
theorem retainedWeight_on_singleton_atom (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hr : R.plateau = {r}) :
    ∀ᵐ x ∂μ, S.ρ x = r.val → R.retainedWeight x = 1 := by
  have havoid := Measure.ae_ae_of_ae_prod (R.sourceSlice_compl_avoids_singleton hW r hr)
  have hel := R.plateau_eligible r (by rw [hr]; exact Finset.mem_singleton_self _)
  have hnot := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hel
  filter_upwards [havoid, hnot,
    R.isFullReverseFlow.sourceSlice_compl_supply (S.reverseCompulsorySource {r})]
    with x hx hn hs hi
  have hreceipt : MissingFlow.receipt μ
      (MissingFlow.sourceSlice (S.reverseCompulsorySource {r})ᶜ R.flow) x = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hx] with y hy
    exact hy hi
  have hns : x ∉ S.H \ S.reverseCompulsorySource {r} := fun h => hn hi h.1
  simp only [retainedWeight, hr, integrableTiltWeight, one_mul]
  change 1 + (MissingFlow.receipt μ _ x - MissingFlow.supply μ _ x) = 1
  rw [hreceipt, hs, indicator_of_notMem hns]
  ring

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The entire compulsory source is retained with original weight one,
including when its original measure is zero. -/
theorem retainedWeight_on_source :
    ∀ᵐ x ∂μ, x ∈ S.reverseCompulsorySource R.plateau → R.retainedWeight x = 1 := by
  filter_upwards [R.isFullReverseFlow.sourceSlice_receipt_zero_off_low
    (S.reverseCompulsorySource R.plateau)ᶜ,
    R.isFullReverseFlow.sourceSlice_compl_supply (S.reverseCompulsorySource R.plateau)]
    with x hx hs hc
  have hnL : x ∉ S.L := fun h => disjoint_left.mp S.hpartition.2.2.2.2.1 hc.1 h
  have hns : x ∉ S.H \ S.reverseCompulsorySource R.plateau := fun h => h.2 hc
  simp only [retainedWeight, integrableTiltWeight, one_mul]
  change 1 + (MissingFlow.receipt μ _ x - MissingFlow.supply μ _ x) = 1
  rw [hx hnL, hs, indicator_of_notMem hns]
  ring

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Every original HIGH point outside the retained compulsory source is
removed by the actual complementary flow. -/
theorem retainedWeight_zero_off_singleton (r : S.I) (hr : R.plateau = {r}) :
    ∀ᵐ x ∂μ, x ∉ {x | S.ρ x = r.val} ∪ S.reverseCompulsorySource {r} ∪
      singletonOther (S := S) r → R.retainedWeight x = 0 := by
  filter_upwards [R.isFullReverseFlow.sourceSlice_receipt_zero_off_low
    (S.reverseCompulsorySource R.plateau)ᶜ,
    R.isFullReverseFlow.sourceSlice_compl_supply (S.reverseCompulsorySource R.plateau)]
    with x hx hs hnot
  have hni : S.ρ x ≠ r.val := fun h => hnot (Or.inl (Or.inl h))
  have hnC : x ∉ S.reverseCompulsorySource {r} := fun h => hnot (Or.inl (Or.inr h))
  have hxH : x ∈ S.H := by
    by_contra h
    exact hnot (Or.inr ⟨h, hni⟩)
  have hnL : x ∉ S.L := fun h => disjoint_left.mp S.hpartition.2.2.2.2.1 hxH h
  have hmem : x ∈ S.H \ S.reverseCompulsorySource R.plateau :=
    ⟨hxH, by simpa only [hr] using hnC⟩
  simp only [retainedWeight, integrableTiltWeight, one_mul]
  change 1 + (MissingFlow.receipt μ _ x - MissingFlow.supply μ _ x) = 0
  rw [hx hnL, hs, indicator_of_mem hmem]
  ring

/-- The same constructed recovery supplies every concrete joined-block and
retained-weight hypothesis of the one-center source calculus. -/
theorem singleton_retainedSourceGeometry (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hr : R.plateau = {r}) :
    MissingFlow.OneCenter.RetainedSourceGeometry (μ := μ) (adjacencyKernel W)
      {x | S.ρ x = r.val} (S.reverseCompulsorySource {r})
      (singletonOther (S := S) r) R.retainedWeight := by
  have hC : MeasurableSet (S.reverseCompulsorySource {r}) := by
    simpa only [hr] using R.measurableSet_source
  refine {
    measurable_I := (S.hfibers r.val r.property).1
    measurable_C := hC
    measurable_O := S.hpartition.1.compl.diff (S.hfibers r.val r.property).1
    positive_I := ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne' (measure_ne_top _ _)
    disjoint_IC := S.disjoint_singleton_fiber_source r
    disjoint_IO := disjoint_left.mpr (fun _ hi ho => ho.2 hi)
    disjoint_CO := disjoint_left.mpr (fun _ hc ho => ho.1 hc.1)
    integrable_weight := integrableTiltWeight_integrable _
      (MissingFlow.integrable_direction (MissingFlow.integrable_sourceSlice
        R.isFullReverseFlow.integrable R.measurableSet_source.compl)) 1
    weight_I := R.retainedWeight_on_singleton_atom r hW hr
    weight_C := ?_
    weight_off := R.retainedWeight_zero_off_singleton r hr
    zero_II := singleton_zero_II r
    zero_IC := singleton_zero_IC r hW hd hgap
    joined_IO := R.singleton_joined_IO r hW hd hgap hr
    joined_CO := R.singleton_joined_CO r hW hd hgap hr
  }
  simpa only [hr] using R.retainedWeight_on_source

end ReverseRecovery

end Erdos1017.CappedModel.SelectedHighLowStructure
