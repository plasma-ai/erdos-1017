module

public import Erdos1017.SelectedModel.Recovery.SelectedReverseRecovery
public import Erdos1017.Exclusions.Common.CompletedAtomicRelationColumns
public import Erdos1017.Exclusions.Common.Flows.SourceRestrictedReverseFlow

/-!
# Source columns of the reverse flow into a plateau

The recipient region `plateauRegion` of a decoded plateau is a finite union of
whole-row fibers, the column mass into it is the indicator of the entire
compulsory source, and for a singleton plateau that source is sent uniformly to
its independent atom.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The actual recipient region of the original decoded plateau. -/
def plateauRegion (R : S.ReverseRecovery) : Set Ω :=
  ⋃ r ∈ R.plateau, {x | S.ρ x = r.val}

/-- A finite union of original measurable whole-row fibers. -/
theorem measurableSet_plateauRegion (R : S.ReverseRecovery) :
    MeasurableSet R.plateauRegion :=
  Finset.measurableSet_biUnion _ (fun r _ => (S.hfibers r.val r.property).1)

/-- Decoding does not change the actual geometric union of recipients. -/
theorem coded_plateau_region_eq (R : S.ReverseRecovery) :
    (⋃ i ∈ R.codePlateau, S.reverseAllAtomFiber R.data.code i) = R.plateauRegion := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (R.active_codePlateau i hi)
    have hc := R.data.label_code i r hr
    have hp : r ∈ R.plateau :=
      (R.data.mem_plateauLabels R.codePlateau r).mpr ⟨i, hi, hr⟩
    exact mem_iUnion₂.mpr ⟨r, hp, by
      simpa only [← hc, S.reverseAllAtomFiber_code] using hx⟩
  · intro hx
    obtain ⟨r, hr, hx⟩ := mem_iUnion₂.mp hx
    have hi := (R.data.code_mem_iff_plateauLabels R.codePlateau R.active_codePlateau r).mpr hr
    exact mem_iUnion₂.mpr ⟨R.data.code r, hi, by
      simpa only [S.reverseAllAtomFiber_code] using hx⟩

/-- The actual column mass into the plateau is the indicator of the entire
original compulsory source, including when that source is null. -/
theorem column_plateau_eq_source (R : S.ReverseRecovery)
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    (fun x => ∫ y in R.plateauRegion, R.flow (y, x) ∂μ) =ᵐ[μ]
      (S.reverseCompulsorySource R.plateau).indicator (fun _ => 1) := by
  have hcol := MissingFlow.CompletedAtomicRelation.setIntegral_column_on_finset
    S.measurable_oriented_relations.2 S.hpartition.1
    (S.measurableSet_reverseAllAtomFiber R.data.code)
    (R.data.raw_feasible hW R.fractions R.feasible)
    (S.reverseAllAtomFiber_pairwise R.data.code) R.codePlateau
  rw [R.coded_plateau_region_eq] at hcol
  filter_upwards [hcol, R.original_entire_source_fractions] with x hx hy
  change (∫ y in R.plateauRegion,
    MissingFlow.CompletedAtomicRelation.density μ S.H S.reverseAssignmentRelation
      (S.reverseAllAtomFiber R.data.code) R.fractions (y, x) ∂μ) = _
  change (∫ y in R.plateauRegion,
    MissingFlow.CompletedAtomicRelation.density μ S.H S.reverseAssignmentRelation
      (S.reverseAllAtomFiber R.data.code) R.fractions (y, x) ∂μ) = _ at hx
  simp only [reverseAssignmentRelation] at hx ⊢
  rw [hx, ← hy]
  by_cases h : x ∈ S.H
  · simp only [MissingFlow.RestrictedAtomicAssignment.liftFraction, indicator_of_mem h]
  · simp only [MissingFlow.RestrictedAtomicAssignment.liftFraction, indicator_of_notMem h,
      Finset.sum_const_zero]

/-- A singleton original plateau has exactly its original coded coordinate. -/
theorem codePlateau_eq_singleton (R : S.ReverseRecovery) (r : S.I)
    (hr : R.plateau = {r}) : R.codePlateau = {R.data.code r} := by
  have h := R.data.plateauLabels_code_image R.codePlateau R.active_codePlateau
  change R.plateau.image R.data.code = R.codePlateau at h
  rw [hr, Finset.image_singleton] at h
  exact h.symm

/-- The singleton's actual lifted assignment is the literal source indicator. -/
theorem singleton_fraction_eq_source (R : S.ReverseRecovery) (r : S.I)
    (hr : R.plateau = {r}) :
    MissingFlow.RestrictedAtomicAssignment.liftFraction S.H R.fractions (R.data.code r) =ᵐ[μ]
      (S.reverseCompulsorySource {r}).indicator (fun _ => 1) := by
  change ∀ᵐ x ∂μ, MissingFlow.RestrictedAtomicAssignment.liftFraction S.H R.fractions
    (R.data.code r) x = (S.reverseCompulsorySource {r}).indicator (fun _ => 1) x
  have h := R.original_entire_source_fractions
  simpa only [R.codePlateau_eq_singleton r hr, Finset.sum_singleton, hr] using h

/-- On an original recipient fiber the constructed product density is
pointwise its uniform density times its actual lifted source fraction. -/
theorem flow_on_original_atom (R : S.ReverseRecovery) (r : S.I) (x y : Ω)
    (hy : S.ρ y = r.val) :
    R.flow (y, x) = (μ.real {z | S.ρ z = r.val})⁻¹ *
      MissingFlow.RestrictedAtomicAssignment.liftFraction S.H R.fractions (R.data.code r) x := by
  let I := S.reverseAllAtomFiber R.data.code
  have hyr : y ∈ I (R.data.code r) := by
    change y ∈ S.reverseAllAtomFiber R.data.code (R.data.code r)
    rw [S.reverseAllAtomFiber_code]
    exact hy
  have hterm (j : ℕ) (hj : j ≠ R.data.code r) :
      MissingFlow.AtomicAssignment.recipientDensity μ (I j) y *
        MissingFlow.RestrictedAtomicAssignment.liftFraction S.H R.fractions j x = 0 := by
    have hyj : y ∉ I j := fun hyj =>
      Set.disjoint_left.mp (S.reverseAllAtomFiber_pairwise R.data.code hj) hyj hyr
    simp only [MissingFlow.AtomicAssignment.recipientDensity, indicator_of_notMem hyj, zero_mul]
  have hd : (y, x) ∉ MissingFlow.CompletedAtomicRelation.diffuseRelation
      S.reverseAssignmentRelation I := fun hp => hp.2.1 (mem_iUnion.mpr ⟨_, hyr⟩)
  change (∑' j, MissingFlow.AtomicAssignment.recipientDensity μ (I j) y *
    MissingFlow.RestrictedAtomicAssignment.liftFraction S.H R.fractions j x) +
      MissingFlow.normalizedDensity μ
        (MissingFlow.CompletedAtomicRelation.diffuseRelation S.reverseAssignmentRelation I) (y, x) = _
  rw [MissingFlow.normalizedDensity_eq_zero_of_notMem _ _ hd, add_zero,
    tsum_eq_single (R.data.code r) hterm]
  rw [MissingFlow.AtomicAssignment.recipientDensity, indicator_of_mem hyr]
  simp only [I, S.reverseAllAtomFiber_code]

private theorem ae_zero_on_rectangle_of_column_zero {q : Ω × Ω → ℝ}
    (hq : Integrable q (μ.prod μ)) (hn : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hc : ∀ᵐ x ∂μ, x ∈ B → (∫ y in A, q (y, x) ∂μ) = 0) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ A → p.2 ∈ B → q p = 0 := by
  let f : Ω × Ω → ℝ := (A ×ˢ B).indicator q
  have hi : Integrable f (μ.prod μ) := hq.indicator (hA.prod hB)
  have hf : ∀ᵐ p ∂μ.prod μ, 0 ≤ f p := by
    filter_upwards [hn] with p hp
    exact indicator_nonneg (fun _ _ => hp) _
  have he : (∫ p, f p ∂μ.prod μ) = 0 := by
    rw [integral_prod_symm _ hi]
    apply integral_eq_zero_of_ae
    filter_upwards [hc] with x hx
    change (∫ y, f (y, x) ∂μ) = 0
    by_cases hxB : x ∈ B
    · have heq : (fun y => f (y, x)) = A.indicator (fun y => q (y, x)) := by
        funext y
        simp only [f, indicator, mem_prod, hxB, and_true]
      rw [heq, integral_indicator hA, hx hxB]
    · have heq : (fun y => f (y, x)) = 0 := by
        funext y
        simp only [f, indicator, mem_prod, hxB, and_false, ite_false, Pi.zero_apply]
      rw [heq]
      change (∫ _ : Ω, (0 : ℝ) ∂μ) = 0
      exact integral_zero _ _
  have hz := (integral_eq_zero_iff_of_nonneg_ae hf hi).mp he
  filter_upwards [hz] with p hp hpa hpb
  simpa only [f, indicator_of_mem (show p ∈ A ×ˢ B from ⟨hpa, hpb⟩), Pi.zero_apply] using hp

/-- Nonzero actual flow enters the original plateau exactly from the entire
compulsory source. This is a product-almost-everywhere statement. -/
theorem ae_plateau_source_iff (R : S.ReverseRecovery)
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ∀ᵐ p ∂μ.prod μ, R.flow p ≠ 0 →
      (p.1 ∈ R.plateauRegion ↔ p.2 ∈ S.reverseCompulsorySource R.plateau) := by
  have hfirst := ae_zero_on_rectangle_of_column_zero R.isFullReverseFlow.integrable R.isFullReverseFlow.nonnegative
    R.measurableSet_plateauRegion R.measurableSet_source.compl (by
      filter_upwards [R.column_plateau_eq_source hW] with x hx hxc
      rw [hx, indicator_of_notMem hxc])
  have hsecond := ae_zero_on_rectangle_of_column_zero R.isFullReverseFlow.integrable R.isFullReverseFlow.nonnegative
    R.measurableSet_plateauRegion.compl R.measurableSet_source (by
      filter_upwards [R.column_plateau_eq_source hW, R.isFullReverseFlow.supply,
        R.isFullReverseFlow.integrable.prod_left_ae] with x hx hs hi hxc
      have hxH : x ∈ S.H := hxc.1
      have hsum := integral_add_compl R.measurableSet_plateauRegion hi
      change (∫ y in R.plateauRegion, R.flow (y, x) ∂μ) +
        (∫ y in R.plateauRegionᶜ, R.flow (y, x) ∂μ) =
        MissingFlow.supply μ R.flow x at hsum
      rw [hx, indicator_of_mem hxc, hs, indicator_of_mem hxH] at hsum
      linarith)
  filter_upwards [hfirst, hsecond] with p hp hq hne
  exact ⟨fun h => by_contra fun hn => hne (hp h hn),
    fun h => by_contra fun hn => hne (hq hn h)⟩

/-- For a singleton plateau the entire physical source is sent uniformly to
its original independent atom. Null compulsory sources require no exception. -/
theorem sourceSlice_singleton (R : S.ReverseRecovery)
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {d c : ℝ}
    (hW : FullStationaryClass d c W m) (r : S.I) (hr : R.plateau = {r}) :
    MissingFlow.sourceSlice (S.reverseCompulsorySource {r}) R.flow =ᵐ[μ.prod μ]
      (fun p => MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = r.val} p.1 *
        (S.reverseCompulsorySource {r}).indicator (fun _ => 1) p.2) := by
  have hprod := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae
    (R.singleton_fraction_eq_source r hr)
  filter_upwards [hprod, R.ae_plateau_source_iff hW] with p hp hs
  have hregion : R.plateauRegion = {x | S.ρ x = r.val} := by
    simp only [plateauRegion, hr, Finset.mem_singleton, iUnion_iUnion_eq_left]
  by_cases hc : p.2 ∈ S.reverseCompulsorySource {r}
  · simp only [MissingFlow.sourceSlice, ite_eq_left hc, indicator_of_mem hc]
    by_cases hi : S.ρ p.1 = r.val
    · have him : p.1 ∈ {x | S.ρ x = r.val} := hi
      change R.flow (p.1, p.2) = _
      rw [R.flow_on_original_atom r p.2 p.1 hi, hp,
        MissingFlow.AtomicAssignment.recipientDensity, indicator_of_mem him,
        indicator_of_mem hc]
    · have hz : R.flow p = 0 := by
        by_contra hne
        have hm := (hs hne).mpr (by simpa only [hr] using hc)
        exact hi (by simpa only [hregion, mem_ofPred_eq] using hm)
      have him : p.1 ∉ {x | S.ρ x = r.val} := hi
      rw [hz, MissingFlow.AtomicAssignment.recipientDensity, indicator_of_notMem him, zero_mul]
  · simp only [MissingFlow.sourceSlice, ite_eq_right hc, indicator_of_notMem hc, mul_zero]

/-- Outside the entire singleton source, the actual remaining flow has no
recipient in that original atom. -/
theorem sourceSlice_compl_avoids_singleton (R : S.ReverseRecovery)
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {d c : ℝ}
    (hW : FullStationaryClass d c W m) (r : S.I) (hr : R.plateau = {r}) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      MissingFlow.sourceSlice (S.reverseCompulsorySource {r})ᶜ R.flow p = 0 := by
  filter_upwards [R.ae_plateau_source_iff hW] with p hp hi
  by_cases hc : p.2 ∈ S.reverseCompulsorySource {r}
  · simp only [MissingFlow.sourceSlice, mem_compl_iff, hc, not_true_eq_false, ite_false]
  · have hz : R.flow p = 0 := by
      by_contra hne
      apply hc
      have hm : p.1 ∈ R.plateauRegion := by
        simp only [plateauRegion, hr, Finset.mem_singleton, iUnion_iUnion_eq_left]
        exact hi
      simpa only [hr] using (hp hne).mp hm
    simp only [MissingFlow.sourceSlice, mem_compl_iff, hc, not_false_eq_true, ite_true, hz]

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
