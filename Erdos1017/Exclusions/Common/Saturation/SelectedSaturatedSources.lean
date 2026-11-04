module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairOrientation
public import Erdos1017.Exclusions.Common.SelectedReverseSingletonGeometry

/-!
# Compulsory sources of a saturated pair

The compulsory source is measurable for every finite set of whole atoms,
distinct singleton compulsory sources are disjoint, either head of a saturated
pair is eligible as a reverse recipient atom, and every compulsory source is
null within a saturated head fiber.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The literal compulsory source is measurable for every finite set of
original whole atoms, independently of a recovered assignment. -/
theorem measurableSet_reverseCompulsorySource (S : SelectedHighLowStructure W m)
    (P : Finset S.I) : MeasurableSet (S.reverseCompulsorySource P) := by
  classical
  let _ : Countable S.I := S.hI.to_subtype
  have hN (r : S.I) : MeasurableSet (KernelOperator.wholeFiberMissingSet S.ρ r.val) :=
    KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ r.val
  have hsome : MeasurableSet
      {x | ∃ r : S.I, r ∈ S.eligibleReverseAtom ∧
        x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val} := by
    have heq : {x | ∃ r : S.I, r ∈ S.eligibleReverseAtom ∧
        x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val} =
        ⋃ r : S.I, if r ∈ S.eligibleReverseAtom then
          KernelOperator.wholeFiberMissingSet S.ρ r.val else ∅ := by
      ext x
      constructor
      · rintro ⟨r, hr, hx⟩
        exact mem_iUnion.mpr ⟨r, by simpa [hr]⟩
      · intro hx
        obtain ⟨r, hr⟩ := mem_iUnion.mp hx
        by_cases hel : r ∈ S.eligibleReverseAtom
        · exact ⟨r, hel, by simpa [hel] using hr⟩
        · simp [hel] at hr
    rw [heq]
    exact MeasurableSet.iUnion (fun r => by
      by_cases hel : r ∈ S.eligibleReverseAtom <;> simp [hel, hN r])
  have hall : MeasurableSet
      {x | ∀ r : S.I, r ∈ S.eligibleReverseAtom →
        x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val → r ∈ P} := by
    have heq : {x | ∀ r : S.I, r ∈ S.eligibleReverseAtom →
        x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val → r ∈ P} =
        ⋂ r : S.I, if r ∈ S.eligibleReverseAtom ∧ r ∉ P then
          (KernelOperator.wholeFiberMissingSet S.ρ r.val)ᶜ else univ := by
      ext x
      constructor
      · intro hx
        apply mem_iInter.mpr
        intro r
        by_cases h : r ∈ S.eligibleReverseAtom ∧ r ∉ P
        · simpa [h] using (fun hxr => h.2 (hx r h.1 hxr))
        · simp [h]
      · intro hx r hel hxr
        by_contra hn
        have hr := mem_iInter.mp hx r
        have hnotmem : x ∉ KernelOperator.wholeFiberMissingSet S.ρ r.val := by
          simpa [hel, hn] using hr
        exact hnotmem hxr
    rw [heq]
    exact MeasurableSet.iInter (fun r => by
      by_cases h : r ∈ S.eligibleReverseAtom ∧ r ∉ P <;> simp [h, hN r])
  exact S.hpartition.1.inter
    ((measurableSet_eq_fun S.measurable_reverseDiffuseSupply measurable_const).inter
      (hsome.inter hall))

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Distinct singleton compulsory sources are disjoint, including their
exceptional points. Their eligible missing labels cannot both be forced
to different singletons. -/
theorem disjoint_singleton_compulsorySources (S : SelectedHighLowStructure W m)
    (r u : S.I) (hru : r ≠ u) :
    Disjoint (S.reverseCompulsorySource {r}) (S.reverseCompulsorySource {u}) := by
  apply disjoint_left.mpr
  intro x hx hu
  obtain ⟨v, hv, hxv⟩ := hu.2.2.1
  have hvr : v = r := Finset.mem_singleton.mp (hx.2.2.2 v hv hxv)
  have hvu : v = u := Finset.mem_singleton.mp (hu.2.2.2 v hv hxv)
  exact hru (hvr.symm.trans hvu)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Either head of an actual saturated pair is eligible as an original
reverse recipient atom. -/
theorem IsSaturatedAtomPair.head_eligibleReverseAtom
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) : r ∈ S.eligibleReverseAtom := by
  change ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∉ S.H
  have hzero := hpair.high_head_null hW hd hgap hell
  rw [measure_eq_zero_iff_ae_notMem] at hzero
  exact (ae_restrict_iff' ((S.hfibers r.val r.property).1)).mpr
    (hzero.mono (fun x hx hxr hHmem => hx ⟨hxr, hHmem⟩))

/-- Every compulsory source is null within an actual saturated head
fiber; this applies to both heads and arbitrary finite source labels. -/
theorem IsSaturatedAtomPair.head_compulsorySource_null
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (P : Finset S.I) :
    μ ({x | S.ρ x = r.val} ∩ S.reverseCompulsorySource P) = 0 := by
  apply le_zero_iff.mp
  calc
    μ ({x | S.ρ x = r.val} ∩ S.reverseCompulsorySource P)
        ≤ μ ({x | S.ρ x = r.val} ∩ S.H) := measure_mono (by
          intro x hx
          exact ⟨hx.1, hx.2.1⟩)
    _ = 0 := hpair.high_head_null hW hd hgap hell

end Erdos1017.CappedModel.SelectedHighLowStructure
