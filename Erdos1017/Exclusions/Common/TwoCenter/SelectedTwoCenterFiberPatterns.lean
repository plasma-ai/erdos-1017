module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterGeometry
public import Erdos1017.SelectedModel.Structure.WholeRowCrossBlocks

/-!
# Fiber patterns of a two-center recovery

Membership in each missing-label and compulsory-source predicate is constant on
every positive whole fiber of the original row, modulo its restricted law, so
every original atom occupies one head or source pattern or lies entirely outside
both heads and the compulsory source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The actual fixed diffuse LOW zero section of an original whole row. -/
def fiberDiffuseMass (S : SelectedHighLowStructure W m) (k : S.I) : ℝ :=
  μ.real {y | y ∈ S.D ∩ S.L ∧ k.val y = 0 ∧ k.val ≠ S.ρ y}

/-- Actual original missing-label incidence on a positive whole fiber. -/
def fiberMissingLabels (S : SelectedHighLowStructure W m) (k : S.I) : Set S.I :=
  {r | ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
    x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val}

/-- The raw diffuse section is derived from the whole original row and
AE symmetry, without evaluating the kernel at a chosen representative. -/
theorem ae_reverseDiffuseSupply_on_fiber (k : S.I) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, S.reverseDiffuseSupply x = S.fiberDiffuseMass k := by
  have hsym : ∀ᵐ p ∂(μ.restrict {x | S.ρ x = k.val}).prod μ,
      p ∈ actualZeroRelation W m S.ρ ↔ p.swap ∈ actualZeroRelation W m S.ρ :=
    ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl) (actualZeroRelation_symm W m S.ρ)
  filter_upwards [(S.hfibers k.val k.property).2.2.2.rows,
    ae_restrict_mem (S.hfibers k.val k.property).1, Measure.ae_ae_of_ae_prod hsym]
    with x hx hmem hs
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hx.1, hs] with y hy hz
  apply propext
  change (y ∈ S.D ∩ S.L ∧ (y, x) ∈ actualZeroRelation W m S.ρ) ↔
    (y ∈ S.D ∩ S.L ∧ k.val y = 0 ∧ k.val ≠ S.ρ y)
  change (x, y) ∈ actualZeroRelation W m S.ρ ↔ (y, x) ∈ actualZeroRelation W m S.ρ at hz
  rw [← hz]
  change (y ∈ S.D ∩ S.L ∧ shiftedKernel W m x y = 0 ∧ S.ρ x ≠ S.ρ y) ↔ _
  rw [hy, hmem]

/-- Membership in each original whole-fiber missing predicate is constant
on a positive original whole fiber, modulo its restricted law. -/
theorem ae_fiber_missing_or_not (k r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
      x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val) ∨
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
      x ∉ KernelOperator.wholeFiberMissingSet S.ρ r.val) := by
  by_cases hkr : k = r
  · right
    filter_upwards [ae_restrict_mem (S.hfibers k.val k.property).1] with x hx hn
    exact hn.1 (hx.trans (congrArg Subtype.val hkr))
  · obtain ⟨q, _, hrq, _, _⟩ := KernelOperator.exists_cross_constant_of_homogeneous_rows
      (shiftedKernel W m) r.val k.val (Lp.stronglyMeasurable r.val) (Lp.stronglyMeasurable k.val)
      {x | S.ρ x = r.val} {x | S.ρ x = k.val}
      (S.hfibers r.val r.property).2.1 (S.hfibers k.val k.property).2.1
      (shiftedKernel_measurable W m)
      ((S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.1))
      ((S.hfibers k.val k.property).2.2.2.rows.mono (fun _ hx => hx.1))
      ((shiftedMoment_symm W m).mono (fun _ hp => hp.symm)) 4 hW.moment_mem
    by_cases hq : q ≤ 0
    · left
      filter_upwards [hrq, ae_restrict_mem (S.hfibers k.val k.property).1] with x hx hm
      exact ⟨fun he => hkr (Subtype.ext (hm.symm.trans he)), hx.trans_le hq⟩
    · right
      filter_upwards [hrq] with x hx hn
      exact hq (hx ▸ hn.2)

/-- The original missing-label incidences are constant on one common
restricted-law event for each original head. -/
theorem ae_missing_iff_fiberMissingLabels (k r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
      x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val ↔ r ∈ S.fiberMissingLabels k := by
  rcases S.ae_fiber_missing_or_not k r hW with hall | hnone
  · filter_upwards [hall] with x hx
    exact ⟨fun _ => hall, fun _ => hx⟩
  · have hnot : r ∉ S.fiberMissingLabels k := by
      intro hall
      change ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
        x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val at hall
      obtain ⟨x, _, hx, hn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
        (S.hfibers k.val k.property).2.1.ne' (hall.and hnone)
      exact hn hx
    filter_upwards [hnone] with x hx
    exact ⟨fun h => False.elim (hx h), fun h => False.elim (hnot h)⟩

/-- A fixed original-row predicate for membership in an entire compulsory
source. Its raw diffuse mass and all incidences are derived, not supplied. -/
def fiberCompulsoryPredicate (S : SelectedHighLowStructure W m) (k : S.I) (P : Finset S.I) : Prop :=
  k ∉ S.eligibleReverseAtom ∧ S.fiberDiffuseMass k = 0 ∧
    (∃ r : S.I, r ∈ S.eligibleReverseAtom ∧ r ∈ S.fiberMissingLabels k) ∧
    ∀ r : S.I, r ∈ S.eligibleReverseAtom → r ∈ S.fiberMissingLabels k → r ∈ P

/-- Entire compulsory-source membership is constant on every original
positive whole fiber, with all countable incidences on one good event. -/
theorem ae_compulsorySource_iff_fiberPredicate (k : S.I) (P : Finset S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
      x ∈ S.reverseCompulsorySource P ↔ S.fiberCompulsoryPredicate k P := by
  let : Countable S.I := S.hI.to_subtype
  have hlabels : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, ∀ r : S.I,
      x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val ↔ r ∈ S.fiberMissingLabels k :=
    ae_all_iff.mpr (fun r => S.ae_missing_iff_fiberMissingLabels k r hW)
  filter_upwards [hlabels, S.ae_reverseDiffuseSupply_on_fiber k,
    ae_restrict_of_ae (ReverseRecovery.ae_fiber_high_iff (S := S)),
    ae_restrict_mem (S.hfibers k.val k.property).1] with x hl hd hh hx
  have hH := hh k hx
  simp only [reverseCompulsorySource, fiberCompulsoryPredicate, mem_inter_iff,
    mem_ofPred_eq, hH, hd]
  simp_rw [hl]

namespace ReverseRecovery

variable (R : S.ReverseRecovery)

/-- Every original atom occupies one genuine original head or source
pattern, or stays entirely outside both heads and the entire source. -/
theorem whole_fiber_twoCenter_pattern (k r u : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hp : R.plateau = {r, u}) :
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, S.ρ x = r.val) ∨
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, S.ρ x = u.val) ∨
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate r u) ∨
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate u r) ∨
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterShared r u) ∨
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
      x ∉ R.plateauRegion ∪ S.reverseCompulsorySource R.plateau) := by
  by_cases hkr : k = r
  · left
    filter_upwards [ae_restrict_mem (S.hfibers k.val k.property).1] with x hx
    exact hx.trans (congrArg Subtype.val hkr)
  right
  by_cases hku : k = u
  · left
    filter_upwards [ae_restrict_mem (S.hfibers k.val k.property).1] with x hx
    exact hx.trans (congrArg Subtype.val hku)
  right
  by_cases hC : S.fiberCompulsoryPredicate k {r, u}
  · have hsource : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
        x ∈ S.reverseCompulsorySource {r, u} :=
      (S.ae_compulsorySource_iff_fiberPredicate k {r, u} hW).mono (fun _ hx => hx.mpr hC)
    rcases S.ae_fiber_missing_or_not k r hW with hr | hr
    · rcases S.ae_fiber_missing_or_not k u hW with hu | hu
      · exact Or.inr (Or.inr (Or.inl (by
          filter_upwards [hsource, hr, hu] with x hc hx hy
          exact ⟨⟨hc, hx⟩, hy⟩)))
      · exact Or.inl (by
          filter_upwards [hsource, hr, hu] with x hc hx hy
          exact ⟨⟨hc, hx⟩, hy⟩)
    · rcases S.ae_fiber_missing_or_not k u hW with hu | hu
      · exact Or.inr (Or.inl (by
          filter_upwards [hsource, hr, hu] with x hc hx hy
          exact ⟨⟨by simpa only [Finset.pair_comm] using hc, hy⟩, hx⟩))
      · obtain ⟨x, _, hc, hx, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
          (S.hfibers k.val k.property).2.1.ne' (hsource.and (hr.and hu))
        obtain ⟨v, hv, hxv⟩ := hc.2.2.1
        have hmem := hc.2.2.2 v hv hxv
        have hvr : v = r ∨ v = u := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
        exact False.elim (hvr.elim (fun h => hx (h ▸ hxv)) (fun h => hy (h ▸ hxv)))
  · right; right; right
    filter_upwards [S.ae_compulsorySource_iff_fiberPredicate k {r, u} hW,
      ae_restrict_mem (S.hfibers k.val k.property).1] with x hx hk hmem
    rcases hmem with hhead | hsource
    · rw [R.plateauRegion_eq_pair r u hp] at hhead
      rcases hhead with hr | hu
      · exact hkr (Subtype.ext (hk.symm.trans hr))
      · exact hku (Subtype.ext (hk.symm.trans hu))
    · exact hC (hx.mp (by simpa only [hp] using hsource))

end ReverseRecovery

end Erdos1017.CappedModel.SelectedHighLowStructure
