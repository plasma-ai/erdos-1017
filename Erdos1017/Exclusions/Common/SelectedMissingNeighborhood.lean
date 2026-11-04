module

public import Erdos1017.Exclusions.Common.SelectedRootRows

/-!
# Missing neighborhood of a whole atom

The exterior missing neighborhood of any whole atom lies on one side of the
zero-relation cut, which determines the adjacency between its distinct whole
rows.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

private theorem exists_missing_neighborhood_cut_side
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∃ b : Bool, ∀ᵐ x ∂μ, S.ρ x ≠ r.val → x ∉ S.rootNeighborhood r →
      (x ∈ S.Bcut ↔ b = true) := by
  have hs := hW.strict_gap_structure hd hgap
  have hpairs : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      p.2 ∉ S.rootNeighborhood r →
      (p.1 ∈ S.Bcut ∧ p.2 ∉ S.Bcut) ∨ (p.2 ∈ S.Bcut ∧ p.1 ∉ S.Bcut) := by
    filter_upwards [S.ae_root_adjacency r hW hd hgap,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
      hs.strict_support, hW.moment_mem, S.hcross] with p hr hg hsupport hmem hcross hx hy hn
    have hAf : PhysicalRepresentative.adjacency W m p.1 p.2 = false :=
      Bool.eq_false_iff.mpr (fun he => hn ((hr hx).mp he))
    have hG0 : W.moment CappedColor.adjacency p = 0 := by simpa [hAf] using hg
    have hM0 : shiftedKernel W m p.1 p.2 = 0 := by
      change shiftedMoment W m p = 0
      apply le_antisymm _ hmem.1
      by_contra hp
      have hpos : 0 < shiftedMoment W m p := lt_of_not_ge hp
      rw [ite_eq_left hpos, hG0] at hsupport
      norm_num at hsupport
    exact hcross hM0 (fun he => hy (he.symm.trans hx))
  rcases S.hfiberSide r.val (S.hfibers r.val r.property).2.1 with hside | hside
  · obtain ⟨x, hx, hxside, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers r.val r.property).2.1.ne'
      (hside.and (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpairs)))
    refine ⟨false, hrow.mono (fun y hy hne hn => ?_)⟩
    have hyNot : y ∉ S.Bcut := by
      rcases hy hx hne hn with h | h
      · exact h.2
      · exact False.elim (h.2 hxside)
    simp only [Bool.false_eq_true, iff_false]
    exact hyNot
  · obtain ⟨x, hx, hxside, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers r.val r.property).2.1.ne'
      (hside.and (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpairs)))
    refine ⟨true, hrow.mono (fun y hy hne hn => ?_)⟩
    have hyIn : y ∈ S.Bcut := by
      rcases hy hx hne hn with h | h
      · exact False.elim (hxside h.1)
      · exact h.1
    simpa using hyIn

/-- The exterior missing neighborhood of any actual whole atom lies on
one original zero-relation cut side. Its distinct whole rows therefore
have original adjacency one almost everywhere. This uses no new model or
pointwise upgrade of an original pair-null statement. -/
theorem ae_missing_neighborhood_complete_mod_rows
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      p.1 ∉ S.rootNeighborhood r → p.2 ∉ S.rootNeighborhood r →
      S.ρ p.1 ≠ S.ρ p.2 → adjacencyKernel W p.1 p.2 = 1 := by
  obtain ⟨b, hb⟩ := S.exists_missing_neighborhood_cut_side r hW hd hgap
  have hs := hW.strict_gap_structure hd hgap
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb,
    Measure.quasiMeasurePreserving_snd.ae hb, hs.strict_support, hW.moment_mem, S.hcross]
    with p hx hy hsupport hmem hcross hxR hyR hxN hyN hne
  have hbx := hx hxR hxN
  have hby := hy hyR hyN
  have hpos : 0 < shiftedMoment W m p := by
    by_contra hn
    have hM0 : shiftedKernel W m p.1 p.2 = 0 := le_antisymm (le_of_not_gt hn) hmem.1
    have h := hcross hM0 hne
    cases b <;> simp_all
  change W.moment CappedColor.adjacency p = 1
  simpa [hpos] using hsupport

end Erdos1017.CappedModel.SelectedHighLowStructure
