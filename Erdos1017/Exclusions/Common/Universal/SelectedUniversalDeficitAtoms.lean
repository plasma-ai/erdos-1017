module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitBudget
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterFiberPatterns

/-!
# Atoms carrying missing mass in the partner hole

Positive missing mass inside the universal partner hole is carried by one whole
independent fiber of the original model.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Positive original missing mass inside the universal partner hole is
carried by one original whole independent fiber. -/
theorem ae_universalPartnerHole_atom_of_missing_mass_pos
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      0 < S.universalPartnerHoleMissingMass r p x →
        ∃ i : S.I, S.ρ x = i.val ∧
          (∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val},
            z ∈ S.universalPartnerHoleRegion r p) ∧
          S.universalPartnerHoleMissingMass r p x = S.originalAtomMass i ∧
          (∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val},
            S.universalRootDeficit r z = S.universalRootDeficit r x) := by
  let H := S.universalPartnerHoleRegion r p
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hmissing := Measure.ae_ae_of_ae_prod
    (S.ae_universalPartnerHole_missing_iff_sameAtom r p hpair hW hd hgap hell)
  have hD := Measure.ae_ae_of_ae_prod
    (S.ae_universalRootDeficit_eq_on_sameAtom r hW hd hgap)
  have hs := Measure.ae_ae_of_ae_prod
    (hW.strict_gap_structure hd hgap).strict_support
  apply (ae_restrict_iff' hH).mpr
  filter_upwards [hmissing, hD, hs] with x hx hDx hsx hxH hpos
  let A : Set Ω := {z | (x, z) ∈ S.sameAtomRelation}
  have hA : MeasurableSet A :=
    S.measurableSet_sameAtomRelation.preimage (measurable_const.prodMk measurable_id)
  have hrow : ∀ᵐ z ∂μ.restrict H,
      1 - adjacencyKernel W x z = A.indicator (fun _ => (1 : ℝ)) z := by
    filter_upwards [ae_restrict_of_ae hx, ae_restrict_of_ae hsx,
      ae_restrict_mem hH] with z hzero hsupport hz
    have heq := hzero hxH hz
    by_cases ha : z ∈ A
    · have hG : adjacencyKernel W x z = 0 := heq.mpr ha
      simp [indicator_of_mem ha, hG]
    · have hG : adjacencyKernel W x z = 1 := by
        have hn : adjacencyKernel W x z ≠ 0 := fun h => ha (heq.mp h)
        change adjacencyKernel W x z =
          if 0 < shiftedKernel W m x z then 1 else 0 at hsupport
        by_cases hk : 0 < shiftedKernel W m x z
        · simpa only [ite_eq_left hk] using hsupport
        · have hz : adjacencyKernel W x z = 0 := by
            simpa only [ite_eq_right hk] using hsupport
          exact False.elim (hn hz)
      simp [indicator_of_notMem ha, hG]
  have hmass : S.universalPartnerHoleMissingMass r p x = μ.real (H ∩ A) := by
    change (∫ z in H, 1 - adjacencyKernel W x z ∂μ) = _
    rw [integral_congr_ae hrow, setIntegral_indicator hA,
      setIntegral_const, smul_eq_mul, mul_one]
  by_cases hi : S.ρ x ∈ S.I
  · let i : S.I := ⟨S.ρ x, hi⟩
    have hxI : S.ρ x = i.val := rfl
    have hAeq : A = {z | S.ρ z = i.val} := by
      ext z
      change (S.ρ x = S.ρ z ∧ S.ρ x ∈ S.I) ↔ S.ρ z = i.val
      constructor
      · exact fun h => h.1.symm.trans hxI
      · exact fun h => ⟨hxI.trans h.symm, hi⟩
    rw [hAeq] at hmass
    have hI : MeasurableSet {z | S.ρ z = i.val} := (S.hfibers i.val i.property).1
    have hposI : 0 < μ (H ∩ {z | S.ρ z = i.val}) := by
      have hm : 0 < μ.real (H ∩ {z | S.ρ z = i.val}) := hmass ▸ hpos
      exact ENNReal.toReal_pos_iff.mp hm |>.1
    have hne_r : i ≠ r := by
      intro he
      have hnull : H ∩ {z | S.ρ z = i.val} = ∅ := by
        ext z
        constructor
        · intro hz
          exact False.elim (hz.1 (Or.inl (Or.inl
            (hz.2.trans (congrArg Subtype.val he)))))
        · intro hz
          exact hz.elim
      rw [hnull, measure_empty] at hposI
      exact (lt_irrefl 0) hposI
    have hne_p : i ≠ p := by
      intro he
      have hnull : H ∩ {z | S.ρ z = i.val} = ∅ := by
        ext z
        constructor
        · intro hz
          exact False.elim (hz.1 (Or.inl (Or.inr
            (hz.2.trans (congrArg Subtype.val he)))))
        · intro hz
          exact hz.elim
      rw [hnull, measure_empty] at hposI
      exact (lt_irrefl 0) hposI
    rcases S.ae_fiber_missing_or_not i p hW with hmiss | hjoined
    · have hwhole : ∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val}, z ∈ H := by
        filter_upwards [hmiss, ae_restrict_mem hI] with z hz hzi
        change z ∉ {z | S.ρ z = r.val} ∪ {z | S.ρ z = p.val} ∪
          S.rootNeighborhood p
        intro hbad
        rcases hbad with (hr | hp) | hN
        · exact hne_r (Subtype.ext (hzi.symm.trans hr))
        · exact hne_p (Subtype.ext (hzi.symm.trans hp))
        · exact (not_lt_of_ge hz.2) hN.2
      have hfull : μ.real (H ∩ {z | S.ρ z = i.val}) = S.originalAtomMass i := by
        change μ.real (H ∩ {z | S.ρ z = i.val}) = μ.real {z | S.ρ z = i.val}
        apply measureReal_congr
        filter_upwards [(ae_restrict_iff' hI).mp hwhole] with z hz
        exact propext ⟨fun h => h.2, fun h => ⟨hz h, h⟩⟩
      have hconst : ∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val},
          S.universalRootDeficit r z = S.universalRootDeficit r x := by
        apply (ae_restrict_iff' hI).mpr
        filter_upwards [hDx] with z hz hzi
        exact (hz ⟨hxI.trans hzi.symm, hi⟩).symm
      exact ⟨i, hxI, hwhole, hmass.trans hfull, hconst⟩
    · have hnull : μ (H ∩ {z | S.ρ z = i.val}) = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        have hjoined' := (ae_restrict_iff' hI).mp hjoined
        have hpzero := (ae_restrict_iff' hH).mp
          (S.ae_partner_row_zero_on_universalHole r p hW)
        filter_upwards [hjoined', hpzero] with z hz hpz hbad
        have hzI := hbad.2
        have hH' := hbad.1
        have hN : z ∈ KernelOperator.wholeFiberMissingSet S.ρ p.val := by
          have hnotp : S.ρ z ≠ p.val := by
            intro he
            exact hH' (Or.inl (Or.inr he))
          exact ⟨hnotp, by rw [hpz hH']⟩
        exact hz hzI hN
      rw [hnull] at hposI
      exact False.elim ((lt_irrefl 0) hposI)
  · have hAempty : A = ∅ := by
      ext z
      constructor
      · intro hz
        exact False.elim (hi hz.2)
      · intro hz
        exact hz.elim
    rw [hAempty, inter_empty, measureReal_empty] at hmass
    exact False.elim ((lt_irrefl 0) (hmass ▸ hpos))

end Erdos1017.CappedModel.SelectedHighLowStructure
