module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalGoodError
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalHighJoin

/-!
# Missing row of the universal hole

The opposite `H` missing row pays the partner and the exact `H` missing cell
once, and only the low good-region residual enters its signed error.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_high_same_atom_high (S : SelectedHighLowStructure W m) :
    ∀ᵐ q ∂μ.prod μ, q ∈ S.sameAtomRelation → q.1 ∈ S.H → q.2 ∈ S.H := by
  let : Countable S.I := S.hI.to_subtype
  have hall : ∀ᵐ q ∂μ.prod μ, ∀ k : S.I,
      S.ρ q.1 = k.val → S.ρ q.2 = k.val → q.1 ∈ S.H → q.2 ∈ S.H := by
    apply ae_all_iff.mpr
    intro k
    have hmeas := (S.hfibers k.val k.property).1
    rcases S.hfiberClass k.val k.property with hH | hL | hN
    · have h := (ae_restrict_iff' hmeas).mp hH
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae h] with q hq _ hk _
      exact hq hk
    · have h := (ae_restrict_iff' hmeas).mp hL
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae h] with q hq hk _ hhigh
      exact False.elim (disjoint_left.mp S.hpartition.2.2.2.2.1 hhigh (hq hk))
    · have h := (ae_restrict_iff' hmeas).mp hN
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae h] with q hq hk _ hhigh
      exact False.elim (disjoint_left.mp S.hpartition.2.2.2.2.2.1 hhigh (hq hk))
  filter_upwards [hall] with q hq hsame hhigh
  let k : S.I := ⟨S.ρ q.1, hsame.2⟩
  exact hq k rfl hsame.1.symm hhigh

private theorem UniversalPhysicalPrimal.ae_hole_missing_three_regions
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.universalPartnerHoleRegion r p →
      PhysicalRepresentative.adjacency W m q.1 q.2 = false →
        S.ρ q.2 = p.val ∨ q.2 ∈ S.universalPartnerHoleRegion r p ∨
          q.2 ∈ S.universalLowGoodRegion r p d c := by
  have hhigh := (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mp
    (S.ae_universalPartnerHole_high r p hpair hW hd hgap hell.2)
  have hroot := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.neutral_atom_physical_adjacency r hW hd hgap hN)
  have hbad := P.ae_universalUpperE2_hole_bad_join S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  have hhighGood := S.ae_universalHole_highGood_join r p hpair hW hd hgap hell.2
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hhigh, hroot, hbad, hhighGood,
    S.ae_high_same_atom_high,
    PhysicalRepresentative.adjacency_moment_ae_eq W m hs,
    hs, hW.moment_mem, S.ae_zero_iff_sameAtom_or_relation hW hd hgap,
    S.hrelation] with q hhigh hroot hbad hhighGood hsame hphysical hsupport hnonneg
      hzero hrel hx hmissing
  have hAdj : adjacencyKernel W q.1 q.2 = 0 := by
    change adjacencyKernel W q.1 q.2 = _ at hphysical
    rw [hphysical, hmissing]
    norm_num
  by_cases hp : S.ρ q.2 = p.val
  · exact Or.inl hp
  by_cases hH : q.2 ∈ S.universalPartnerHoleRegion r p
  · exact Or.inr (Or.inl hH)
  have hnotr : S.ρ q.1 ≠ r.val := fun h => hx (Or.inl (Or.inl h))
  have hyr : S.ρ q.2 ≠ r.val := by
    intro hy
    have h := (hroot hy).mpr hnotr
    change PhysicalRepresentative.adjacency W m q.2 q.1 = true at h
    rw [PhysicalRepresentative.adjacency_symm W m q.2 q.1, hmissing] at h
    exact Bool.false_ne_true h
  have hyU : q.2 ∈ S.universalPartnerCommonRegion r p := by
    intro h
    rcases h with (hr | hp') | hh
    · exact hyr hr
    · exact hp hp'
    · exact hH hh
  have hyBad : q.2 ∉ S.universalUpperE2BadRegion r p d c := by
    intro hy
    have h := hbad hx hy
    linarith only [h, hAdj]
  have hyGood : q.2 ∈ S.universalGoodCommonRegion r p d c := ⟨hyU, hyBad⟩
  have hK : shiftedKernel W m q.1 q.2 = 0 := by
    apply le_antisymm _ hnonneg.1
    apply le_of_not_gt
    intro hpos
    change adjacencyKernel W q.1 q.2 =
      (if 0 < shiftedMoment W m q then 1 else 0) at hsupport
    rw [ite_eq_left hpos] at hsupport
    linarith only [hAdj, hsupport]
  rcases hzero.mp hK with h | h
  · have hyHigh : q.2 ∈ S.H := hsame h (hhigh hx)
    have hone := hhighGood hx ⟨hyGood, hyHigh⟩
    exact False.elim (by linarith only [hone, hAdj])
  · rcases hrel h with h | h
    · exact Or.inr (Or.inr ⟨hyGood, h.2.1⟩)
    · exact False.elim (disjoint_left.mp S.hpartition.2.2.2.2.1 (hhigh hx) h.2.1)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integral_missing_row_three_sections
    (M I H L : Set Ω) (hM : MeasurableSet M)
    (hH : MeasurableSet H) (hL : MeasurableSet L)
    (hIH : Disjoint I H) (hIL : Disjoint I L) (hHL : Disjoint H L)
    (hcover : M =ᵐ[μ] ((M ∩ I) ∪ (M ∩ H)) ∪ (M ∩ L))
    (f sigma : Ω → ℝ) (hf : Integrable f μ) (hsigma : Integrable sigma μ)
    (v w : ℝ)
    (hrowI : ∀ᵐ z ∂μ.restrict (M ∩ I), f z ≤ v)
    (hrowH : ∀ᵐ z ∂μ.restrict (M ∩ H), f z ≤ w)
    (hrowL : ∀ᵐ z ∂μ.restrict (M ∩ L), f z ≤ sigma z) :
    (∫ z in M, f z ∂μ) ≤ v * μ.real (M ∩ I) + w * μ.real (M ∩ H) +
      ∫ z in M ∩ L, sigma z ∂μ := by
  have hdis1 : Disjoint (M ∩ I) (M ∩ H) := disjoint_left.mpr
    (fun _ hx hy => disjoint_left.mp hIH hx.2 hy.2)
  have hdis2 : Disjoint ((M ∩ I) ∪ (M ∩ H)) (M ∩ L) := by
    apply disjoint_left.mpr
    intro z hz hy
    rcases hz with hz | hz
    · exact disjoint_left.mp hIL hz.2 hy.2
    · exact disjoint_left.mp hHL hz.2 hy.2
  have hi := integral_mono_ae hf.integrableOn (integrable_const v) hrowI
  have hh := integral_mono_ae hf.integrableOn (integrable_const w) hrowH
  have hl := integral_mono_ae hf.integrableOn hsigma.integrableOn hrowL
  rw [setIntegral_const, smul_eq_mul] at hi hh
  rw [setIntegral_congr_set hcover,
    setIntegral_union hdis2 (hM.inter hL) hf.integrableOn hf.integrableOn,
    setIntegral_union hdis1 (hM.inter hH) hf.integrableOn hf.integrableOn]
  nlinarith only [hi, hh, hl]

private theorem ae_physical_hole_missingMass_eq_original (S : SelectedHighLowStructure W m)
    (r p : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ h ∂μ,
      μ.real (IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) h ∩
        S.universalPartnerHoleRegion r p) = S.universalPartnerHoleMissingMass r p h := by
  let H := S.universalPartnerHoleRegion r p
  let A := PhysicalRepresentative.adjacency W m
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hprod := PhysicalRepresentative.adjacency_moment_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  have hsections := Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hsections] with x hx
  have hM : MeasurableSet (IndependentAtomCopy.missingSection A x) :=
    IndependentAtomCopy.measurableSet_missingSection A
      (PhysicalRepresentative.measurable_adjacency W m) x
  have hpoint : (fun z => (IndependentAtomCopy.missingSection A x).indicator (fun _ => (1 : ℝ)) z)
      =ᵐ[μ] (fun z => 1 - adjacencyKernel W x z) := by
    filter_upwards [hx] with z hz
    by_cases hAz : A x z = true
    · have hreal : adjacencyKernel W x z = 1 := by
        change adjacencyKernel W x z = if A x z = true then 1 else 0 at hz
        simpa [hAz] using hz
      simp [IndependentAtomCopy.missingSection, hAz, hreal]
    · have hAz' : A x z = false := Bool.eq_false_iff.mpr hAz
      have hreal : adjacencyKernel W x z = 0 := by
        change adjacencyKernel W x z = if A x z = true then 1 else 0 at hz
        simpa [hAz'] using hz
      simp [IndependentAtomCopy.missingSection, hAz', hreal]
  change μ.real (IndependentAtomCopy.missingSection A x ∩ H) =
    ∫ z in H, 1 - adjacencyKernel W x z ∂μ
  rw [← integral_indicator_one (hM.inter hH)]
  rw [← integral_indicator hH]
  apply integral_congr_ae
  filter_upwards [hpoint] with z hz
  by_cases hzH : z ∈ H
  · by_cases hzM : z ∈ IndependentAtomCopy.missingSection A x
    · simpa [Set.indicator, hzH, hzM] using hz
    · simpa [Set.indicator, hzH, hzM] using hz
  · simp [Set.indicator, hzH]

/-- The original opposite H missing row pays the partner and exact H
missing cell once. Only the actual LOW good-region residual enters its error. -/
theorem UniversalPhysicalPrimal.ae_hole_missing_row_le_signed_error
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.universalPartnerHoleRegion r p →
      q.2 ∈ S.universalNegativeRegion r p →
        (∫ z in IndependentAtomCopy.missingSection
          (PhysicalRepresentative.adjacency W m) q.1,
            PhysicalRepresentative.charge W m q.2 z ∂μ) ≤
          S.originalAtomMass p * (-S.rootChargeRow r q.2) +
            S.universalPartnerHoleMissingMass r p q.1 *
              PhysicalRepresentative.charge W m q.1 q.2 +
            S.universalLowGoodErrorRow r p d c q.1 := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalNegativeRegion r p
  let Bad := S.universalUpperE2BadRegion r p d c
  let Good := S.universalGoodCommonRegion r p d c
  let L := S.universalLowGoodRegion r p d c
  let I := {z | S.ρ z = p.val}
  let sigma := fun z => -(S.rootChargeRow r z + S.rootChargeRow p z)
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  have hBad : MeasurableSet Bad := S.measurableSet_universalUpperE2BadRegion r p d c
  have hGood : MeasurableSet Good := S.measurableSet_universalGoodCommonRegion r p d c
  have hL : MeasurableSet L := S.measurableSet_universalLowGoodRegion r p d c
  have hI : MeasurableSet I := (S.hfibers p.val p.property).1
  have hsub := S.universalNegativeRegion_subset_upperE2Bad r p d c
    (by linarith only [hA]) hmargin (by linarith only [hell.2])
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have hYeq := PhysicalRepresentative.charge_ae_eq W m hs
  have hBG := P.ae_bad_good_charge_le_score_deficit S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  rw [Measure.prod_restrict] at hBG
  have hBG' := (ae_restrict_iff' (hBad.prod hGood)).mp hBG
  have hgood : ∀ᵐ v ∂μ.prod μ, v.1 ∈ B → v.2 ∈ L → Y v.1 v.2 ≤ sigma v.2 := by
    filter_upwards [hBG', hYeq] with v hv he hx hz
    change PhysicalRepresentative.charge W m v.1 v.2 ≤ _
    rw [he]
    exact hv ⟨hsub hx, hz.1⟩
  have hpartner : ∀ᵐ v ∂μ.prod μ, S.ρ v.2 = p.val → Y v.1 v.2 = S.rootChargeRow p v.1 := by
    have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (S.ae_root_charge p hW hd hgap)
    filter_upwards [hswap] with v hv hz
    change PhysicalRepresentative.charge W m v.1 v.2 = _
    exact (PhysicalRepresentative.charge_symm W m v.1 v.2).trans (hv hz)
  have hpartnerOpp := (ae_restrict_iff' hB).mp
    (P.ae_universalNegative_partner_charge S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hcover := Measure.ae_ae_of_ae_prod
    (P.ae_hole_missing_three_regions S r p hpair hW hd hgap hN hA hAhalf hell hmargin)
  have hHH := Measure.ae_ae_of_ae_prod
    (S.ae_universalPartnerHole_missing_iff_sameAtom r p hpair hW hd hgap hell.2)
  have hphysical := Measure.ae_ae_of_ae_prod
    (PhysicalRepresentative.adjacency_moment_ae_eq W m hs)
  have hmass := S.ae_physical_hole_missingMass_eq_original r p hW hd hgap
  have hsigma : Integrable sigma μ := by
    convert (S.integrable_universalNegativeCharge r).add
      (S.integrable_universalNegativeCharge p) using 1
    ext z
    change -(S.rootChargeRow r z + S.rootChargeRow p z) =
      -S.rootChargeRow r z + -S.rootChargeRow p z
    ring
  have hIH : Disjoint I H := disjoint_left.mpr
    (fun _ hx hy => hy (Or.inl (Or.inr hx)))
  have hIL : Disjoint I L := disjoint_left.mpr
    (fun _ hx hy => hy.1.1 (Or.inl (Or.inr hx)))
  have hHL : Disjoint H L := disjoint_left.mpr
    (fun _ hx hy => hy.1.1 (Or.inr hx))
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcover,
    Measure.quasiMeasurePreserving_fst.ae hHH,
    Measure.quasiMeasurePreserving_fst.ae hphysical,
    Measure.quasiMeasurePreserving_fst.ae hmass,
    Measure.quasiMeasurePreserving_snd.ae (Measure.ae_ae_of_ae_prod hpartner),
    Measure.quasiMeasurePreserving_snd.ae (Measure.ae_ae_of_ae_prod hgood),
    Measure.quasiMeasurePreserving_snd.ae hpartnerOpp,
    S.ae_physical_charge_eq_on_sameAtom hW hd hgap]
    with q hc hh hp hm hpart hg hopp hsame hxH hxB
  let M := IndependentAtomCopy.missingSection G q.1
  let f := Y q.2
  let v := Y q.1 q.2
  let dneg := -S.rootChargeRow r q.2
  have hM : MeasurableSet M := IndependentAtomCopy.measurableSet_missingSection G
    (PhysicalRepresentative.measurable_adjacency W m) q.1
  have hf : Integrable f μ := by
    apply Integrable.of_bound
      ((PhysicalRepresentative.measurable_charge W m).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 3
    exact Eventually.of_forall (fun z => by
      have h := PhysicalRepresentative.charge_mem_Icc W m q.2 z
      change ‖f z‖ ≤ 3
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨h.1, by linarith only [h.2]⟩)
  have hparts : M =ᵐ[μ] ((M ∩ I) ∪ (M ∩ H)) ∪ (M ∩ L) := by
    filter_upwards [hc] with z hz
    apply propext
    constructor
    · intro hzm
      rcases hz hxH hzm with hzI | hzH | hzL
      · exact Or.inl (Or.inl ⟨hzm, hzI⟩)
      · exact Or.inl (Or.inr ⟨hzm, hzH⟩)
      · exact Or.inr ⟨hzm, hzL⟩
    · intro h
      rcases h with (h | h) | h <;> exact h.1
  have hrowI : ∀ᵐ z ∂μ.restrict (M ∩ I), f z ≤ dneg := by
    filter_upwards [ae_restrict_of_ae hpart, ae_restrict_mem (hM.inter hI)] with z hz hzi
    have heq := hz hzi.2
    rw [hopp hxB] at heq
    exact heq.le
  have hrowH : ∀ᵐ z ∂μ.restrict (M ∩ H), f z ≤ v := by
    filter_upwards [ae_restrict_of_ae hh, ae_restrict_of_ae hp,
      ae_restrict_of_ae hsame, ae_restrict_mem (hM.inter hH)] with z hz hphys hcharge hzm
    have hzero : adjacencyKernel W q.1 z = 0 := by
      change adjacencyKernel W q.1 z = _ at hphys
      have hmissing : PhysicalRepresentative.adjacency W m q.1 z = false := hzm.1
      rw [hphys, hmissing]
      norm_num
    have hAtom := (hz hxH hzm.2).mp hzero
    have heq : f z = v := (hcharge hAtom).trans
      (PhysicalRepresentative.charge_symm W m q.2 q.1)
    exact heq.le
  have hrowL : ∀ᵐ z ∂μ.restrict (M ∩ L), f z ≤ sigma z := by
    filter_upwards [ae_restrict_of_ae hg, ae_restrict_mem (hM.inter hL)] with z hz hzl
    exact hz hxB hzl.2
  have hbound := integral_missing_row_three_sections M I H L hM hH hL hIH hIL hHL
    hparts f sigma hf hsigma dneg v hrowI hrowH hrowL
  have hPmass : μ.real (M ∩ I) ≤ S.originalAtomMass p :=
    measureReal_mono inter_subset_right
  have hdneg : 0 ≤ dneg := neg_nonneg.mpr hxB.2.le
  have hpaid := mul_le_mul_of_nonneg_left hPmass hdneg
  change μ.real (M ∩ H) = S.universalPartnerHoleMissingMass r p q.1 at hm
  rw [hm] at hbound
  change (∫ z in M, f z ∂μ) ≤ S.originalAtomMass p * dneg +
    S.universalPartnerHoleMissingMass r p q.1 * v +
      S.universalLowGoodErrorRow r p d c q.1
  change (∫ z in M, f z ∂μ) ≤ _ at hbound
  have he : S.universalLowGoodErrorRow r p d c q.1 = ∫ z in M ∩ L, sigma z ∂μ := rfl
  rw [← he] at hbound
  nlinarith only [hbound, hpaid]

end Erdos1017.CappedModel.SelectedHighLowStructure
