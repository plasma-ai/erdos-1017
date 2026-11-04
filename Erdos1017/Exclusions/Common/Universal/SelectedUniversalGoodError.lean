module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalBounds
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalBadLowHoles
public import Erdos1017.Exclusions.E2.Upper.UpperE2UniversalPricePrerequisites

/-!
# Copy error of the extra hole in the universal primal

This module defines the part of the partner hole outside the compulsory source
and bounds its copied error: the good-region mass pays the denominator, the
full-hole copied error equals its extra-hole part, and the corrected error is an
integrable nonnegative row allowance.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.UpperE2UniversalScalar

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]

private theorem good_error_integral_le
    (E : Set Ω) (e den : Ω → ℝ) (c w gL gH tau : ℝ)
    (hc : 0 < c) (hw : 0 ≤ w) (hgL : 0 ≤ gL) (hgH : 0 ≤ gH)
    (htau : 0 ≤ tau) (hu : 0 < w + gL + gH)
    (hsm : AEStronglyMeasurable (fun x => e x / den x) (μ.restrict E))
    (he : ∀ᵐ x ∂μ.restrict E, 0 ≤ e x ∧ e x ≤ tau * gL)
    (hden : ∀ᵐ x ∂μ.restrict E, 0 < e x → c + w + gL ≤ den x) :
    Integrable (fun x => e x / den x) (μ.restrict E) ∧
      ∫ x in E, e x / den x ∂μ ≤
        μ.real E * (tau * (gL + gH) / (w + gL + gH)) := by
  let C := tau * (gL + gH) / (w + gL + gH)
  have hC : 0 ≤ C :=
    div_nonneg (mul_nonneg htau (add_nonneg hgL hgH)) hu.le
  have hbound : ∀ᵐ x ∂μ.restrict E, ‖e x / den x‖ ≤ C := by
    filter_upwards [he, hden] with x hx hdx
    have hnonneg : 0 ≤ e x / den x := by
      by_cases hpos : 0 < e x
      · exact div_nonneg hx.1 (by linarith [hdx hpos])
      · have hzero : e x = 0 := le_antisymm (le_of_not_gt hpos) hx.1
        simp [hzero]
    have hle : e x / den x ≤ C :=
      good_error_ratio_le hc hw hgL hgH htau hx.1 hx.2 hu hdx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hint : Integrable (fun x => e x / den x) (μ.restrict E) :=
    Integrable.of_bound hsm C hbound
  refine ⟨hint, ?_⟩
  have hle : ∀ᵐ x ∂μ.restrict E, e x / den x ≤ C := by
    filter_upwards [he, hden] with x hx hdx
    exact good_error_ratio_le hc hw hgL hgH htau hx.1 hx.2 hu hdx
  have hInt := integral_mono_ae hint (integrable_const C) hle
  simpa only [setIntegral_const, smul_eq_mul] using hInt

end Erdos1017.UpperE2UniversalScalar

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The same saturated partner row pays the common-region and good-region
mass resources, without a smooth contact or alternate primal law. -/
theorem universal_partner_common_good_resources
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    2 * (c - m * d) - (1 - m) * S.originalAtomMass r ≤
        2 * (-m) * μ.real (S.universalPartnerCommonRegion r p) ∧
      ((-m) + (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))) *
          μ.real (S.universalGoodCommonRegion r p d c) ≤
        2 * (-m) * μ.real (S.universalPartnerCommonRegion r p) -
          (2 * (c - m * d) - (1 - m) * S.originalAtomMass r) := by
  let U := S.universalPartnerCommonRegion r p
  let Good := S.universalGoodCommonRegion r p d c
  let θ := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  let ell := -m
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hGood : MeasurableSet Good := S.measurableSet_universalGoodCommonRegion r p d c
  have hp : Integrable (p.val : Ω → ℝ) μ := (Lp.memLp p.val).integrable (by norm_num)
  have hrow : ∀ᵐ x ∂μ.restrict U,
      p.val x ≤ 2 * ell ∧ (x ∈ Good → p.val x ≤ ell - θ) := by
    filter_upwards [ae_restrict_of_ae (S.ae_universal_row_pos_on_outside r hW hd hgap hN),
      S.ae_partner_row_pos_on_universalCommon r p,
      ae_restrict_of_ae (hpair.ae_common_neighbor_score_le hW hd hgap),
      ae_restrict_of_ae (S.ae_universalRootDeficit_eq_shifted_row r hW hd hgap),
      ae_restrict_mem hU] with x hr hp' hscore hβ hx
    have hnotr : S.ρ x ≠ r.val := by
      intro hh
      exact hx (Or.inl (Or.inl hh))
    have hrx := hr hnotr
    have hs := hscore hrx hp'
    have hβ' : S.rootChargeRow r x = r.val x + m := by
      unfold universalRootDeficit at hβ
      rw [ite_eq_left hrx] at hβ
      linarith only [hβ]
    constructor
    · dsimp only [ell]
      linarith only [hs, hrx]
    · intro hxGood
      have hθ : θ ≤ S.rootChargeRow r x := by
        have hxBad : x ∉ S.universalUpperE2BadRegion r p d c := hxGood.2
        apply le_of_not_gt
        intro hlt
        apply hxBad
        change x ∈ (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ) ∩
          {x | S.rootChargeRow r x < θ}
        exact ⟨by
          intro hhead
          rcases hhead with h | h
          · exact hnotr h
          · exact hx (Or.inl (Or.inr h)), hlt⟩
      dsimp only [ell]
      linarith only [hs, hβ', hθ]
  have hrowU : ∀ᵐ x ∂μ.restrict U, p.val x ≤ 2 * ell := hrow.mono (fun _ hx => hx.1)
  have hUbound := integral_mono_ae hp.integrableOn (integrable_const (2 * ell)) hrowU
  rw [setIntegral_const, smul_eq_mul] at hUbound
  have hUeq := S.universal_partner_common_row_integral r p hpair hW
  change (∫ x in U, p.val x ∂μ) = _ at hUeq
  rw [hUeq] at hUbound
  have hGoodSub : Good ⊆ U := fun _ hx => hx.1
  let J := U \ Good
  have hJ : MeasurableSet J := hU.diff hGood
  have hdis : Disjoint J Good := disjoint_sdiff_self_left
  have hpart : J ∪ Good = U := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · exact hGoodSub hx
    · intro hx
      by_cases hg : x ∈ Good
      · exact Or.inr hg
      · exact Or.inl ⟨hx, hg⟩
  have hGbound : ∀ᵐ x ∂μ.restrict Good, p.val x ≤ ell - θ := by
    have h' := (ae_restrict_iff' hU).mp hrow
    apply (ae_restrict_iff' hGood).mpr
    filter_upwards [h'] with x hx hxGood
    exact (hx (hGoodSub hxGood)).2 hxGood
  have hJbound : ∀ᵐ x ∂μ.restrict J, p.val x ≤ 2 * ell := by
    have h' := (ae_restrict_iff' hU).mp hrowU
    apply (ae_restrict_iff' hJ).mpr
    filter_upwards [h'] with x hx hxJ
    exact hx hxJ.1
  have hI1 := integral_mono_ae hp.integrableOn (integrable_const (ell - θ)) hGbound
  have hI2 := integral_mono_ae hp.integrableOn (integrable_const (2 * ell)) hJbound
  rw [setIntegral_const, smul_eq_mul] at hI1 hI2
  have hsplit : (∫ x in U, p.val x ∂μ) =
      (∫ x in J, p.val x ∂μ) + (∫ x in Good, p.val x ∂μ) := by
    rw [← hpart, setIntegral_union hdis hGood hp.integrableOn hp.integrableOn]
  have hmass : μ.real J + μ.real Good = μ.real U := by
    rw [← measureReal_union hdis hGood, hpart]
  rw [hUeq] at hsplit
  dsimp only [U, Good, ell, θ] at *
  constructor
  · nlinarith only [hUbound]
  · have hmassMul := congrArg (fun t : ℝ => 2 * (-m) * t) hmass
    nlinarith only [hI1, hI2, hsplit, hmassMul]

/-- The literal part of the partner hole outside the same entire
compulsory source of the selected singleton recovery. -/
def universalExtraHoleRegion (S : SelectedHighLowStructure W m)
    (r p : S.I) : Set Ω :=
  S.universalPartnerHoleRegion r p \ S.reverseCompulsorySource {p}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
theorem measurableSet_universalExtraHoleRegion
    (S : SelectedHighLowStructure W m) (r p : S.I) :
    MeasurableSet (S.universalExtraHoleRegion r p) :=
  (S.measurableSet_universalPartnerHoleRegion r p).diff
    (S.measurableSet_reverseCompulsorySource {p})

/-- The actual signed LOW good-region missing-recipient allowance for one
extra-hole row. It uses the original physical representative. -/
def universalLowGoodErrorRow (S : SelectedHighLowStructure W m)
    (r p : S.I) (d c : ℝ) (h : Ω) : ℝ :=
  ∫ z in IndependentAtomCopy.missingSection
      (PhysicalRepresentative.adjacency W m) h ∩
        S.universalLowGoodRegion r p d c,
    -(S.rootChargeRow r z + S.rootChargeRow p z) ∂μ

/-- On the actual LOW good region, the two-head signed score lies in
the same interval used for the copied-row error. -/
theorem ae_lowGood_score_range
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ z ∂μ.restrict (S.universalLowGoodRegion r p d c),
      0 ≤ -(S.rootChargeRow r z + S.rootChargeRow p z) ∧
      -(S.rootChargeRow r z + S.rootChargeRow p z) ≤
        max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
          (1 + m))) 0 := by
  let L := S.universalLowGoodRegion r p d c
  let U := S.universalPartnerCommonRegion r p
  have hL : MeasurableSet L := S.measurableSet_universalLowGoodRegion r p d c
  have hLsub : L ⊆ U := fun _ hz => hz.1.1
  have hrow := (ae_restrict_iff' (S.measurableSet_universalPartnerCommonRegion r p)).mp
    (S.ae_partner_row_pos_on_universalCommon r p)
  have hgood := (ae_restrict_iff' (S.measurableSet_universalGoodCommonRegion r p d c)).mp
    (S.ae_good_common_score_deficit_le_endpoint r p hW hd hgap)
  apply (ae_restrict_iff' hL).mpr
  filter_upwards [S.ae_universal_row_pos_on_outside r hW hd hgap hN,
    hrow, hpair.ae_common_neighbor_score_le hW hd hgap,
    S.ae_universalRootDeficit_eq_shifted_row r hW hd hgap,
    S.ae_universalRootDeficit_eq_shifted_row p hW hd hgap,
    hgood] with z hr hp hs hβr hβp hg hzL
  have hzU : z ∈ U := hLsub hzL
  have hnotr : S.ρ z ≠ r.val := by
    intro hh
    exact hzU (Or.inl (Or.inl hh))
  have hrpos := hr hnotr
  have hppos := hp hzU
  have hscore := hs hrpos hppos
  have hβr' : S.rootChargeRow r z = r.val z + m := by
    unfold universalRootDeficit at hβr
    rw [ite_eq_left hrpos] at hβr
    linarith only [hβr]
  have hβp' : S.rootChargeRow p z = p.val z + m := by
    unfold universalRootDeficit at hβp
    rw [ite_eq_left hppos] at hβp
    linarith only [hβp]
  constructor
  · linarith only [hscore, hβr', hβp']
  · exact hg hzL.1


/-- The actual LOW good-region missing-row error lies between zero and the
common LOW good-region mass times its signed score allowance. -/
theorem universalLowGoodErrorRow_mem_Icc
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (h : Ω) :
    S.universalLowGoodErrorRow r p d c h ∈ Icc (0 : ℝ)
      (max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
        (1 + m))) 0 * μ.real (S.universalLowGoodRegion r p d c)) := by
  let L := S.universalLowGoodRegion r p d c
  let M := IndependentAtomCopy.missingSection
    (PhysicalRepresentative.adjacency W m) h ∩ L
  let τ := max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
    (1 + m))) 0
  let σ := fun z : Ω => -(S.rootChargeRow r z + S.rootChargeRow p z)
  have hL : MeasurableSet L := S.measurableSet_universalLowGoodRegion r p d c
  have hM : MeasurableSet M :=
    (IndependentAtomCopy.measurableSet_missingSection
      (PhysicalRepresentative.adjacency W m)
      (PhysicalRepresentative.measurable_adjacency W m) h).inter hL
  have hσi : Integrable σ μ := by
    dsimp only [σ]
    convert (S.integrable_universalNegativeCharge r).add
      (S.integrable_universalNegativeCharge p) using 1
    funext z
    simp only [Pi.add_apply]
    ring
  have hσ := (ae_restrict_iff' hL).mp
    (S.ae_lowGood_score_range r p hpair hW hd hgap hN)
  have hσM : ∀ᵐ z ∂μ.restrict M, 0 ≤ σ z ∧ σ z ≤ τ := by
    apply (ae_restrict_iff' hM).mpr
    filter_upwards [hσ] with z hz hzM
    exact hz hzM.2
  have hlow : 0 ≤ ∫ z in M, σ z ∂μ :=
    integral_nonneg_of_ae (hσM.mono (fun _ hz => hz.1))
  have hhi := integral_mono_ae hσi.integrableOn (integrable_const τ) (hσM.mono
    (fun _ hz => hz.2))
  rw [setIntegral_const, smul_eq_mul] at hhi
  have hτ : 0 ≤ τ := le_max_right _ _
  have hmeasure : μ.real M ≤ μ.real L := by
    exact ENNReal.toReal_mono (measure_ne_top μ L) (measure_mono inter_subset_right)
  have hscaled := mul_le_mul_of_nonneg_right hmeasure hτ
  change (∫ z in M, σ z ∂μ) ∈ Icc 0 (τ * μ.real L)
  exact ⟨hlow, hhi.trans (by nlinarith only [hscaled])⟩

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem aestronglyMeasurable_universalLowGoodErrorRow
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c : ℝ) :
    AEStronglyMeasurable (S.universalLowGoodErrorRow r p d c) μ := by
  let G := PhysicalRepresentative.adjacency W m
  let L := S.universalLowGoodRegion r p d c
  let σ := fun z : Ω => -(S.rootChargeRow r z + S.rootChargeRow p z)
  let f : Ω × Ω → ℝ := fun q => if G q.1 q.2 = false then σ q.2 else 0
  have hf : Measurable f := by
    dsimp only [f, σ]
    exact Measurable.ite
      ((PhysicalRepresentative.measurable_adjacency W m)
        (measurableSet_singleton false))
      ((S.measurable_rootChargeRow r).comp measurable_snd |>.add
        ((S.measurable_rootChargeRow p).comp measurable_snd) |>.neg) measurable_const
  have hm := (hf.aestronglyMeasurable : AEStronglyMeasurable f
    (μ.prod (μ.restrict L))).integral_prod_right'
  convert hm using 1
  funext h
  change (∫ z in {z | G h z = false} ∩ L, σ z ∂μ) =
    ∫ z in L, f (h, z) ∂μ
  have hM : MeasurableSet {z | G h z = false} :=
    (IndependentAtomCopy.measurableSet_missingSection G
      (PhysicalRepresentative.measurable_adjacency W m) h)
  rw [Set.inter_comm, ← setIntegral_indicator hM]
  congr 1
  funext z
  by_cases hz : G h z = false <;> simp [f, σ, hz, Set.indicator]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem aestronglyMeasurable_goodErrorQuotient
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c : ℝ) (x : Ω) :
    AEStronglyMeasurable (fun h => S.universalLowGoodErrorRow r p d c h /
      (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p h -
        S.universalOwnMass x)) μ := by
  have hconst : AEStronglyMeasurable (fun _ : Ω => S.originalAtomMass r) μ :=
    aestronglyMeasurable_const
  have hconst2 : AEStronglyMeasurable (fun _ : Ω => S.universalOwnMass x) μ :=
    aestronglyMeasurable_const
  exact (S.aestronglyMeasurable_universalLowGoodErrorRow r p d c).div₀
    ((hconst.sub (S.aestronglyMeasurable_universalPartnerHoleMissingMass r p)).sub hconst2)

/-- The positive copied-row error on the actual extra hole. The
denominator uses the H-row missing mass and the bad row's own atom. -/
def universalExtraHoleCopyError (S : SelectedHighLowStructure W m)
    (r p : S.I) (d c : ℝ) (x : Ω) : ℝ :=
  ∫ h in S.universalExtraHoleRegion r p,
    S.universalLowGoodErrorRow r p d c h /
      (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p h -
        S.universalOwnMass x) ∂μ

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The corrected extra-hole copied error is measurable on the
original source law up to the representative exception. -/
theorem aestronglyMeasurable_universalExtraHoleCopyError
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c : ℝ) :
    AEStronglyMeasurable (S.universalExtraHoleCopyError r p d c) μ := by
  let E := S.universalExtraHoleRegion r p
  let e := S.universalLowGoodErrorRow r p d c
  let a := S.universalPartnerHoleMissingMass r p
  let u := S.universalOwnMass
  let f : Ω × Ω → ℝ := fun q =>
    e q.2 / (S.originalAtomMass r - a q.2 - u q.1)
  have he : AEStronglyMeasurable (fun q : Ω × Ω => e q.2) (μ.prod μ) :=
    (S.aestronglyMeasurable_universalLowGoodErrorRow r p d c).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  have ha : AEStronglyMeasurable (fun q : Ω × Ω => a q.2) (μ.prod μ) :=
    (S.aestronglyMeasurable_universalPartnerHoleMissingMass r p).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  have hu : AEStronglyMeasurable (fun q : Ω × Ω => u q.1) (μ.prod μ) :=
    ((S.measurable_universalOwnMass).comp measurable_fst).aestronglyMeasurable
  have hc : AEStronglyMeasurable (fun _ : Ω × Ω => S.originalAtomMass r) (μ.prod μ) :=
    aestronglyMeasurable_const
  have hf : AEStronglyMeasurable f (μ.prod μ) :=
    he.div₀ ((hc.sub ha).sub hu)
  have hprod : μ.prod (μ.restrict E) ≤ μ.prod μ :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hm := (hf.mono_measure hprod).integral_prod_right'
  change AEStronglyMeasurable (S.universalExtraHoleCopyError r p d c) μ at hm
  exact hm

/-- The unchanged entire singleton source is joined to every LOW
good-region recipient outside the recovered partner head. -/
theorem ReverseRecovery.ae_singleton_source_lowGood_join
    {S : SelectedHighLowStructure W m} (R : S.ReverseRecovery) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hr : R.plateau = {p}) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.reverseCompulsorySource {p} →
      q.2 ∈ S.universalLowGoodRegion r p d c →
        adjacencyKernel W q.1 q.2 = 1 := by
  have hjoin := R.plateau_source_joined_other hW hd hgap
  filter_upwards [hjoin] with q hq hsource hlow
  have hnotp : S.ρ q.2 ≠ p.val := by
    intro hp
    exact hlow.1.1 (Or.inl (Or.inr hp))
  have hother : q.2 ∈ R.plateauOther := by
    constructor
    · exact (Set.disjoint_right.mp S.hpartition.2.2.2.2.1) hlow.2
    · intro hregion
      have hp : S.ρ q.2 = p.val := by
        simpa [ReverseRecovery.plateauRegion, hr] using hregion
      exact hnotp hp
  apply hq
  · simpa only [hr] using hsource
  · exact hother

/-- The same singleton-source join leaves no LOW good-region physical
missing recipients, so its signed error row vanishes almost everywhere. -/
theorem ReverseRecovery.ae_singleton_source_lowGood_error_zero
    {S : SelectedHighLowStructure W m} (R : S.ReverseRecovery) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hr : R.plateau = {p}) :
    ∀ᵐ h ∂μ.restrict (S.reverseCompulsorySource {p}),
      S.universalLowGoodErrorRow r p d c h = 0 := by
  let G := PhysicalRepresentative.adjacency W m
  let L := S.universalLowGoodRegion r p d c
  have hjoin := R.ae_singleton_source_lowGood_join r p hW hd hgap hr
  have hphys := PhysicalRepresentative.adjacency_moment_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  have hgood : ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.reverseCompulsorySource {p} → q.2 ∈ L → G q.1 q.2 = true := by
    filter_upwards [hjoin, hphys] with q hj hp hs hl
    have hk := hj hs hl
    by_cases hg : G q.1 q.2 = true
    · exact hg
    · have hf : G q.1 q.2 = false := Bool.eq_false_iff.mpr hg
      change adjacencyKernel W q.1 q.2 = _ at hp
      dsimp only [G] at hf
      rw [hf] at hp
      norm_num at hp
      linarith only [hk, hp]
  have hsec := Measure.ae_ae_of_ae_prod hgood
  have hsource : MeasurableSet (S.reverseCompulsorySource {p}) :=
    S.measurableSet_reverseCompulsorySource {p}
  apply (ae_restrict_iff' hsource).mpr
  filter_upwards [hsec] with h hh hs
  have hzero : μ (IndependentAtomCopy.missingSection G h ∩ L) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hh] with z hz hmem
    exact Bool.false_ne_true (hmem.1.symm.trans (hz hs hmem.2))
  change (∫ z in IndependentAtomCopy.missingSection G h ∩ L,
    -(S.rootChargeRow r z + S.rootChargeRow p z) ∂μ) = 0
  exact setIntegral_measure_zero _ hzero

/-- A LOW good-region vertex can miss only its original atom, the extra
partner hole, or the HIGH good region on the original physical law. -/
theorem UniversalPhysicalPrimal.ae_lowGood_missing_recipient_class
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {c : ℝ} (P : S.UniversalPhysicalPrimal r c) (R : S.ReverseRecovery)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hr : R.plateau = {p}) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalLowGoodRegion r p d c →
      PhysicalRepresentative.adjacency W m q.1 q.2 = false →
        q ∈ S.sameAtomRelation ∨
          q.2 ∈ S.universalExtraHoleRegion r p ∨
          q.2 ∈ S.universalHighGoodRegion r p d c := by
  let L := S.universalLowGoodRegion r p d c
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  have hsource := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (R.ae_singleton_source_lowGood_join r p hW hd hgap hr)
  have hbad := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (P.ae_bad_high_low_join S r p hpair hW hd hgap hN hA hAhalf hell hmargin)
  have hroot := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.neutral_atom_physical_adjacency r hW hd hgap hN)
  have hpartner := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_adjacency p hW hd hgap)
  have hNroot := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hN
  have hPnotHigh : ∀ᵐ x ∂μ, S.ρ x = p.val → x ∉ S.H := by
    filter_upwards [compl_mem_ae_iff.mpr
      (hpair.symm.high_head_null hW hd hgap hell.2)] with x hx hp hh
    exact hx ⟨hp, hh⟩
  filter_upwards [hsource, hbad, hroot, hpartner,
    Measure.quasiMeasurePreserving_snd.ae hNroot,
    Measure.quasiMeasurePreserving_snd.ae hPnotHigh,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support,
    (hW.strict_gap_structure hd hgap).strict_support, hW.moment_mem,
    S.ae_zero_iff_sameAtom_or_relation hW hd hgap, S.hrelation,
    adjacencyKernel_symm W] with q hsource hbad hroot hpartner hNroot hPnotHigh
      hphysical hsupport hnonneg hzero hrel hsym hlow hmissing
  have hAdj : adjacencyKernel W q.1 q.2 = 0 := by
    change adjacencyKernel W q.1 q.2 = _ at hphysical
    rw [hphysical, hmissing]
    norm_num
  have hK : shiftedKernel W m q.1 q.2 = 0 := by
    apply le_antisymm _ hnonneg.1
    exact le_of_not_gt (fun hpos => by
      have hone : adjacencyKernel W q.1 q.2 = 1 := by
        change adjacencyKernel W q.1 q.2 =
          (if 0 < shiftedMoment W m q then 1 else 0) at hsupport
        simpa only [ite_eq_left hpos] using hsupport
      linarith only [hAdj, hone])
  rcases hzero.mp hK with hSame | hZ
  · exact Or.inl hSame
  have hHigh : q.2 ∈ S.H := by
    rcases hrel hZ with hcross | hcross
    · exact False.elim ((Set.disjoint_right.mp S.hpartition.2.2.2.2.1) hlow.2
        hcross.1)
    · exact hcross.1
  have hnotRoot : S.ρ q.2 ≠ r.val := by
    intro h
    exact (Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1) hHigh (hNroot h)
  have hnotPartner : S.ρ q.2 ≠ p.val := fun h => hPnotHigh h hHigh
  have hnotSource : q.2 ∉ S.reverseCompulsorySource {p} := by
    intro hc
    have hone := hsource hc hlow
    change adjacencyKernel W q.2 q.1 = 1 at hone
    rw [← hsym] at hone
    linarith only [hAdj, hone]
  have hnotBad : q.2 ∉ B := by
    intro hb
    have hone := hbad hb hHigh hlow.2 (fun hs => hZ.2 hs.1.symm)
    change adjacencyKernel W q.2 q.1 = 1 at hone
    rw [← hsym] at hone
    linarith only [hAdj, hone]
  have hlocation := S.universalPartner_regions_partition r p
  have hmem : q.2 ∈ {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪ H ∪
      S.universalPartnerCommonRegion r p := by
    rw [hlocation]
    trivial
  rcases hmem with ((hr' | hp') | hH) | hU
  · exact False.elim (hnotRoot hr')
  · exact False.elim (hnotPartner hp')
  · exact Or.inr (Or.inl ⟨hH, hnotSource⟩)
  · exact Or.inr (Or.inr ⟨⟨hU, hnotBad⟩, hHigh⟩)

/-- Whole original atom columns retain their common physical adjacency
value even when the source point lies in diffuse dust. -/
private theorem ae_missing_original_atom_column
    (S : SelectedHighLowStructure W m) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ q ∂μ.prod μ, ∀ k : S.I, S.ρ q.2 = k.val →
      PhysicalRepresentative.adjacency W m q.1 q.2 = false →
        ∀ᵐ y ∂μ.restrict {y | S.ρ y = k.val},
          PhysicalRepresentative.adjacency W m q.1 y = false := by
  let : Countable S.I := S.hI.to_subtype
  have hrows : ∀ᵐ q ∂μ.prod μ, ∀ k : S.I, S.ρ q.2 = k.val →
      (PhysicalRepresentative.adjacency W m q.1 q.2 = true ↔
        q.1 ∈ S.rootNeighborhood k) := by
    apply ae_all_iff.mpr
    intro k
    have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (S.ae_root_adjacency k hW hd hgap)
    filter_upwards [hswap] with q hq hk
    have h := hq hk
    change PhysicalRepresentative.adjacency W m q.2 q.1 = true ↔ _ at h
    rw [PhysicalRepresentative.adjacency_symm W m q.2 q.1] at h
    exact h
  filter_upwards [hrows,
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ae_of_ae_prod hrows)]
    with q hq hsection k hk hmissing
  have hnot : q.1 ∉ S.rootNeighborhood k := by
    intro hn
    have h := (hq k hk).mpr hn
    rw [hmissing] at h
    exact Bool.false_ne_true h
  filter_upwards [ae_restrict_of_ae hsection,
    ae_restrict_mem (S.hfibers k.val k.property).1] with y hy hyk
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hnot ((hy k hyk).mp htrue)

private theorem ae_missing_original_atom_column_mass
    (S : SelectedHighLowStructure W m) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ q ∂μ.prod μ, ∀ k : S.I, S.ρ q.2 = k.val →
      PhysicalRepresentative.adjacency W m q.1 q.2 = false →
        μ.real {y | S.ρ y = k.val ∧
          PhysicalRepresentative.adjacency W m q.1 y = false} = S.originalAtomMass k := by
  filter_upwards [S.ae_missing_original_atom_column hW hd hgap] with q hq k hk hmissing
  have hsection := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp (hq k hk hmissing)
  have heq : {y | S.ρ y = k.val ∧ PhysicalRepresentative.adjacency W m q.1 y = false}
      =ᵐ[μ] {y | S.ρ y = k.val} := by
    filter_upwards [hsection] with y hy
    apply propext
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, hy h⟩
  exact congrArg ENNReal.toReal (measure_congr heq)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem universalOwnMass_eq_sameAtom_section
    (S : SelectedHighLowStructure W m) (x : Ω) :
    S.universalOwnMass x = μ.real {z | (x, z) ∈ S.sameAtomRelation} := by
  have hswap : {z | (x, z) ∈ S.sameAtomRelation} =
      {z | (z, x) ∈ S.sameAtomRelation} := by
    ext z
    change (S.ρ x = S.ρ z ∧ S.ρ x ∈ S.I) ↔
      (S.ρ z = S.ρ x ∧ S.ρ z ∈ S.I)
    constructor <;> rintro ⟨h, hI⟩ <;> exact ⟨h.symm, h ▸ hI⟩
  rw [hswap]
  change (S.collapsedPartLabel x).elim 0 S.originalAtomMass = S.ownIndependentMass x
  by_cases hx : S.ρ x ∈ S.I
  · rw [S.ownIndependentMass_eq_fiber (S.ρ x) hx x rfl]
    simp [collapsedPartLabel, HalfGraphMultipartite.collapsedLabel,
      hx, originalAtomMass]
  · rw [S.ownIndependentMass_eq_zero_of_not_mem x hx]
    simp [collapsedPartLabel, HalfGraphMultipartite.collapsedLabel, hx]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Almost every LOW vertex in a positive original whole atom carries
the LOW class on that whole atom. -/
private theorem ae_low_fiber_class (S : SelectedHighLowStructure W m) :
    ∀ᵐ z ∂μ, z ∈ S.L → ∀ k : S.I, S.ρ z = k.val →
      ∀ᵐ y ∂μ.restrict {y | S.ρ y = k.val}, y ∈ S.L := by
  let : Countable S.I := S.hI.to_subtype
  have hall : ∀ᵐ z ∂μ, ∀ k : S.I, z ∈ S.L → S.ρ z = k.val →
      ∀ᵐ y ∂μ.restrict {y | S.ρ y = k.val}, y ∈ S.L := by
    apply ae_all_iff.mpr
    intro k
    rcases S.hfiberClass k.val k.property with hH | hL | hN
    · filter_upwards [(ae_restrict_iff' (S.hfibers k.val k.property).1).mp hH]
        with z hz
      intro hzL hzk
      exact False.elim ((Set.disjoint_left.mp S.hpartition.2.2.2.2.1)
        (hz hzk) hzL)
    · exact Eventually.of_forall (fun _ _ _ => hL)
    · filter_upwards [(ae_restrict_iff' (S.hfibers k.val k.property).1).mp hN]
        with z hz
      intro hzL hzk
      exact False.elim ((Set.disjoint_right.mp S.hpartition.2.2.2.2.2.2)
        (hz hzk) hzL)
  filter_upwards [hall] with z hz
  intro hzL k hk
  exact hz k hzL hk

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A third disjoint missing block adds its full mass to the original
degree and the already counted partner-hole missing integral. -/
private theorem degree_add_hole_extra_mass_le (f : Ω → ℝ) (hf : Integrable f μ)
    (hfle : ∀ y, f y ≤ 1) (P H K : Set Ω)
    (hP : MeasurableSet P) (hH : MeasurableSet H) (hK : MeasurableSet K)
    (hPH : Disjoint P H) (hPK : Disjoint P K)
    (hHK : ∀ᵐ y ∂μ, y ∈ H → y ∉ K)
    (hPzero : ∀ᵐ y ∂μ, y ∈ P → f y = 0)
    (hKzero : ∀ᵐ y ∂μ, y ∈ K → f y = 0) :
    (∫ y, f y ∂μ) + (∫ y in H, 1 - f y ∂μ) + μ.real P + μ.real K ≤ 1 := by
  let φ := fun y => 1 - f y
  have hφ : Integrable φ μ := (integrable_const 1).sub hf
  have hPi : Integrable (P.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hP
  have hHi : Integrable (H.indicator φ) μ := hφ.indicator hH
  have hKi : Integrable (K.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hK
  have hpoint : ∀ᵐ y ∂μ,
      P.indicator (fun _ : Ω => (1 : ℝ)) y + H.indicator φ y +
        K.indicator (fun _ : Ω => (1 : ℝ)) y ≤ φ y := by
    filter_upwards [hHK, hPzero, hKzero] with y hdis hpzero hkzero
    by_cases hp : y ∈ P
    · have hnotH : y ∉ H := (Set.disjoint_left.mp hPH) hp
      have hnotK : y ∉ K := (Set.disjoint_left.mp hPK) hp
      simp only [indicator_of_mem hp, indicator_of_notMem hnotH,
        indicator_of_notMem hnotK, hpzero hp, φ]
      norm_num
    · by_cases hh : y ∈ H
      · have hnotK : y ∉ K := hdis hh
        simp only [indicator_of_notMem hp, indicator_of_mem hh,
          indicator_of_notMem hnotK, zero_add, add_zero]
        exact le_refl _
      · by_cases hk : y ∈ K
        · simp only [indicator_of_notMem hp, indicator_of_notMem hh,
            indicator_of_mem hk, zero_add, hkzero hk, φ]
          norm_num
        · simp only [indicator_of_notMem hp, indicator_of_notMem hh,
            indicator_of_notMem hk, add_zero, φ]
          linarith [hfle y]
  have hbound := integral_mono_ae ((hPi.add hHi).add hKi) hφ hpoint
  have hadd1 : (∫ y, P.indicator (fun _ : Ω => (1 : ℝ)) y + H.indicator φ y +
      K.indicator (fun _ : Ω => (1 : ℝ)) y ∂μ) =
      (∫ y, P.indicator (fun _ : Ω => (1 : ℝ)) y + H.indicator φ y ∂μ) +
        (∫ y, K.indicator (fun _ : Ω => (1 : ℝ)) y ∂μ) := by
    simpa only [Pi.add_apply] using (integral_add (hPi.add hHi) hKi)
  have hadd2 : (∫ y, P.indicator (fun _ : Ω => (1 : ℝ)) y + H.indicator φ y ∂μ) =
      (∫ y, P.indicator (fun _ : Ω => (1 : ℝ)) y ∂μ) +
        (∫ y, H.indicator φ y ∂μ) := integral_add hPi hHi
  change (∫ y, P.indicator (fun _ : Ω => (1 : ℝ)) y + H.indicator φ y +
    K.indicator (fun _ : Ω => (1 : ℝ)) y ∂μ) ≤ ∫ y, φ y ∂μ at hbound
  rw [hadd1, hadd2,
    integral_indicator hP, integral_indicator hH, integral_indicator hK,
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul,
    mul_one, integral_sub (integrable_const 1) hf,
    integral_const, probReal_univ, one_smul] at hbound
  dsimp only [φ] at hbound
  linarith only [hbound]

/-- The literal partner head is absent from each original H row. -/
private theorem ae_partner_original_zero_on_hole
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      ∀ᵐ y ∂μ.restrict {y | S.ρ y = p.val}, adjacencyKernel W x y = 0 := by
  let H := S.universalPartnerHoleRegion r p
  let P := {y | S.ρ y = p.val}
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hle : (μ.restrict P).prod (μ.restrict H) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hzero : ∀ᵐ q ∂(μ.restrict P).prod (μ.restrict H),
      shiftedKernel W m q.1 q.2 = 0 := by
    filter_upwards [ae_mono hle (S.ae_kernel_eq_fiber_row p.val p.property),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hP),
      Measure.quasiMeasurePreserving_snd.ae
        (S.ae_partner_row_zero_on_universalHole r p hW)] with q hrow hp hz
    exact (hrow hp).trans hz
  have hAdjPH : ∀ᵐ q ∂(μ.restrict P).prod (μ.restrict H),
      adjacencyKernel W q.1 q.2 = 0 := by
    filter_upwards [hzero,
      ae_mono hle (hW.strict_gap_structure hd hgap).strict_support]
      with q hz hs
    change adjacencyKernel W q.1 q.2 =
      (if 0 < shiftedKernel W m q.1 q.2 then 1 else 0) at hs
    rw [hz] at hs
    simpa only [lt_irrefl, ↓reduceIte] using hs
  have hswap := (Measure.measurePreserving_swap
    (μ := μ.restrict H) (ν := μ.restrict P)).quasiMeasurePreserving
  have hAdjHP : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict P),
      adjacencyKernel W q.1 q.2 = 0 := by
    have hle' : (μ.restrict H).prod (μ.restrict P) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [hswap.ae hAdjPH, ae_mono hle' (adjacencyKernel_symm W)]
      with q hz hs
    change adjacencyKernel W q.2 q.1 = 0 at hz
    exact hs.trans hz
  exact Measure.ae_ae_of_ae_prod hAdjHP

/-- An extra-hole row missing a LOW good-region point also misses that
point's entire original atom. Its full degree pays both this atom and
the partner plus the H-row missing section. -/
theorem ae_extraHole_missing_lowGood_degree_upper
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerHoleRegion r p →
      q.2 ∈ S.universalLowGoodRegion r p d c →
      PhysicalRepresentative.adjacency W m q.1 q.2 = false →
        (∫ y, adjacencyKernel W q.1 y ∂μ) +
          S.universalPartnerHoleMissingMass r p q.1 +
            S.originalAtomMass p + S.universalOwnMass q.2 ≤ 1 := by
  let H := S.universalPartnerHoleRegion r p
  let P := {y | S.ρ y = p.val}
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hPH : Disjoint P H := disjoint_left.mpr (fun _ hp hh => hh (Or.inl (Or.inr hp)))
  have hHHigh := (ae_restrict_iff' hH).mp
    (S.ae_universalPartnerHole_high r p hpair hW hd hgap hell)
  have hProw := (ae_restrict_iff' hH).mp
    (S.ae_partner_original_zero_on_hole r p hW hd hgap)
  have hbase := (ae_restrict_iff' hH).mp
    (S.ae_hole_degree_add_missing_le_one_sub_partner r p hW hd hgap)
  have hphysRow := Measure.ae_ae_of_ae_prod
    (PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support)
  filter_upwards [S.ae_missing_original_atom_column hW hd hgap,
    Measure.quasiMeasurePreserving_fst.ae hProw,
    Measure.quasiMeasurePreserving_fst.ae hbase,
    Measure.quasiMeasurePreserving_fst.ae hphysRow,
    Measure.quasiMeasurePreserving_snd.ae (S.ae_low_fiber_class),
    Measure.quasiMeasurePreserving_snd.ae
      (S.ae_universalRootDeficit_eq_shifted_row p hW hd hgap)]
    with q hcolumn hpzero hbase hphys hlowClass _ hqH hqL hmissing
  by_cases hI : S.ρ q.2 ∈ S.I
  · let k : S.I := ⟨S.ρ q.2, hI⟩
    let K := {y | S.ρ y = k.val}
    have hK : MeasurableSet K := (S.hfibers k.val k.property).1
    have hk : S.ρ q.2 = k.val := rfl
    have hnotp : k ≠ p := by
      intro he
      have hqp : S.ρ q.2 = p.val := by simpa [he] using hk
      exact hqL.1.1 (Or.inl (Or.inr hqp))
    have hPK : Disjoint P K := disjoint_left.mpr (fun _ hp hk' =>
      hnotp (Subtype.ext (hp.symm.trans hk').symm))
    have hlowK := hlowClass hqL.2 k hk
    have hlowGlobal := (ae_restrict_iff' hK).mp hlowK
    have hHK : ∀ᵐ y ∂μ, y ∈ H → y ∉ K := by
      filter_upwards [hHHigh, hlowGlobal] with y hhigh hlow hyH hyK
      exact (Set.disjoint_left.mp S.hpartition.2.2.2.2.1) (hhigh hyH) (hlow hyK)
    have hzeroPhys := hcolumn k hk hmissing
    have hzeroPhysGlobal := (ae_restrict_iff' hK).mp hzeroPhys
    have hKzero : ∀ᵐ y ∂μ, y ∈ K → adjacencyKernel W q.1 y = 0 := by
      filter_upwards [hphys, hzeroPhysGlobal] with y hEq hzero hyK
      change adjacencyKernel W q.1 y = _ at hEq
      rw [hzero hyK] at hEq
      simpa using hEq
    have hi : Integrable (adjacencyKernel W q.1) μ := Integrable.of_bound
      ((W.stronglyMeasurable_moment
        CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (Eventually.of_forall (fun y => by
        change ‖W.moment CappedColor.adjacency (q.1, y)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (q.1, y)).1]
        exact (adjacency_moment_mem W (q.1, y)).2))
    have hbound := degree_add_hole_extra_mass_le (adjacencyKernel W q.1) hi
      (fun y => (adjacency_moment_mem W (q.1, y)).2) P H K
      hP hH hK hPH hPK hHK ((ae_restrict_iff' hP).mp (hpzero hqH)) hKzero
    have hown : S.universalOwnMass q.2 = S.originalAtomMass k := by
      rw [S.universalOwnMass_eq_sameAtom_section]
      have hsame : {y | (q.2, y) ∈ S.sameAtomRelation} = K := by
        ext y
        change (S.ρ q.2 = S.ρ y ∧ S.ρ q.2 ∈ S.I) ↔ S.ρ y = k.val
        constructor
        · intro h
          exact hk ▸ h.1.symm
        · intro h
          exact ⟨hk.trans h.symm, hI⟩
      rw [hsame]
      rfl
    change (∫ y, adjacencyKernel W q.1 y ∂μ) +
      S.universalPartnerHoleMissingMass r p q.1 +
        S.originalAtomMass p + S.originalAtomMass k ≤ 1 at hbound
    rw [hown]
    linarith only [hbound]
  · have hown : S.universalOwnMass q.2 = 0 := by
      simp [universalOwnMass, collapsedPartLabel,
        HalfGraphMultipartite.collapsedLabel, hI]
    rw [hown]
    have hb := hbase hqH
    change (∫ y, adjacencyKernel W q.1 y ∂μ) +
      S.universalPartnerHoleMissingMass r p q.1 ≤
        1 - S.originalAtomMass p at hb
    linarith only [hb]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem missing_mass_eq_one_sub_degree
    (G : Ω → Ω → Bool) (hG : Measurable (Function.uncurry G)) (x : Ω) :
    μ.real (IndependentAtomCopy.missingSection G x) =
      1 - ∫ z, (if G x z = true then (1 : ℝ) else 0) ∂μ := by
  let E := {z | G x z = true}
  have hE : MeasurableSet E :=
    measurableSet_eq_fun (hG.comp (measurable_const.prodMk measurable_id)) measurable_const
  have hM : IndependentAtomCopy.missingSection G x = Eᶜ := by
    ext z
    cases h : G x z <;> simp [IndependentAtomCopy.missingSection, E, h]
  rw [hM, measureReal_compl hE, probReal_univ]
  have he : E.indicator (fun _ => (1 : ℝ)) =
      fun z => if G x z = true then 1 else 0 := by
    funext z
    simp [Set.indicator, E]
  rw [← he, integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]

/-- The LOW good-region original degree pays its own atom, the extra hole, and the HIGH
good region. -/
theorem UniversalPhysicalPrimal.ae_low_good_original_degree_lower
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (R : S.ReverseRecovery)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (hr : R.plateau = {p}) :
    ∀ᵐ z ∂μ.restrict (S.universalLowGoodRegion r p d c),
      1 - S.universalOwnMass z - μ.real (S.universalExtraHoleRegion r p) -
          μ.real (S.universalHighGoodRegion r p d c) ≤
        ∫ y, adjacencyKernel W z y ∂μ := by
  let G := PhysicalRepresentative.adjacency W m
  let L := S.universalLowGoodRegion r p d c
  let E := S.universalExtraHoleRegion r p
  let H := S.universalHighGoodRegion r p d c
  have hclass := Measure.ae_ae_of_ae_prod
    (P.ae_lowGood_missing_recipient_class S r p hpair R hW hd hgap hN
      hA hAhalf hell hmargin hr)
  have hphysical := Measure.ae_ae_of_ae_prod
    (PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support)
  filter_upwards [ae_restrict_of_ae hclass, ae_restrict_of_ae hphysical,
    ae_restrict_mem (S.measurableSet_universalLowGoodRegion r p d c)]
    with z hz hrow hzL
  let M := IndependentAtomCopy.missingSection G z
  let C := {y | (z, y) ∈ S.sameAtomRelation}
  have hsub : ∀ᵐ y ∂μ, y ∈ M → y ∈ C ∪ E ∪ H := by
    filter_upwards [hz] with y hy hyM
    rcases hy hzL hyM with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hmass := ENNReal.toReal_mono (measure_ne_top μ (C ∪ E ∪ H))
    (measure_mono_ae hsub)
  change μ.real M ≤ μ.real (C ∪ E ∪ H) at hmass
  have hunion := measureReal_union_le (μ := μ) (C ∪ E) H
  have hCE := measureReal_union_le (μ := μ) C E
  have hown : μ.real C = S.universalOwnMass z :=
    (S.universalOwnMass_eq_sameAtom_section z).symm
  have hmissing := missing_mass_eq_one_sub_degree (μ := μ)
    G (PhysicalRepresentative.measurable_adjacency W m) z
  have hdegree : (∫ y, adjacencyKernel W z y ∂μ) =
      ∫ y, (if G z y = true then (1 : ℝ) else 0) ∂μ := by
    apply integral_congr_ae
    exact hrow
  change μ.real M = _ at hmissing
  change 1 - S.universalOwnMass z - μ.real E - μ.real H ≤ _
  rw [hown] at hCE
  linarith only [hmass, hunion, hCE, hmissing, hdegree]

/-- The literal extra hole has the source-subtracted H mass almost everywhere. -/
theorem universal_extra_hole_mass_eq
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    μ.real (S.universalExtraHoleRegion r p) =
      μ.real (S.universalPartnerHoleRegion r p) -
        μ.real (S.reverseCompulsorySource {p}) := by
  let H := S.universalPartnerHoleRegion r p
  let C := S.reverseCompulsorySource {p}
  have hsub := S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell
  have hAE : H ∪ C =ᵐ[μ] H := by
    filter_upwards [hsub] with x hx
    apply propext
    exact ⟨fun h => h.elim id hx, Or.inl⟩
  have hmass : μ.real (H ∪ C) = μ.real H :=
    congrArg ENNReal.toReal (measure_congr hAE)
  change μ.real (H \ C) = μ.real H - μ.real C
  rw [measureReal_sdiff' (S.measurableSet_reverseCompulsorySource {p}), hmass]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_high_low_not_same_atom (S : SelectedHighLowStructure W m) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.H → q.2 ∈ S.L → q ∉ S.sameAtomRelation := by
  let : Countable S.I := S.hI.to_subtype
  have hall : ∀ᵐ q ∂μ.prod μ, ∀ k : S.I,
      S.ρ q.1 = k.val → S.ρ q.2 = k.val → q.1 ∈ S.H → q.2 ∈ S.L → False := by
    apply ae_all_iff.mpr
    intro k
    have hmeas := (S.hfibers k.val k.property).1
    rcases S.hfiberClass k.val k.property with hH | hL | hN
    · have h := (ae_restrict_iff' hmeas).mp hH
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae h] with q hq _ hk _ hlow
      exact disjoint_left.mp S.hpartition.2.2.2.2.1 (hq hk) hlow
    · have h := (ae_restrict_iff' hmeas).mp hL
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae h] with q hq hk _ hhigh _
      exact disjoint_left.mp S.hpartition.2.2.2.2.1 hhigh (hq hk)
    · have h := (ae_restrict_iff' hmeas).mp hN
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae h] with q hq hk _ hhigh _
      exact disjoint_left.mp S.hpartition.2.2.2.2.2.1 hhigh (hq hk)
  filter_upwards [hall] with q hq hhigh hlow hsame
  let k : S.I := ⟨S.ρ q.1, hsame.2⟩
  exact hq k rfl hsame.1.symm hhigh hlow

/-- The actual missing H-to-LOW edge has strict original degree order. -/
theorem ae_hole_low_missing_degree_order
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.universalPartnerHoleRegion r p →
      q.2 ∈ S.universalLowGoodRegion r p d c →
      PhysicalRepresentative.adjacency W m q.1 q.2 = false →
        (∫ y, adjacencyKernel W q.2 y ∂μ) < ∫ y, adjacencyKernel W q.1 y ∂μ := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hhigh := (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mp
    (S.ae_universalPartnerHole_high r p hpair hW hd hgap hell)
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have hdegree : ∀ᵐ x ∂μ, g x = ∫ y, adjacencyKernel W x y ∂μ := by
    have hop := KernelOperator.onL2_coe (adjacencyKernel W)
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      (Lp.const 2 μ (1 : ℝ))
    filter_upwards [hop] with x hx
    change g x = KernelOperator.applyKernel (adjacencyKernel W)
      (Lp.const 2 μ (1 : ℝ)) x at hx
    rw [hx, KernelOperator.applyKernel]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with y hy
    simp only [hy, Function.const_apply, mul_one]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hhigh,
    Measure.quasiMeasurePreserving_fst.ae hdegree,
    Measure.quasiMeasurePreserving_snd.ae hdegree,
    S.ae_high_low_not_same_atom,
    PhysicalRepresentative.adjacency_moment_ae_eq W m hs,
    hs, hW.moment_mem, S.ae_zero_iff_sameAtom_or_relation hW hd hgap,
    S.hrelation] with q hhigh hd1 hd2 hsame hphysical hsupport hnonneg hzero hrel hx hy hmiss
  have hxH := hhigh hx
  have hyL : q.2 ∈ S.L := hy.2
  have hAdj : adjacencyKernel W q.1 q.2 = 0 := by
    change adjacencyKernel W q.1 q.2 = _ at hphysical
    rw [hphysical, hmiss]
    norm_num
  have hK : shiftedKernel W m q.1 q.2 = 0 := by
    apply le_antisymm _ hnonneg.1
    apply le_of_not_gt
    intro hpos
    change adjacencyKernel W q.1 q.2 =
      (if 0 < shiftedMoment W m q then 1 else 0) at hsupport
    rw [ite_eq_left hpos] at hsupport
    linarith only [hAdj, hsupport]
  have hZ : q ∈ actualZeroRelation W m S.ρ := by
    rcases hzero.mp hK with h | h
    · exact False.elim (hsame hxH hyL h)
    · exact h
  have horder : g q.2 < g q.1 := by
    rcases hrel hZ with h | h
    · exact h.2.2
    · exact False.elim (disjoint_left.mp S.hpartition.2.2.2.2.1 h.1 hyL)
  simpa only [hd1, hd2] using horder

/-- An error-bearing extra-hole row has strictly less H missing mass
than the extra hole and the HIGH good region can accommodate after paying P. -/
theorem UniversalPhysicalPrimal.ae_extraHole_error_missing_mass_strict
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {c : ℝ} (P : S.UniversalPhysicalPrimal r c) (R : S.ReverseRecovery)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (hr : R.plateau = {p}) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalExtraHoleRegion r p →
      q.2 ∈ S.universalLowGoodRegion r p d c →
      PhysicalRepresentative.adjacency W m q.1 q.2 = false →
        S.universalPartnerHoleMissingMass r p q.1 <
          μ.real (S.universalExtraHoleRegion r p) +
            μ.real (S.universalHighGoodRegion r p d c) - S.originalAtomMass p := by
  have hL := S.measurableSet_universalLowGoodRegion r p d c
  have hlow := (ae_restrict_iff' hL).mp
    (P.ae_low_good_original_degree_lower S r p hpair R hW hd hgap hN
      hA hAhalf hell hmargin hr)
  filter_upwards [S.ae_extraHole_missing_lowGood_degree_upper r p hpair hW hd hgap hell.2,
    S.ae_hole_low_missing_degree_order r p hpair hW hd hgap hell.2,
    Measure.quasiMeasurePreserving_snd.ae hlow] with q hupper horder hlower hqE hqL hmissing
  have hu := hupper hqE.1 hqL hmissing
  have ho := horder hqE.1 hqL hmissing
  have hl := hlower hqL
  linarith only [hu, ho, hl]

/-- Positive LOW good-region error witnesses a genuine missing edge, so the
strict original-degree comparison applies to almost every such H row. -/
theorem UniversalPhysicalPrimal.ae_extraHole_missing_mass_strict_of_error_pos
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {c : ℝ} (P : S.UniversalPhysicalPrimal r c) (R : S.ReverseRecovery)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (hr : R.plateau = {p}) :
    ∀ᵐ h ∂μ.restrict (S.universalExtraHoleRegion r p),
      0 < S.universalLowGoodErrorRow r p d c h →
        S.universalPartnerHoleMissingMass r p h <
          μ.real (S.universalExtraHoleRegion r p) +
            μ.real (S.universalHighGoodRegion r p d c) - S.originalAtomMass p := by
  let E := S.universalExtraHoleRegion r p
  let L := S.universalLowGoodRegion r p d c
  have hE : MeasurableSet E := S.measurableSet_universalExtraHoleRegion r p
  have hL : MeasurableSet L := S.measurableSet_universalLowGoodRegion r p d c
  have hsec := Measure.ae_ae_of_ae_prod
    (P.ae_extraHole_error_missing_mass_strict S r p hpair R hW hd hgap
      hN hA hAhalf hell hmargin hr)
  filter_upwards [ae_restrict_of_ae hsec, ae_restrict_mem hE] with h hs hh hpos
  let M := IndependentAtomCopy.missingSection
    (PhysicalRepresentative.adjacency W m) h ∩ L
  have hM : MeasurableSet M :=
    (IndependentAtomCopy.measurableSet_missingSection
      (PhysicalRepresentative.adjacency W m)
      (PhysicalRepresentative.measurable_adjacency W m) h).inter hL
  have hMpos : 0 < μ M := by
    by_contra hn
    have hzero : μ M = 0 := le_antisymm (le_of_not_gt hn) bot_le
    have heq : S.universalLowGoodErrorRow r p d c h = 0 := by
      change (∫ z in M,
        -(S.rootChargeRow r z + S.rootChargeRow p z) ∂μ) = 0
      exact setIntegral_measure_zero _ hzero
    linarith only [hpos, heq]
  have hgood : ∀ᵐ z ∂μ.restrict M,
      S.universalPartnerHoleMissingMass r p h <
        μ.real E + μ.real (S.universalHighGoodRegion r p d c) -
          S.originalAtomMass p := by
    apply (ae_restrict_iff' hM).mpr
    filter_upwards [hs] with z hz hzM
    exact hz hh hzM.2 hzM.1
  obtain ⟨z, _, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hMpos.ne' hgood
  exact hz

private theorem ae_missing_sameAtom_section_mass
    (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ,
      μ.real (IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) x ∩
          {z | (x, z) ∈ S.sameAtomRelation}) = S.universalOwnMass x := by
  let G := PhysicalRepresentative.adjacency W m
  have hzero : ∀ᵐ q ∂μ.prod μ,
      q ∈ S.sameAtomRelation → G q.1 q.2 = false := by
    filter_upwards [S.ae_zero_iff_sameAtom_or_relation hW hd hgap,
      (hW.strict_gap_structure hd hgap).strict_support,
      PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support]
      with q hiff hs hphys hsame
    have hM : shiftedKernel W m q.1 q.2 = 0 := hiff.mpr (Or.inl hsame)
    change adjacencyKernel W q.1 q.2 =
      (if 0 < shiftedKernel W m q.1 q.2 then (1 : ℝ) else 0) at hs
    rw [hM] at hs
    change adjacencyKernel W q.1 q.2 =
      (if G q.1 q.2 = true then (1 : ℝ) else 0) at hphys
    rw [hs] at hphys
    by_cases hg : G q.1 q.2 = true
    · simp [hg] at hphys
    · exact Bool.eq_false_iff.mpr hg
  have hsec := Measure.ae_ae_of_ae_prod hzero
  filter_upwards [hsec] with x hx
  have hmass : μ.real (IndependentAtomCopy.missingSection G x ∩
      {z | (x, z) ∈ S.sameAtomRelation}) =
      μ.real {z | (x, z) ∈ S.sameAtomRelation} := by
    apply measureReal_congr
    filter_upwards [hx] with z hz
    exact propext ⟨fun h => h.2, fun h => ⟨hz h, h⟩⟩
  exact hmass.trans (S.universalOwnMass_eq_sameAtom_section x).symm

/-- The original bad-degree cap also caps the mass of its actual
independent whole atom, including a zero-mass diffuse point. -/
theorem UniversalPhysicalPrimal.ae_negative_own_mass_le_first_cap
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalOwnMass x ≤
        1 - 3 * S.originalAtomMass r + S.originalAtomMass p := by
  let G := PhysicalRepresentative.adjacency W m
  let M := fun x => IndependentAtomCopy.missingSection G x
  let B := S.universalUpperE2BadRegion r p d c
  let Neg := S.universalNegativeRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalUpperE2BadRegion r p d c
  have hNeg : MeasurableSet Neg := S.measurableSet_universalNegativeRegion r p
  have hsubset : Neg ⊆ B := S.universalNegativeRegion_subset_upperE2Bad r p d c
    (by linarith only [hA]) hmargin (by linarith only [hell.2])
  have hdegree := (ae_restrict_iff' hB).mp
    (P.ae_universalUpperE2Bad_originalDegree_ge S r p hpair hW hd hgap
      hN hA hAhalf hell hmargin)
  have hphys := Measure.ae_ae_of_ae_prod
    (PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support)
  have hown := S.ae_missing_sameAtom_section_mass hW hd hgap
  apply (ae_restrict_iff' hNeg).mpr
  filter_upwards [hdegree, hphys, hown] with x hdg hrow hown hx
  have hxB := hsubset hx
  have hownLe : S.universalOwnMass x ≤ μ.real (M x) := by
    rw [← hown]
    exact ENNReal.toReal_mono (measure_ne_top μ (M x))
      (measure_mono inter_subset_left)
  have hmissing := missing_mass_eq_one_sub_degree (μ := μ)
    G (PhysicalRepresentative.measurable_adjacency W m) x
  have hrowEq : (∫ y, adjacencyKernel W x y ∂μ) =
      ∫ y, (if G x y = true then (1 : ℝ) else 0) ∂μ := by
    apply integral_congr_ae
    exact hrow
  change μ.real (M x) = _ at hmissing
  linarith only [hownLe, hmissing, hrowEq, hdg hxB]

/-- The same good-region mass pays the strict copied denominator whenever
the LOW good-region error is positive. Neutral good-region mass is retained. -/
theorem UniversalPhysicalPrimal.ae_extraHole_copy_denominator_strict
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {c : ℝ} (P : S.UniversalPhysicalPrimal r c) (R : S.ReverseRecovery)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (hr : R.plateau = {p}) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      ∀ᵐ h ∂μ.restrict (S.universalExtraHoleRegion r p),
        0 < S.universalLowGoodErrorRow r p d c h →
          6 * S.originalAtomMass r - 2 +
              μ.real (S.universalUpperE2BadRegion r p d c) +
                μ.real (S.universalLowGoodRegion r p d c) <
            S.originalAtomMass r - S.universalPartnerHoleMissingMass r p h -
              S.universalOwnMass x := by
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  let Good := S.universalGoodCommonRegion r p d c
  let L := S.universalLowGoodRegion r p d c
  let J := S.universalHighGoodRegion r p d c
  let E := S.universalExtraHoleRegion r p
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalUpperE2BadRegion r p d c
  have hGood : MeasurableSet Good := S.measurableSet_universalGoodCommonRegion r p d c
  have hL : MeasurableSet L := S.measurableSet_universalLowGoodRegion r p d c
  have hJ : MeasurableSet J := S.measurableSet_universalHighGoodRegion r p d c
  have hsubset := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  have hUunion : U ∪ B =ᵐ[μ] U := by
    filter_upwards [hsubset] with x hx
    apply propext
    exact ⟨fun h => h.elim id hx, Or.inl⟩
  have hmassUB : μ.real U = μ.real B + μ.real Good := by
    have hmass : μ.real Good = μ.real U - μ.real B := by
      change μ.real (U \ B) = _
      rw [measureReal_sdiff' hB]
      have heqMass : μ.real (U ∪ B) = μ.real U :=
        congrArg ENNReal.toReal (measure_congr hUunion)
      rw [heqMass]
    have hBle : μ.real B ≤ μ.real U := ENNReal.toReal_mono (measure_ne_top μ U)
      (measure_mono_ae hsubset)
    linarith only [hmass, hBle]
  have hLJ : Disjoint L J := disjoint_left.mpr (fun _ hx hy =>
    (Set.disjoint_right.mp S.hpartition.2.2.2.2.1) hx.2 hy.2)
  have hLJsub : L ∪ J ⊆ Good := fun _ hx => hx.elim (fun h => h.1) (fun h => h.1)
  have hmassLJ : μ.real L + μ.real J ≤ μ.real Good := by
    rw [← measureReal_union hLJ hJ]
    exact ENNReal.toReal_mono (measure_ne_top μ Good) (measure_mono hLJsub)
  have hκ := (R.universal_partner_source_mass_margin r p hpair hW hd hgap
    hell.2 hr hN).2
  have hEmass := S.universal_extra_hole_mass_eq r p hpair hW hd hgap hell.2
  rw [← hEmass] at hκ
  have hown := P.ae_negative_own_mass_le_first_cap S r p hpair hW hd hgap
    hN hA hAhalf hell hmargin
  have hstrict := P.ae_extraHole_missing_mass_strict_of_error_pos
    S r p hpair R hW hd hgap hN hA hAhalf hell hmargin hr
  filter_upwards [hown] with x hx
  filter_upwards [hstrict] with h hh he
  have hs := hh he
  dsimp only [U, B, Good, L, J, E] at *
  linarith only [hx, hs, hκ, hmassUB, hmassLJ]

/-- The original extra-hole copy error uses the full good-region mass in its
denominator payment, including neutral good-region vertices. -/
theorem UniversalPhysicalPrimal.ae_universalExtraHoleCopyError_le
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {c : ℝ} (P : S.UniversalPhysicalPrimal r c) (R : S.ReverseRecovery)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (hr : R.plateau = {p})
    (hu : 0 < μ.real (S.universalPartnerCommonRegion r p)) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      Integrable (fun h => S.universalLowGoodErrorRow r p d c h /
        (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p h -
          S.universalOwnMass x)) (μ.restrict (S.universalExtraHoleRegion r p)) ∧
      S.universalExtraHoleCopyError r p d c x ≤
        μ.real (S.universalExtraHoleRegion r p) *
          (max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
            (1 + m))) 0 * μ.real (S.universalGoodCommonRegion r p d c) /
              μ.real (S.universalPartnerCommonRegion r p)) := by
  let U := S.universalPartnerCommonRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  let Good := S.universalGoodCommonRegion r p d c
  let L := S.universalLowGoodRegion r p d c
  let E := S.universalExtraHoleRegion r p
  let τ := max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
    (1 + m))) 0
  let e := S.universalLowGoodErrorRow r p d c
  let den := fun x h => S.originalAtomMass r -
    S.universalPartnerHoleMissingMass r p h - S.universalOwnMass x
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalUpperE2BadRegion r p d c
  have hGood : MeasurableSet Good := S.measurableSet_universalGoodCommonRegion r p d c
  have hL : MeasurableSet L := S.measurableSet_universalLowGoodRegion r p d c
  have hsub := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  have hmassBGood : μ.real U = μ.real B + μ.real Good := by
    have hmass : μ.real Good = μ.real U - μ.real B := by
      change μ.real (U \ B) = _
      rw [measureReal_sdiff' hB]
      have heq : μ.real (U ∪ B) = μ.real U :=
        congrArg ENNReal.toReal (measure_congr (by
          filter_upwards [hsub] with x hx
          exact propext ⟨fun h => h.elim id hx, Or.inl⟩))
      rw [heq]
    have hBle : μ.real B ≤ μ.real U := ENNReal.toReal_mono (measure_ne_top μ U)
      (measure_mono_ae hsub)
    linarith only [hmass, hBle]
  have hLsub : L ⊆ Good := fun _ hx => hx.1
  have hLle : μ.real L ≤ μ.real Good := ENNReal.toReal_mono
    (measure_ne_top μ Good) (measure_mono hLsub)
  have hB0 : 0 ≤ μ.real B := measureReal_nonneg
  have hL0 : 0 ≤ μ.real L := measureReal_nonneg
  have hGdiff : 0 ≤ μ.real Good - μ.real L := sub_nonneg.mpr hLle
  have hτ : 0 ≤ τ := le_max_right _ _
  have hc : 0 < 6 * S.originalAtomMass r - 2 := by linarith only [hA]
  have he : ∀ h, 0 ≤ e h ∧ e h ≤ τ * μ.real L :=
    fun h => S.universalLowGoodErrorRow_mem_Icc r p hpair hW hd hgap hN h
  have hden := P.ae_extraHole_copy_denominator_strict S r p hpair R hW hd hgap
    hN hA hAhalf hell hmargin hr
  filter_upwards [hden] with x hx
  have hsm : AEStronglyMeasurable (fun h => e h / den x h)
      (μ.restrict E) := by
    exact (S.aestronglyMeasurable_goodErrorQuotient r p d c x).mono_measure
      Measure.restrict_le_self
  have heE : ∀ᵐ h ∂μ.restrict E, 0 ≤ e h ∧ e h ≤ τ * μ.real L :=
    Eventually.of_forall he
  have hdenE : ∀ᵐ h ∂μ.restrict E,
      0 < e h → 6 * S.originalAtomMass r - 2 + μ.real B + μ.real L ≤ den x h := by
    filter_upwards [hx] with h hh hp
    exact (hh hp).le
  have hu' : 0 < μ.real B + μ.real L + (μ.real Good - μ.real L) := by
    linarith only [hu, hmassBGood]
  have hresult := UpperE2UniversalScalar.good_error_integral_le
    E e (den x) (6 * S.originalAtomMass r - 2) (μ.real B) (μ.real L)
    (μ.real Good - μ.real L) τ hc hB0 hL0 hGdiff hτ hu' hsm heE hdenE
  constructor
  · exact hresult.1
  · change (∫ h in E, e h / den x h ∂μ) ≤ _
    rw [hmassBGood]
    convert hresult.2 using 1
    ring

/-- The original full-hole copied error equals its extra-hole part:
the entire singleton source has zero LOW good-region error almost everywhere. -/
theorem UniversalPhysicalPrimal.ae_universalHoleCopyError_eq_extra
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {c : ℝ} (P : S.UniversalPhysicalPrimal r c) (R : S.ReverseRecovery)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (hr : R.plateau = {p})
    (hu : 0 < μ.real (S.universalPartnerCommonRegion r p)) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      Integrable (fun h => S.universalLowGoodErrorRow r p d c h /
        (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p h -
          S.universalOwnMass x))
        (μ.restrict (S.universalPartnerHoleRegion r p)) ∧
      (∫ h in S.universalPartnerHoleRegion r p,
        S.universalLowGoodErrorRow r p d c h /
          (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p h -
            S.universalOwnMass x) ∂μ) =
        S.universalExtraHoleCopyError r p d c x := by
  let H := S.universalPartnerHoleRegion r p
  let T := S.reverseCompulsorySource {p}
  let E := S.universalExtraHoleRegion r p
  let J := H ∩ T
  let f := fun x h => S.universalLowGoodErrorRow r p d c h /
    (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p h -
      S.universalOwnMass x)
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hT : MeasurableSet T := S.measurableSet_reverseCompulsorySource {p}
  have hE : MeasurableSet E := S.measurableSet_universalExtraHoleRegion r p
  have hJ : MeasurableSet J := hH.inter hT
  have hpart : E ∪ J = H := by
    ext h
    change (h ∈ H ∧ h ∉ T) ∨ (h ∈ H ∧ h ∈ T) ↔ h ∈ H
    tauto
  have hdis : Disjoint E J := by
    apply disjoint_left.mpr
    intro h hh hj
    exact hh.2 hj.2
  have hzero := (ae_restrict_iff' hT).mp
    (R.ae_singleton_source_lowGood_error_zero r p hW hd hgap hr)
  have hIntE := P.ae_universalExtraHoleCopyError_le S r p hpair R hW hd hgap
    hN hA hAhalf hell hmargin hr hu
  filter_upwards [hIntE] with x hx
  have hzeroJ : ∀ᵐ h ∂μ.restrict J, f x h = 0 := by
    apply (ae_restrict_iff' hJ).mpr
    filter_upwards [hzero] with h hh hj
    simp only [f, hh hj.2, zero_div]
  have hIntJ : Integrable (f x) (μ.restrict J) := by
    rw [integrable_congr hzeroJ]
    change Integrable (fun _ : Ω => (0 : ℝ)) (μ.restrict J)
    exact integrable_zero Ω ℝ (μ.restrict J)
  have hIntEx : Integrable (f x) (μ.restrict E) := hx.1
  constructor
  · change Integrable (f x) (μ.restrict H)
    rw [← hpart]
    exact integrableOn_union.mpr ⟨hIntEx, hIntJ⟩
  · change (∫ h in H, f x h ∂μ) = _
    rw [← hpart, setIntegral_union hdis hJ hIntEx hIntJ]
    have hzeroInt : (∫ h in J, f x h ∂μ) = 0 := by
      rw [integral_congr_ae hzeroJ]
      simp
    rw [hzeroInt, add_zero]
    rfl

/-- The corrected copied error is an integrable nonnegative row
allowance on the original negative common region. -/
theorem UniversalPhysicalPrimal.integrable_universalExtraHoleCopyError
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {c : ℝ} (P : S.UniversalPhysicalPrimal r c) (R : S.ReverseRecovery)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (hr : R.plateau = {p})
    (hu : 0 < μ.real (S.universalPartnerCommonRegion r p)) :
    Integrable (S.universalExtraHoleCopyError r p d c)
      (μ.restrict (S.universalNegativeRegion r p)) ∧
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      0 ≤ S.universalExtraHoleCopyError r p d c x := by
  let E := S.universalExtraHoleRegion r p
  let L := S.universalLowGoodRegion r p d c
  let U := S.universalPartnerCommonRegion r p
  let Good := S.universalGoodCommonRegion r p d c
  let τ := max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
    (1 + m))) 0
  let C := μ.real E * (τ * μ.real Good / μ.real U)
  let e := S.universalLowGoodErrorRow r p d c
  let den := fun x h => S.originalAtomMass r -
    S.universalPartnerHoleMissingMass r p h - S.universalOwnMass x
  have he : ∀ h, 0 ≤ e h := fun h =>
    (S.universalLowGoodErrorRow_mem_Icc r p hpair hW hd hgap hN h).1
  have hden := P.ae_extraHole_copy_denominator_strict S r p hpair R hW hd hgap
    hN hA hAhalf hell hmargin hr
  have hnonneg : ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      0 ≤ S.universalExtraHoleCopyError r p d c x := by
    filter_upwards [hden] with x hx
    have hquot : ∀ᵐ h ∂μ.restrict E, 0 ≤ e h / den x h := by
      filter_upwards [hx] with h hh
      by_cases hp : 0 < e h
      · have hB0 : 0 ≤ μ.real (S.universalUpperE2BadRegion r p d c) :=
          measureReal_nonneg
        have hL0 : 0 ≤ μ.real L := measureReal_nonneg
        have hpos : 0 < den x h := by
          have hstrict := hh hp
          dsimp only [den, L] at *
          linarith only [hstrict, hA, hB0, hL0]
        exact div_nonneg (he h) hpos.le
      · have hz : e h = 0 := le_antisymm (le_of_not_gt hp) (he h)
        simp [hz]
    change 0 ≤ ∫ h in E, e h / den x h ∂μ
    exact integral_nonneg_of_ae hquot
  have hupper := (P.ae_universalExtraHoleCopyError_le S r p hpair R hW hd
    hgap hN hA hAhalf hell hmargin hr hu).mono (fun _ hx => hx.2)
  have hbound : ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      ‖S.universalExtraHoleCopyError r p d c x‖ ≤ C := by
    filter_upwards [hnonneg, hupper] with x hx hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using hy
  have hmeas : AEStronglyMeasurable (S.universalExtraHoleCopyError r p d c)
      (μ.restrict (S.universalNegativeRegion r p)) :=
    (S.aestronglyMeasurable_universalExtraHoleCopyError r p d c).mono_measure
      Measure.restrict_le_self
  exact ⟨Integrable.of_bound hmeas C hbound, hnonneg⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
