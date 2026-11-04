module

public import Erdos1017.Exclusions.E2.Middle.MiddleE2UniversalParameterGuards
public import Erdos1017.Exclusions.E2.Middle.MiddleE2UniversalLowParameterScalar
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSharpMissingCap
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSharpDiffuseCap
public import Erdos1017.Exclusions.Common.ConditionalMissingMassCap
public import Erdos1017.Exclusions.E2.Middle.SelectedUniversalIntegratedDeficitFloor
public import Erdos1017.Exclusions.Common.Universal.SelectedTwoUniversalE2

/-!
# No universal saturated peak on the low middle parameters

Every universal saturated common peak is excluded on the closed low
middle-parameter range, using its small ratio, small head, and all atomic and
diffuse bounds (`no_universal_middle_low_parameter_saturated_peak`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

private theorem low_parameter_partner_universal_of_empty_holes (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hnull : μ (S.universalPartnerHoleRegion r p) = 0) :
    ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = p.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = p.val then 0 else 1 := by
  have hnotH : ∀ᵐ x ∂μ, x ∉ S.universalPartnerHoleRegion r p :=
    compl_mem_ae_iff.mpr hnull
  have hSAT := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hpair.symm.row_on_other
  have hmneg := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hsets : ∀ᵐ x ∂μ, x ∈ S.rootNeighborhood p ↔ S.ρ x ≠ p.val := by
    filter_upwards [hnotH, hSAT] with x hn hs
    constructor
    · exact fun h => h.1
    · intro hxp
      by_cases hxr : S.ρ x = r.val
      · exact ⟨hxp, by rw [hs hxr]; linarith only [hmneg]⟩
      · by_contra hnot
        exact hn (by
          intro hh
          rcases hh with (hh | hh) | hh
          · exact hxr hh
          · exact hxp hh
          · exact hnot hh)
  filter_upwards [S.ae_root_adjacency p hW hd hgap,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support,
    Measure.quasiMeasurePreserving_snd.ae hsets] with z hz ha hs hzp
  change adjacencyKernel W z.1 z.2 =
    (if PhysicalRepresentative.adjacency W m z.1 z.2 = true then 1 else 0) at ha
  by_cases hy : S.ρ z.2 = p.val
  · have hf : PhysicalRepresentative.adjacency W m z.1 z.2 = false :=
      Bool.eq_false_iff.mpr (fun he => (hs.mp ((hz hzp).mp he)) hy)
    simpa only [hf, Bool.false_eq_true, ite_false, hy, ite_true] using ha
  · have ht := (hz hzp).mpr (hs.mpr hy)
    simpa only [ht, ite_true, hy, ite_false] using ha

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem low_parameter_hole_partner_mass_le_outside
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hW : FullStationaryClass d c W m) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.originalAtomMass p ≤ S.outsideSectionMass x := by
  filter_upwards [S.ae_partner_row_zero_on_universalHole r p hW,
    ae_restrict_of_ae (S.ae_atomMass_le_outsideSectionMass_on_missing hW p),
    ae_restrict_mem (S.measurableSet_universalPartnerHoleRegion r p)] with x hx hb hxH
  apply hb
  exact ⟨fun he => hxH (Or.inl (Or.inr he)), by rw [hx]⟩

/-- Every actual universal saturated common peak is excluded on the
closed low middle-parameter range. Its small ratio and small head, as well
as all atomic and diffuse entire-hole caps, are derived internally. -/
theorem no_universal_middle_low_parameter_saturated_peak
    (S : SelectedHighLowStructure W m) (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Icc (7 / 50 : ℝ) (157 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = r.val then 0 else 1) : False := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let eta := μ.real (S.universalPartnerHoleRegion r p)
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let ybar : ℝ := 1 / 3
  let C := 1 / 5 - b
  let x := ybar - A
  let P := ybar - u
  let N := 2 / 15 + x
  let w := N + C
  have hqCoarse : q ∈ Icc (7 / 50 : ℝ) (1 / 5) :=
    ⟨hq.1, by linarith only [hq.2]⟩
  have hq' : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨by linarith only [hq.1], hqCoarse.2⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ Benchmark.e2_density_mem hq'
  obtain ⟨hm, hell, hgamma⟩ := hW.e2_gamma_floor hq' hdq hgap hglobal
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  have hell23 : 2 / 3 ≤ -m := by
    rw [hneg]
    unfold LowerE2Scalar.multiplier
    rw [le_div_iff₀ (by linarith only [hq.1])]
    linarith only [hq.2]
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  have hnonlow : ∀ᵐ v ∂μ.restrict {v | S.ρ v = r.val}, v ∉ S.L :=
    hN.mono (fun _ hv hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hv)
  have hholes : 0 < μ (S.universalPartnerHoleRegion r p) := by
    apply bot_lt_iff_ne_bot.mpr
    intro hnull
    exact hpair.not_both_universal_e2 hW hq' hdq hgap hglobal huniv
      (S.low_parameter_partner_universal_of_empty_holes r p hpair hW hd hgap hnull)
  have hdelta : 0 < 1 + m := by linarith only [hell.2]
  have hdef : 1 - m - 4 * (c - m * d) <
      (1 + m) * (9 * q / (2 * LowerE2Scalar.denominator q)) := by
    have href := LowerE2Scalar.deficit_eq_gap_mul_ratio hq'.1.le
    rw [← hneg] at href
    nlinarith only [href, hgamma]
  have hyupper : (1 - m - 4 * (c - m * d)) / (1 + m) <
      9 * q / (2 * LowerE2Scalar.denominator q) :=
    (div_lt_iff₀ hdelta).mpr (by nlinarith only [hdef])
  have hratio : 9 * q / (2 * LowerE2Scalar.denominator q) ≤ ybar := by
    have hh := LowerE2Scalar.universal_ratio_monotoneOn_middle
      ⟨hq'.1.le, hqCoarse.2⟩
      (by norm_num : (157 / 1000 : ℝ) ∈ Icc (0 : ℝ) (1 / 5)) hq.2
    norm_num [LowerE2Scalar.denominator] at hh
    dsimp only [ybar, LowerE2Scalar.denominator]
    linarith only [hh]
  have hy : (1 - m - 4 * (c - m * d)) / (1 + m) ≤ ybar := hyupper.le.trans hratio
  have hAy := S.universal_atom_mass_le_saturated_deficit_ratio
    r p hpair hW hd hgap hell.2 hN hholes
  have hsmallHead : S.originalAtomMass r ≤ 1 / 3 := hAy.trans hy
  obtain ⟨hDelta, i, hquarter, _, hi, _, _, _, _⟩ :=
    S.exists_original_forward_quarter_peak hW ⟨by linarith only [hq.1], hqCoarse.2⟩
      hdq hgap hglobal
  have hir : i = r := (hi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  have hA : S.originalAtomMass r ∈ Icc (1 / 4 : ℝ) (1 / 3) :=
    ⟨by simpa only [hir] using hquarter.le, hsmallHead⟩
  have hatomic : ∀ j : S.I, j ≠ r →
      (∀ᵐ v ∂μ.restrict {v | S.ρ v = j.val}, v ∈ S.H) →
      S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) < 1 / 5 := by
    intro j hjr hjH
    have hbudget := S.middle_high_atom_closed_missing_sq_bound
      r j hjr hW hd hgap hpeak hnonlow hjH hA hell23
    rw [hneg] at hbudget
    exact MiddleE2UniversalLowParameter.closed_missing_lt_fifth hqCoarse hgamma hbudget
  have hmargin := MiddleE2UniversalLowParameter.selector_margin (A := A) hqCoarse
  rw [← hneg] at hmargin
  have hdiffuse := S.ae_middle_diffuse_high_outside_le r hW hd hgap hpeak hnonlow hA
    hell23 (R := 1 / 5) (by norm_num) (by linarith only [hA.1])
    (by dsimp only [A] at hmargin; linarith only [hmargin, hgamma])
  have hrecipients := S.ae_nonpeak_high_outside_le hW r (1 / 5)
    (fun j hjr hjH => (hatomic j hjr hjH).le) hdiffuse
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hHhigh := S.ae_universalPartnerHole_high r p hpair hW hd hgap hell.2
  have hsections : ∀ᵐ v ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.outsideSectionMass v ≤ 1 / 5 := by
    filter_upwards [ae_restrict_of_ae hrecipients, hHhigh, ae_restrict_mem hH]
      with v hv hvH hvHole
    exact hv hvH (fun he => hvHole (Or.inl (Or.inl he)))
  have hbOutside := S.low_parameter_hole_partner_mass_le_outside r p hW
  have hbcap : b ≤ 1 / 5 := by
    obtain ⟨v, _, hvb, hvcap⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hholes.ne' (hbOutside.and hsections)
    exact hvb.trans hvcap
  have hC : 0 ≤ C := sub_nonneg.mpr hbcap
  have hparts : ∀ j : S.I, (∀ᵐ v ∂μ.restrict {v | S.ρ v = j.val},
      v ∈ S.universalPartnerHoleRegion r p) → S.originalAtomMass j ≤ C := by
    intro j hwhole
    have hIj := S.hfibers j.val j.property
    obtain ⟨v, hvj, hvHole⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hIj.2.1.ne' hwhole
    have hjr : j ≠ r := fun he => hvHole (Or.inl (Or.inl
      (hvj.trans (congrArg Subtype.val he))))
    have hjH : ∀ᵐ v ∂μ.restrict {v | S.ρ v = j.val}, v ∈ S.H := by
      have hg := (ae_restrict_iff' hH).mp hHhigh
      filter_upwards [hwhole, ae_restrict_of_ae hg] with v hv hh
      exact hh hv
    have hclosed := hatomic j hjr hjH
    have houtside := S.ae_outsideSectionMass_eq_missingRegion_on_fiber hW j j.property
    have hbGlobal := (ae_restrict_iff' hH).mp hbOutside
    obtain ⟨v, _, hvHole, hvb, hvEq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hIj.2.1.ne' (hwhole.and ((ae_restrict_of_ae hbGlobal).and houtside))
    have hbmissing : b ≤ μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
      rw [← hvEq]
      exact hvb hvHole
    dsimp only [C]
    linarith only [hclosed, hbmissing]
  have hmass := S.universalPartner_regions_mass r p hpair.1
  change A + b + eta + u = 1 at hmass
  have hu : 0 ≤ u := measureReal_nonneg
  have heta : 0 ≤ eta := measureReal_nonneg
  have hremain : 0 < eta - C - (ybar - u) := by
    dsimp only [C, ybar]
    change A ≤ 1 / 3 at hsmallHead
    linarith only [hmass, hsmallHead]
  have hcoef : 0 ≤ eta + u - A := by
    change A ≤ 1 / 3 at hsmallHead
    linarith only [hmass, hsmallHead, hbcap]
  obtain ⟨hhalf, _, _⟩ := S.universal_integrated_atomic_deficit_floor
    r p hpair hW hd hgap hell.2 hN hy hC hparts hremain
  change eta / 2 ≤ P at hhalf
  have hp0 : 0 ≤ P := by linarith only [heta, hhalf]
  have hp : P ≤ 1 / 3 := by dsimp only [P, ybar]; linarith only [hu]
  have hx : 0 ≤ x := by
    dsimp only [x, ybar]
    linarith only [hsmallHead]
  have hpolys := S.universal_deficit_three_polynomials
    r p hpair hW hd hgap hell.2 hN hy le_rfl hC hparts hremain hcoef
  have hfirst := hpolys.2.1
  change 0 ≤ (2 * P - eta) * C * eta -
    ((1 - A - b - ybar) ^ 2 - x * P) * (eta - 2 * C) at hfirst
  have hw : w = 1 - A - b - ybar := by dsimp only [w, N, x, C, ybar]; ring
  have hetaEq : P + w = eta := by rw [hw]; dsimp only [P]; linarith only [hmass]
  have hfactor : eta - 2 * C = P + N - C := by rw [← hetaEq]; dsimp only [w]; ring
  have hprod : (2 * P - eta) * C * eta = C * (P ^ 2 - w ^ 2) := by
    rw [← hetaEq]
    ring
  rw [← hw, hfactor, hprod] at hfirst
  have hnegative := MiddleE2UniversalLowParameter.first_polynomial_neg hx hC hp0 hp
  change C * (P ^ 2 - w ^ 2) - (w ^ 2 - x * P) * (P + N - C) < 0 at hnegative
  exact (not_lt_of_ge hfirst) hnegative

end Erdos1017.CappedModel.SelectedHighLowStructure
