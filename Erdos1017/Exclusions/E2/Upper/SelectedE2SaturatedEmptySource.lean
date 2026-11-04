module

public import Erdos1017.Exclusions.Common.E2.SelectedEmptySatE2Inventory
public import Erdos1017.Exclusions.Common.SelectedEmptySource
public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards
public import Erdos1017.Exclusions.Common.Universal.SelectedTwoUniversalGeometry
public import Erdos1017.Exclusions.E2.Upper.UpperE2TwoUniversalScalar
public import Erdos1017.Exclusions.E2.Upper.UpperE2ParameterGuards
public import Erdos1017.Exclusions.Common.Universal.TwoUniversalE2Scalar

/-!
# No saturated head with empty source

A singleton reverse recovery with null entire source and a saturated recovered
head is impossible at an `E₂` contact with `0 < q ≤ 213/1000`
(`no_e2_saturated_empty_source`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.EmptySatE2

private theorem baseCredit_pos {δ A D : ℝ} (hδ : δ ∈ Icc (18 / 109 : ℝ) (1 / 5))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D) (hD : D ≤ 19 / 50) :
    0 < baseCredit δ A D := by
  have hv : 1 / 20 ≤ baseDifference A D := by unfold baseDifference; linarith
  have hm : 9 / 5 ≤ 2 - δ := by linarith only [hδ.2]
  have hp := mul_le_mul_of_nonneg_right hm (show 0 ≤ baseDifference A D by linarith)
  unfold baseCredit
  nlinarith only [hp, hv, hD]

private theorem deleted_price_eq (δ h A D L s : ℝ) :
    let b := 1 - A - D - L
    let U := A + b
    let v := A - b
    let T := -δ * L
    δ * (U - 2 * h) - 2 * (1 - δ) * v ^ 2 + (2 * U - 1) * T -
      (1 - U) ^ 2 / 12 + (12 / 25) *
        (baseCredit δ A D + 23 * L / 12) ^ 2 + 4 * δ * b * s =
      supportScore δ h A D L + 4 * δ * b * (s - L) := by
  dsimp only
  unfold supportScore baseScore baseCredit baseDifference
  ring

private theorem exceptional_price_eq (δ h A D e Z : ℝ) :
    let U := 1 - D + e
    let v := baseDifference A D - e
    let T := δ * e
    δ * (U - 2 * h) - 2 * (1 - δ) * v ^ 2 + (2 * U - 1) * T -
      (1 - U) ^ 2 / 12 + (12 / 25) *
        (baseCredit δ A D - 23 * e / 12 + 2 * Z) ^ 2 - 4 * A * Z =
      rawExceptionalScore δ h A D e Z := by
  dsimp only
  unfold rawExceptionalScore baseCredit baseDifference
  ring

private theorem exceptional_square_pos {δ A D e Z : ℝ}
    (hδ : δ ∈ Icc (18 / 109 : ℝ) (1 / 5)) (hA : 7 / 20 ≤ A)
    (_hAD : A ≤ D) (hD : D ≤ 19 / 50) (he : 0 ≤ e) (heE : e ≤ D - A)
    (hZ : 0 ≤ Z) : 0 < baseCredit δ A D - 23 * e / 12 + 2 * Z := by
  have hv : 1 / 20 ≤ baseDifference A D - e := by unfold baseDifference; linarith
  have hm : 9 / 5 ≤ 2 - δ := by linarith only [hδ.2]
  have he3 : e ≤ 3 / 100 := by linarith
  have hde : δ * e ≤ (1 / 5) * (3 / 100) :=
    (mul_le_mul_of_nonneg_right hδ.2 he).trans
      (mul_le_mul_of_nonneg_left he3 (by norm_num))
  have hp := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ baseDifference A D - e by linarith)
  have hid : baseCredit δ A D - 23 * e / 12 =
      (2 - δ) * (baseDifference A D - e) - δ * e - (D - e) / 12 := by
    unfold baseCredit
    ring
  rw [hid]
  nlinarith only [hp, hv, hde, hD, he, hZ]

end Erdos1017.EmptySatE2

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

private theorem no_neutral_saturated_peak_e2 (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioc (0 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hm : m = -LowerE2Scalar.multiplier q) (hell : -m < 1)
    (hgap : benchmark d < c)
    (hgamma : LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (horder : S.originalAtomMass p ≤ S.originalAtomMass r)
    (hcA : c ≤ (S.originalAtomMass r) ^ 2) : False := by
  have hqfull : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨hq.1, by linarith only [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hqfull
  have hc : Benchmark.twoHeadValue ((q + 2) / 3) < c := hvalue ▸ hgap
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let δ := 1 + m
  let γ := 2 * (c - m * d) + m
  let D := (1 - m - 4 * (c - m * d)) / δ
  let L := s + u - D
  let E := D - A
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hell]
  have hδq : δ = EmptySatE2.delta q := by simp only [δ, hm, EmptySatE2.delta]; ring
  have hratio : δ * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ hδ.ne'
  have hDγ : δ * (1 - D) = 2 * γ := by dsimp only [δ, γ] at *; nlinarith only [hratio]
  have hmass : A + b + s + u = 1 := S.universalPartner_regions_mass r p hpair.1
  have hL : L = 1 - A - b - D := by dsimp only [L]; linarith only [hmass]
  have hb : b = 1 - A - D - L := by linarith only [hL]
  have hA0 : 0 ≤ A := measureReal_nonneg
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hs0 : 0 ≤ s := measureReal_nonneg
  have hu0 : 0 ≤ u := measureReal_nonneg
  have hmissing : 1 - 2 * d = LowerE2Scalar.missingMass q := by rw [hdq]; ring
  have hbudget := S.empty_sat_deleted_partner_support r p hpair hW hd hgap hN
  change δ * (A + b - 2 * (1 - 2 * d)) + 2 * m * (A - b) ^ 2 +
    (2 * (A + b) - 1) * (δ * (A + b) - 2 * γ) - (1 - (A + b)) ^ 2 / 12 +
      (12 / 25) * max ((1 - m) * (A - b) - (δ * (A + b) - 2 * γ) -
        (1 - (A + b)) / 12) 0 ^ 2 + 4 * δ * b * s ≤ 0 at hbudget
  have hT : δ * (A + b) - 2 * γ = -δ * L := by
    rw [hL]
    nlinarith only [hDγ]
  by_cases hL0 : L ≤ 0
  · have hsquare := S.two_originalAtomMass_sq_le_missing_density r p hpair.1
    rw [hW.density_eq] at hsquare
    have hcircle : (A + b) ^ 2 + (A - b) ^ 2 ≤ 2 * LowerE2Scalar.missingMass q := by
      change A ^ 2 + b ^ 2 ≤ 1 - 2 * d at hsquare
      nlinarith only [hsquare, hmissing]
    have hsum : A + b < 1 := by
      have hh : LowerE2Scalar.missingMass q < 1 / 2 := by linarith only [hd.1, hmissing]
      nlinarith only [hcircle, sq_nonneg (A - b), hA0, hb0, hh]
    have hcorr : δ * (A + b) - 2 * γ =
        (1 - LowerE2Scalar.multiplier q) * (A + b - TwoUniversalE2Scalar.width q c) := by
      dsimp only [δ, γ]
      rw [hm]
      unfold TwoUniversalE2Scalar.width
      rw [← hmissing]
      have hδ' : 1 - LowerE2Scalar.multiplier q ≠ 0 := by
        simpa only [δ, hm, sub_eq_add_neg] using hδ.ne'
      field_simp [hδ']
      ring
    have hw : TwoUniversalE2Scalar.width q c ≤ A + b := by
      have hδ' : 0 < 1 - LowerE2Scalar.multiplier q := by
        simpa only [δ, hm, sub_eq_add_neg] using hδ
      have ht0 : 0 ≤ δ * (A + b) - 2 * γ := by rw [hT]; nlinarith only [hδ, hL0]
      rw [hcorr] at ht0
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hδ').mp ht0)
    have hpos : 0 < TwoUniversalE2Scalar.supportPolynomial q (A + b) (A - b)
        (δ * (A + b) - 2 * γ) := by
      by_cases hq5 : q ≤ 1 / 5
      · exact TwoUniversalE2Scalar.supportPolynomial_pos_of_twoHeadValue_lt
          ⟨hq.1, hq5⟩ hc hw hsum (sub_nonneg.mpr horder) hcircle hcorr
      · exact TwoUniversalE2Scalar.supportPolynomial_pos_of_twoHeadValue_lt_upper
          ⟨by linarith only [hq5], hq.2⟩ hc hw hsum
          (sub_nonneg.mpr horder) hcircle hcorr
    have hdebit : 0 ≤ 4 * δ * b * s := by positivity
    unfold TwoUniversalE2Scalar.supportPolynomial at hpos
    rw [hm, hmissing] at hbudget
    have heq : 1 - -LowerE2Scalar.multiplier q = 1 + LowerE2Scalar.multiplier q := by ring
    rw [heq] at hbudget
    have hδ' : δ = 1 - LowerE2Scalar.multiplier q := by
      dsimp only [δ]; rw [hm]; ring
    rw [hδ'] at hbudget hdebit hpos
    nlinarith only [hpos, hbudget, hdebit]
  have hLpos : 0 < L := lt_of_not_ge hL0
  have hcap := S.universalPartnerHole_deficit_cap r p hpair hW hd hgap hN
  have hint : 0 ≤ ∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ :=
    integral_nonneg (fun x => (S.universalRootDeficit_mem_Icc r x).1)
  have hLs : L ≤ s := by
    change (∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ) ≤
      1 - m - 4 * (c - m * d) - δ * u at hcap
    have hdu : u ≤ D := by nlinarith only [hcap, hint, hratio, hδ]
    dsimp only [L]
    linarith only [hdu]
  have hholes : 0 < μ (S.universalPartnerHoleRegion r p) :=
    ENNReal.toReal_pos_iff.mp (show 0 < s by linarith only [hLpos, hLs]) |>.1
  have hAD : A ≤ D := S.universal_atom_mass_le_saturated_deficit_ratio
    r p hpair hW hd hgap hell hN hholes
  have hR := LowerE2Scalar.denominator_pos hq.1.le
  have href : δ * (1 - 9 * q / (2 * LowerE2Scalar.denominator q)) =
      2 * LowerE2Scalar.gapFloor q := by
    rw [show δ = 1 - LowerE2Scalar.multiplier q by dsimp only [δ]; rw [hm]; ring]
    unfold LowerE2Scalar.multiplier LowerE2Scalar.gapFloor
    field_simp [hR.ne', show 2 + q ≠ 0 by linarith only [hq.1]]
    unfold LowerE2Scalar.denominator
    ring
  have hDref : D < 9 * q / (2 * LowerE2Scalar.denominator q) := by
    have hg : LowerE2Scalar.gapFloor q < γ := hgamma
    nlinarith only [hDγ, href, hg, hδ]
  by_cases hqsmall : q ≤ 9 / 50
  · have href0 : 0 ≤ 9 * q / (2 * LowerE2Scalar.denominator q) :=
      div_nonneg (by linarith only [hq.1]) (by positivity)
    have hsq := EmptySatE2.contact_value_gt_reference_sq ⟨hq.1.le, hqsmall⟩
    have hAr : A < 9 * q / (2 * LowerE2Scalar.denominator q) := hAD.trans_lt hDref
    nlinarith only [hA0, href0, hAr, hsq, hcA, hc]
  have hqbox : q ∈ Icc (9 / 50 : ℝ) (213 / 1000) := ⟨by linarith only [hqsmall], hq.2⟩
  obtain ⟨hA, hD, hδbox⟩ := EmptySatE2.contact_enclosure hqbox hA0 hc hcA hDref
  have hA' : 7 / 20 ≤ A := hA.le
  have hD' : D ≤ 19 / 50 := hD.le
  have hδbox' : δ ∈ Icc (18 / 109 : ℝ) (1 / 5) := hδq ▸ hδbox
  have hbase := EmptySatE2.baseCredit_pos hδbox' hA' hAD hD'
  have harg : (1 - m) * (A - b) - (δ * (A + b) - 2 * γ) - (1 - (A + b)) / 12 =
      EmptySatE2.baseCredit δ A D + 23 * L / 12 := by
    rw [hT, hb]
    dsimp only [δ]
    unfold EmptySatE2.baseCredit EmptySatE2.baseDifference
    ring
  rw [harg, max_eq_left (by linarith only [hbase, hLpos]), hT] at hbudget
  have hnorm := EmptySatE2.deleted_price_eq δ (1 - 2 * d) A D L s
  rw [← hb] at hnorm
  have hmδ : m = δ - 1 := by dsimp only [δ]; ring
  have hprice : EmptySatE2.supportScore δ (1 - 2 * d) A D L +
      4 * δ * b * (s - L) ≤ 0 := by
    rw [hmδ] at hbudget
    nlinarith only [hbudget, hnorm]
  have hE0 : 0 ≤ E := sub_nonneg.mpr hAD
  by_cases hLE : L ≤ E
  · have hpos := EmptySatE2.supportScore_pos_of_le_excess
      hqbox hA' hAD hD' hLpos.le hLE
    rw [← hδq, ← hmissing] at hpos
    have hdebit : 0 ≤ 4 * δ * b * (s - L) := by positivity
    linarith only [hprice, hpos, hdebit]
  have hEL : E < L := lt_of_not_ge hLE
  by_cases hsmall : ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x < L
  · obtain ⟨_, hstrong, hsquare⟩ :=
      S.empty_sat_small_parts_integrated_bounds r p hpair hW hd hgap hell hN hholes
        hLpos hEL hsmall
    change E * L + L ^ 2 ≤ E * s at hstrong
    change L ^ 2 ≤ E * D at hsquare
    have hpos := EmptySatE2.integratedScore_pos hqbox hA' hAD hD' hEL hsquare
    rw [← hδq, ← hmissing] at hpos
    have hmul := mul_le_mul_of_nonneg_left hprice hE0
    have hstrong' := mul_le_mul_of_nonneg_left hstrong
      (show 0 ≤ 4 * δ * b by positivity)
    unfold EmptySatE2.integratedScore at hpos
    rw [← hb] at hpos
    dsimp only [E] at hmul hstrong'
    nlinarith only [hmul, hstrong', hpos]
  obtain ⟨i, di, hir, hip, hwhole, haL, haE, hdi, _, hdef, hkzero, hZcap⟩ :=
    S.empty_sat_exceptional_atom r p hpair hW hd hgap hell hN hholes hEL hsmall
  have hprivate := S.empty_sat_exceptional_private_row
    r p i hpair hir hW hd hgap hell hN hwhole hkzero
  have hex := S.empty_sat_exceptional_support
    r p i hpair hir hip hW hd hgap hell hN hwhole di hdef hprivate
  let a := S.originalAtomMass i
  let e := a - L
  let Z := a * di
  have ha0 : 0 ≤ a := measureReal_nonneg
  have he0 : 0 ≤ e := sub_nonneg.mpr haL
  have heE : e ≤ D - A := by change a ≤ L + E at haE; dsimp only [e, E]; linarith
  have hZ0 : 0 ≤ Z := mul_nonneg ha0 hdi
  have hargpos := EmptySatE2.exceptional_square_pos hδbox' hA' hAD hD' he0 heE hZ0
  have hUex : A + a + b = 1 - D + e := by dsimp only [e]; linarith only [hb]
  have hvex : A - a - b = EmptySatE2.baseDifference A D - e := by
    dsimp only [e]
    unfold EmptySatE2.baseDifference
    linarith only [hb]
  have hTex : δ * (A + a + b) - 2 * γ = δ * e := by
    rw [hUex]
    nlinarith only [hDγ]
  change δ * (A + a + b - 2 * (1 - 2 * d)) + 2 * m * (A - a - b) ^ 2 +
    (2 * (A + a + b) - 1) * (δ * (A + a + b) - 2 * γ) -
      (1 - (A + a + b)) ^ 2 / 12 + (12 / 25) *
        max ((1 - m) * (A - a - b) - (δ * (A + a + b) - 2 * γ) -
          (1 - (A + a + b)) / 12 + 2 * Z) 0 ^ 2 - 4 * A * Z ≤ 0 at hex
  rw [hTex, hUex, hvex, hmδ] at hex
  have hargex : (1 - (δ - 1)) * (EmptySatE2.baseDifference A D - e) - δ * e -
      (1 - (1 - D + e)) / 12 + 2 * Z =
        EmptySatE2.baseCredit δ A D - 23 * e / 12 + 2 * Z := by
    unfold EmptySatE2.baseCredit
    ring
  rw [hargex, max_eq_left hargpos.le] at hex
  have hnormex := EmptySatE2.exceptional_price_eq δ (1 - 2 * d) A D e Z
  dsimp only at hnormex
  have hnonpos : EmptySatE2.rawExceptionalScore δ (1 - 2 * d) A D e Z ≤ 0 := by
    nlinarith only [hex, hnormex]
  have hZcap' : Z ≤ EmptySatE2.delta q * (D - A + e) / 2 := by
    rw [← hδq]
    exact hZcap
  have hpos := EmptySatE2.rawExceptionalScore_pos hqbox hA' hAD hD' he0 heE hZcap'
  rw [← hδq, ← hmissing] at hpos
  exact (not_lt_of_ge hnonpos) hpos

/-- An actual singleton reverse recovery with null entire source and a
saturated recovered head is impossible at the stated genuine E2 contact.
Universality, the original peak, every restriction and all scalar guards
are derived in the same original model. No body-energy premise is needed. -/
theorem ReverseRecovery.no_e2_saturated_empty_source
    {S : SelectedHighLowStructure W m} (R : S.ReverseRecovery)
    (r p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioc (0 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) : False := by
  have hqfull : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨hq.1, by linarith only [hq.2]⟩
  have hd := hdq ▸ LowerE2Scalar.contact_density_mem hqfull
  obtain ⟨hm, hell, hgamma⟩ :=
    hW.e2_general_contact_parameters hqfull hdq hvalue hderiv hgap hglobal
  have hpeak := R.empty_source_is_original_peak r hr hW hd hgap hnull
  exact no_neutral_saturated_peak_e2 S r p hpair hW hq hdq hvalue hm hell.2 hgap hgamma
    (R.empty_source_head_neutral r hr hW hd hgap hnull)
    (hpeak.2 p (Ne.symm hpair.1)).le
    (R.empty_source_objective_le_sq r hr hW hd hgap hnull)

end Erdos1017.CappedModel.SelectedHighLowStructure
