module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalPriceFinal
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalBounds
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalGoodError
public import Erdos1017.Exclusions.E2.Upper.UpperE2UniversalPricePrerequisites

/-!
# Price calibration of the universal upper `E₂` primal

The contact, recovery and original physical primal pay the deficit, zero-price
and error coefficients on one shared hole inventory
(`universal_upperE2_price_calibration`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The actual contact, recovery and original physical primal pay the
deficit, zero-price and error coefficients on one shared hole inventory. -/
theorem UniversalPhysicalPrimal.universal_upperE2_price_calibration
    (S : SelectedHighLowStructure W m) (R : S.ReverseRecovery) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c q : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {p}) (hsource : 0 < μ (S.reverseCompulsorySource {p}))
    (huniv : ∀ᵐ v ∂μ.prod μ, S.ρ v.1 = r.val →
      adjacencyKernel W v.1 v.2 = if S.ρ v.2 = r.val then 0 else 1)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val}) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let ell := -m
    let gamma := 2 * (c - m * d) + m
    let u := μ.real (S.universalPartnerCommonRegion r p)
    let capacity := min (1 - 3 * A + b) ((1 - u - 2 * ell * A - 3 * gamma) / ell)
    let z := S.universalSharedHoleRadius r p capacity
    let theta := 3 * gamma / A - (1 - ell)
    let DH := ∫ h in S.universalPartnerHoleRegion r p, S.universalRootDeficit r h ∂μ
    let chi := if theta < 1 / 2 then
      DH * (1 - 2 * theta) / ((A - z) * (1 - theta) - DH) else 0
    let kappa := μ.real (S.universalPartnerHoleRegion r p) -
      μ.real (S.reverseCompulsorySource {p})
    let Ecap := kappa * max (ell - theta) 0 *
      μ.real (S.universalGoodCommonRegion r p d c) / u
    DH < theta * (A - z) ∧ 0 ≤ chi ∧ chi < 1 / 2 ∧
      1 / 200 < gamma - max (1 - 2 * theta) 0 * capacity ∧
      0 ≤ Ecap ∧ Ecap < 3 * gamma / 5 := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let ell := -m
  let gamma := 2 * (c - m * d) + m
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let capacity := min (1 - 3 * A + b) ((1 - u - 2 * ell * A - 3 * gamma) / ell)
  let z := S.universalSharedHoleRadius r p capacity
  let theta := 3 * gamma / A - (1 - ell)
  let DH := ∫ h in S.universalPartnerHoleRegion r p, S.universalRootDeficit r h ∂μ
  let kappa := μ.real (S.universalPartnerHoleRegion r p) -
    μ.real (S.reverseCompulsorySource {p})
  let Ecap := kappa * max (ell - theta) 0 *
    μ.real (S.universalGoodCommonRegion r p d c) / u
  obtain ⟨hA, hb, hmargin, hcut, hu, hBpos, _, _⟩ :=
    P.universal_upperE2_quantitative_bounds R r p hpair hW hq hdq hvalue hderiv
      hgap hglobal hr hsource huniv hpeak hpositive
  have hAbox : A ∈ Icc (1 / 3 : ℝ) (93 / 250) := ⟨hA.le, hcut.le⟩
  have hmissing := UpperE2Parameter.missingMass_mem hq
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    constructor <;> linarith only [hmissing.1, hmissing.2]
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) :=
    ⟨by linarith only [hq.1], by linarith only [hq.2]⟩
  obtain ⟨hm, hell, hfloor⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hellbox : ell ∈ Icc (4 / 5 : ℝ) (9 / 11) := by
    have h := UpperE2Parameter.multiplier_mem hq
    rw [← neg_eq_iff_eq_neg.mpr hm] at h
    exact ⟨h.1.le, h.2⟩
  have hell0 : 0 < ell := by linarith only [hellbox.1]
  have hgamma : UpperE2UniversalScalar.gammaFloor ell ≤ gamma := by
    have h := UpperE2Parameter.gapFloor_ge_correlated hq
    rw [← neg_eq_iff_eq_neg.mpr hm] at h
    dsimp only [UpperE2UniversalScalar.gammaFloor, gamma, ell]
    linarith only [h, hfloor]
  have hgamma0 : (7 / 122 : ℝ) ≤ gamma :=
    (UpperE2Parameter.gapFloor_ge hq).trans hfloor.le
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  have hAhalf : S.originalAtomMass r ≤ 1 / 2 := by linarith only [hcut]
  have hcap := P.ae_negative_shared_hole_cap S r p hpair hW hd hgap hN hA
    hAhalf hell hmargin hu
  change ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
    S.universalOwnMass x + S.universalGoodMissingMass r p d c x ≤
      min (1 - 3 * A + b) ((1 - u + 2 * m * A - 3 * gamma) / ell) at hcap
  have hcapacityEq : min (1 - 3 * A + b)
      ((1 - u + 2 * m * A - 3 * gamma) / ell) = capacity := by
    dsimp only [capacity]
    apply congrArg (min (1 - 3 * A + b))
    apply congrArg (fun t : ℝ => t / ell)
    dsimp only [ell]
    ring
  rw [hcapacityEq] at hcap
  have hcapacity : 0 ≤ capacity :=
    S.universalSharedHoleCapacity_nonneg r p d c capacity hBpos hcap
  have hzcap : z ≤ capacity := S.universalSharedHoleRadius_le_capacity r p capacity
  have hzbad : z ≤ 1 - 3 * A + b := hzcap.trans (min_le_left _ _)
  have hzrow : capacity ≤ (1 - u - 2 * ell * A - 3 * gamma) / ell := min_le_right _ _
  have hk : 0 < A - z := by
    change b ≤ 1 - 2 * A at hb
    nlinarith only [hzbad, hb, hA]
  have hmass := S.universalPartner_regions_mass r p hpair.1
  have hpack := P.hole_add_shared_radius_sq_le_original_missing S r p hpair hW
    hd hgap hN hA hAhalf hell hmargin capacity hcapacity
  have hqh := S.universalHoleSquareMoment_nonneg r p
  have hpacking : z ^ 2 ≤ 3509 / 14884 - A ^ 2 - b ^ 2 -
      2 * b * (1 - A - b - u) := by
    have hmissingEq : 1 - 2 * d = LowerE2Scalar.missingMass q := by rw [hdq]; ring
    change A + b + μ.real (S.universalPartnerHoleRegion r p) + u = 1 at hmass
    change S.universalHoleSquareMoment r p + z ^ 2 ≤
      1 - 2 * d - A ^ 2 - b ^ 2 -
        2 * b * μ.real (S.universalPartnerHoleRegion r p) at hpack
    rw [hmissingEq] at hpack
    have hmassMul := congrArg (fun t : ℝ => 2 * b * t) hmass
    nlinarith only [hpack, hqh, hmissing.2, hmassMul]
  have hresources := S.universal_partner_common_good_resources r p hpair hW hd hgap hN
  have hresource : ell + gamma - (1 + ell) * A ≤ 2 * ell * u := by
    dsimp only [ell, gamma, A, u]
    nlinarith only [hresources.1]
  have hgood : (ell + theta) * μ.real (S.universalGoodCommonRegion r p d c) ≤
      2 * ell * u - (ell + gamma - (1 + ell) * A) := by
    dsimp only [ell, theta, gamma, A, u]
    nlinarith only [hresources.2]
  have hgapnum := UpperE2UniversalScalar.deficit_cap_lt_threshold hAbox hellbox
    hgamma0 hb hu.le hzbad hresource hpacking
  have hshared := S.empty_sat_corner_shared_budget r p hpair hW hd hgap hN
  have hscore : ∀ᵐ x ∂μ.restrict (S.universalPartnerCommonRegion r p),
      0 ≤ -(S.rootChargeRow r x + S.rootChargeRow p x) := by
    filter_upwards [ae_restrict_of_ae
      (S.ae_universal_saturated_common_score_nonpos r p hpair hW hd hgap hN),
      ae_restrict_mem (S.measurableSet_universalPartnerCommonRegion r p)]
      with x hx hxU
    have hnotr : S.ρ x ≠ r.val := fun h => hxU (Or.inl (Or.inl h))
    exact neg_nonneg.mpr (hx hnotr (S.common_region_mem_rootNeighborhood r p hxU))
  have hDHcap : DH ≤ (1 - ell) * (1 - u) - 2 * gamma := by
    have hnonneg := integral_nonneg_of_ae hscore
    change DH + _ = _ at hshared
    dsimp only [ell, gamma, u] at *
    linarith only [hshared, hnonneg]
  have hDHgap : DH < theta * (A - z) := hDHcap.trans_lt hgapnum
  have hDH0 : 0 ≤ DH :=
    integral_nonneg (fun x => (S.universalRootDeficit_mem_Icc r x).1)
  have htheta0 : 0 ≤ theta := by
    have hA0 : 0 < A := by linarith only [hA]
    have htheta : A * theta = 3 * gamma - A * (1 - ell) := by
      dsimp only [theta]
      field_simp [hA0.ne']
    have hprod := mul_nonneg hA0.le (show 0 ≤ 1 - ell by linarith only [hellbox.2])
    have hmargin' : 2 * A * (1 - ell) < 3 * gamma := by
      dsimp only [A, ell, gamma]
      nlinarith only [hmargin]
    nlinarith only [htheta, hmargin', hprod, hA0]
  have hchi : 0 ≤ (if theta < 1 / 2 then
      DH * (1 - 2 * theta) / ((A - z) * (1 - theta) - DH) else 0) ∧
      (if theta < 1 / 2 then
        DH * (1 - 2 * theta) / ((A - z) * (1 - theta) - DH) else 0) < 1 / 2 := by
    split_ifs with htheta
    · exact (UpperE2UniversalScalar.deficit_ratio_lt_half ⟨htheta0, htheta⟩ hk hDH0 hDHgap).2
    · constructor <;> norm_num
  have hzero := UpperE2UniversalScalar.zero_price_numerator_margin hAbox hellbox hgamma
    hcapacity hresource hzrow
  have hsourceMargin := R.universal_partner_source_mass_margin r p hpair hW hd hgap
    hell.2 hr hN
  have herror := UpperE2UniversalScalar.error_cap_lt_three_fifths hAbox hellbox hgamma
    hsourceMargin.1 hsourceMargin.2 hresource hgood
  have hRPpos : 0 < ell + gamma - (1 + ell) * A := by
    have h := (UpperE2UniversalScalar.error_resources_pos hAbox hellbox).1
    dsimp only [UpperE2UniversalScalar.errorRp] at h
    linarith only [h, hgamma]
  have hu0 : 0 < u := by
    have h : 0 < 2 * ell * u := hRPpos.trans_le hresource
    exact (mul_pos_iff_of_pos_left (show 0 < 2 * ell by positivity)).mp h
  have hEcap0 : 0 ≤ Ecap :=
    div_nonneg (mul_nonneg (mul_nonneg hsourceMargin.1 (le_max_right _ _))
      measureReal_nonneg) hu0.le
  exact ⟨hDHgap, hchi.1, hchi.2, hzero, hEcap0, herror⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
