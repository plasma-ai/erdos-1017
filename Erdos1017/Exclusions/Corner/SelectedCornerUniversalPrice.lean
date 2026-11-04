module

public import Erdos1017.Exclusions.Corner.SelectedCornerUniversalGeometry
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalCopyCap
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerBadRegion
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalGoodError
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalPriceFinal
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalPriceJoin
public import Erdos1017.Exclusions.E2.Upper.UpperE2UniversalTrace
public import Erdos1017.Exclusions.E2.Upper.UpperE2UniversalPricePrerequisites
public import Erdos1017.Exclusions.Corner.UniversalCornerScalar

/-!
# Exclusion of the universal one-center corner recovery

A universal peak with singleton recovery cannot occur at the `W`/`E₂` corner;
every price stock is derived from its primal.
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

/-- The same common mass pays the signed error before either corner license. -/
private theorem corner_error_le_coarse {A ell gamma u kappa g : ℝ}
    (hA : 0 < A)
    (hRP : 0 < ell + gamma - (1 + ell) * A)
    (hRR : 0 < (2 * ell - 1) * A + 3 * gamma)
    (hu : 0 < u) (hkappa : 0 ≤ kappa) (hg : 0 ≤ g)
    (hmargin : u + kappa ≤ 1 - 2 * A)
    (hgood : (ell + (3 * gamma / A - (1 - ell))) * g ≤
      2 * ell * u - (ell + gamma - (1 + ell) * A)) :
    let theta := 3 * gamma / A - (1 - ell)
    let RP := ell + gamma - (1 + ell) * A
    let RR := (2 * ell - 1) * A + 3 * gamma
    let D := 2 * ell * (1 - 2 * A) - RP
    kappa * max (ell - theta) 0 * g / u ≤
      max (A - 3 * gamma) 0 * D ^ 2 / (4 * RP * RR) := by
  let theta := 3 * gamma / A - (1 - ell)
  let RP := ell + gamma - (1 + ell) * A
  let RR := (2 * ell - 1) * A + 3 * gamma
  let T := A - 3 * gamma
  let r0 := 1 - 2 * A
  have hucap : u ≤ r0 := by dsimp only [r0]; linarith only [hmargin, hkappa]
  by_cases htau : 0 < ell - theta
  · have hTidentity : A * (ell - theta) = T := by
      dsimp only [theta, T]
      field_simp [hA.ne']
      ring
    have hT : 0 < T := hTidentity ▸ mul_pos hA htau
    have hRidentity : A * (ell + theta) = RR := by
      dsimp only [theta, RR]
      field_simp [hA.ne']
      ring
    have hgoodscaled := mul_le_mul_of_nonneg_left hgood hA.le
    have hRscaled := congrArg (fun x : ℝ => x * g) hRidentity
    have hgood' : RR * g ≤ A * (2 * ell * u - RP) := by
      dsimp only [theta, RP] at *
      nlinarith only [hgoodscaled, hRscaled]
    have hw : 0 ≤ 2 * ell * u - RP := by
      have hnonnegative : 0 ≤ A * (2 * ell * u - RP) :=
        (mul_nonneg hRR.le hg).trans hgood'
      exact (mul_nonneg_iff_of_pos_left hA).mp hnonnegative
    have hscaled := mul_le_mul_of_nonneg_left hgood' (mul_nonneg hkappa htau.le)
    have hTscaled := congrArg (fun x : ℝ => kappa * x * (2 * ell * u - RP)) hTidentity
    have hkpaid := mul_nonneg
      (show 0 ≤ r0 - u - kappa by dsimp only [r0]; linarith only [hmargin])
      (mul_nonneg hT.le hw)
    have hrow : kappa * (ell - theta) * g * RR ≤
        T * (r0 - u) * (2 * ell * u - RP) := by
      nlinarith only [hscaled, hTscaled, hkpaid]
    have hratio : kappa * (ell - theta) * g / u ≤
        (T / RR) * ((r0 - u) * (2 * ell - RP / u)) := by
      have heq : (T / RR) * ((r0 - u) * (2 * ell - RP / u)) =
          T * (r0 - u) * (2 * ell * u - RP) / (RR * u) := by
        field_simp [hRR.ne', hu.ne']
      rw [heq]
      apply (div_le_div_iff₀ hu (mul_pos hRR hu)).mpr
      have h := mul_le_mul_of_nonneg_right hrow hu.le
      nlinarith only [h]
    have hbound := mul_le_mul_of_nonneg_left
      (Erdos1017.UpperE2UniversalScalar.common_error_resource_bound (ell := ell) hu hRP hucap)
      (div_nonneg hT.le hRR.le)
    have heq : (T / RR) * ((2 * ell * r0 - RP) ^ 2 / (4 * RP)) =
        T * (2 * ell * r0 - RP) ^ 2 / (4 * RP * RR) := by
      field_simp [hRR.ne', hRP.ne']
    change kappa * max (ell - theta) 0 * g / u ≤
      max T 0 * (2 * ell * r0 - RP) ^ 2 / (4 * RP * RR)
    rw [max_eq_left htau.le, max_eq_left hT.le]
    change (T / RR) * ((r0 - u) * (2 * ell - RP / u)) ≤
      (T / RR) * ((2 * ell * r0 - RP) ^ 2 / (4 * RP)) at hbound
    rw [heq] at hbound
    exact hratio.trans hbound
  · change kappa * max (ell - theta) 0 * g / u ≤ _
    rw [max_eq_right (le_of_not_gt htau), mul_zero, zero_mul, zero_div]
    positivity

private theorem UniversalPhysicalPrimal.corner_hole_licenses
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hsource : 0 < μ (S.reverseCompulsorySource {p})) :
    0 < μ.real (S.universalPartnerHoleRegion r p) ∧
      S.originalAtomMass p ≤ 1 - 2 * S.originalAtomMass r ∧
      3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m) < 1 := by
  have hsubset := S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell.2
  have hHpos : 0 < μ (S.universalPartnerHoleRegion r p) :=
    lt_of_lt_of_le hsource (measure_mono_ae hsubset)
  obtain ⟨x, _, hlow, hupp, hthreshold, hstrict⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hHpos.ne'
      ((S.ae_universalPartnerHole_degree_ge_twice_mass r p hpair hW hd hgap hell.2 hN).and
        ((S.ae_universalPartnerHole_degree_le_one_sub_partner_mass r p hW hd hgap).and
          ((P.ae_universal_upperE2_hole_star_threshold S r p hpair hW hd hgap
            hN hA hAhalf hell hmargin).and
            (S.ae_rootChargeRow_lt_one_on_universalPartnerHole r p hpair hW hd hgap hell.2))))
  refine ⟨ENNReal.toReal_pos hHpos.ne' (measure_ne_top μ _), ?_, hthreshold.trans_lt hstrict⟩
  change 2 * S.originalAtomMass r ≤ ∫ z, adjacencyKernel W x z ∂μ at hlow
  linarith only [hlow, hupp]

private theorem corner_gamma_ratio_floor {ell h c gamma : ℝ}
    (hell : ell ∈ Icc (363 / 589 : ℝ) (9 / 11))
    (hh : h < 23243417 / 10 ^ 8)
    (hc : (138261458236451 : ℝ) / 1116960975000000 < c)
    (hgamma : gamma = 2 * c - ell * h) :
    (2820692027533121 : ℝ) / 40210595100000000 < gamma / ell := by
  have hell0 : 0 < ell := by linarith only [hell.1]
  apply (lt_div_iff₀ hell0).mpr
  rw [hgamma]
  have hscale := mul_le_mul_of_nonneg_left hell.2
    (show 0 ≤ (22 / 9 : ℝ) * (138261458236451 / 1116960975000000) by norm_num)
  have hheight := mul_lt_mul_of_pos_left hh hell0
  nlinarith only [hc, hheight, hscale]

private theorem corner_partner_row_pos {A ell gamma : ℝ}
    (hA : A < 3 / 7) (hell : 1 / 2 < ell)
    (hmargin : 2 * A * (1 - ell) < 3 * gamma) :
    0 < ell + gamma - (1 + ell) * A := by
  have hfactor : 0 < 1 - 5 * A / 3 := by linarith only [hA]
  have hpaid := mul_pos (sub_pos.mpr hell) hfactor
  nlinarith only [hmargin, hpaid, hA]

private theorem corner_bad_row_gap {A ell gamma : ℝ}
    (hA : A ∈ Ioo (1 / 3 : ℝ) (369 / 1000))
    (hell : ell ∈ Icc (363 / 589 : ℝ) (9 / 11))
    (hmargin : 2 * A * (1 - ell) < 3 * gamma) :
    0 < ell + gamma - (1 + ell) * A -
      max (ell - (3 * gamma / A - (1 - ell))) 0 * (1 - 2 * A) := by
  have hA0 : 0 < A := lt_trans (by norm_num) hA.1
  have hAhi : A < 3 / 7 := by linarith only [hA.2]
  have hell0 : 1 / 2 < ell := by linarith only [hell.1]
  have hdelta : 0 < 1 - ell := by linarith only [hell.2]
  have hRP := corner_partner_row_pos hAhi hell0 hmargin
  by_cases hside : ell - (3 * gamma / A - (1 - ell)) ≤ 0
  · simpa only [max_eq_right hside, zero_mul, sub_zero] using hRP
  · rw [max_eq_left (le_of_not_ge hside)]
    have hfactor : 0 < 3 - 5 * A := by linarith only [hA.2]
    have hscaled := mul_lt_mul_of_pos_right hmargin hfactor
    have hpaid := mul_pos (mul_pos hA0 hdelta)
      (show 0 < 3 - 7 * A by linarith only [hAhi])
    have hpositive : 0 < gamma * (3 - 5 * A) - A * (1 - ell) * (1 - A) := by
      nlinarith only [hscaled, hpaid]
    have heq : A * (ell + gamma - (1 + ell) * A -
        (ell - (3 * gamma / A - (1 - ell))) * (1 - 2 * A)) =
        gamma * (3 - 5 * A) - A * (1 - ell) * (1 - A) := by
      field_simp
      ring
    exact (mul_pos_iff_of_pos_left hA0).mp (heq.symm ▸ hpositive)

private theorem corner_bad_region_pos (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : S.originalAtomMass r ∈ Ioo (1 / 3 : ℝ) (369 / 1000))
    (hell : -m ∈ Icc (363 / 589 : ℝ) (9 / 11))
    (hmargin : 2 * S.originalAtomMass r * (1 + m) < 3 * (2 * (c - m * d) + m))
    (hu : μ.real (S.universalPartnerCommonRegion r p) < 1 - 2 * S.originalAtomMass r) :
    0 < μ (S.universalUpperE2BadRegion r p d c) := by
  by_contra hn
  have hnull : μ (S.universalUpperE2BadRegion r p d c) = 0 :=
    le_antisymm (le_of_not_gt hn) zero_le
  let A := S.originalAtomMass r
  let ell := -m
  let gamma := 2 * (c - m * d) + m
  let theta := 3 * gamma / A - (1 + m)
  let RP := 2 * (c - m * d) - (1 - m) * A
  let U := S.universalPartnerCommonRegion r p
  let Good := S.universalGoodCommonRegion r p d c
  have hGood : μ.real Good = μ.real U := by
    apply measureReal_congr
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    exact propext ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩
  have hresource := (S.universal_partner_common_good_resources r p hpair hW hd hgap hN).2
  change (ell + theta) * μ.real Good ≤ 2 * ell * μ.real U - RP at hresource
  rw [hGood] at hresource
  have hrow : RP ≤ (ell - theta) * μ.real U := by linarith only [hresource]
  have hmax := mul_le_mul_of_nonneg_right (le_max_left (ell - theta) 0)
    (measureReal_nonneg (μ := μ) (s := U))
  have hcap := mul_le_mul_of_nonneg_left hu.le (le_max_right (ell - theta) 0)
  have hbound := (hrow.trans hmax).trans hcap
  have hmargin' : 2 * A * (1 - ell) < 3 * gamma := by
    simpa only [A, ell, gamma, sub_neg_eq_add] using hmargin
  have hstrict := corner_bad_row_gap (A := A) (ell := ell) (gamma := gamma) hA hell hmargin'
  have htheta : 3 * gamma / A - (1 - ell) = theta := by dsimp only [ell, theta]; ring
  rw [htheta] at hstrict
  have heq : ell + gamma - (1 + ell) * A = RP := by dsimp only [ell, gamma, RP]; ring
  rw [heq] at hstrict
  linarith only [hstrict, hbound]

private theorem UniversalPhysicalPrimal.corner_negative_region_pos
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : S.originalAtomMass r ∈ Ioo (1 / 3 : ℝ) (369 / 1000))
    (hell : -m ∈ Icc (363 / 589 : ℝ) (9 / 11))
    (hh : 1 - 2 * d < 23243417 / 10 ^ 8)
    (hc : (138261458236451 : ℝ) / 1116960975000000 < c)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) < 3 * (2 * (c - m * d) + m))
    (hu : μ.real (S.universalPartnerCommonRegion r p) < 1 - 2 * S.originalAtomMass r) :
    0 < μ (S.universalNegativeRegion r p) := by
  have hbad := corner_bad_region_pos S r p hpair hW hd hgap hN hA hell hmargin hu
  have hAhi : S.originalAtomMass r < 3 / 8 := by linarith only [hA.2]
  have hmul := mul_lt_mul_of_pos_left hh (show 0 < -m by linarith only [hell.1])
  have hfloor : 2 * (138261458236451 / 1116960975000000 : ℝ) -
      (-m) * (23243417 / 10 ^ 8) < 2 * (c - m * d) + m := by
    nlinarith only [hc, hmul]
  exact P.corner_negative_region_pos_of_bad_pos S r p hpair hW hd hgap hN hA.1 hAhi
    hell hfloor hmargin hbad

private theorem corner_body_cap_price_guard {A b gamma ell : ℝ}
    (hell : 0 < ell) (hA : (369 / 1000 : ℝ) ≤ A)
    (hb : b ≤ 1 - 2 * A)
    (hgamma : (2820692027533121 : ℝ) / 40210595100000000 < gamma / ell) :
    b * ell - gamma ≤ ell * (6 * A - 2) := by
  have hscaled := (lt_div_iff₀ hell).mp hgamma
  have hmargin : 3 - 8 * A < (2820692027533121 : ℝ) / 40210595100000000 := by
    linarith only [hA]
  have hm := mul_lt_mul_of_pos_right hmargin hell
  have hb' := mul_le_mul_of_nonneg_right hb hell.le
  nlinarith only [hscaled, hm, hb']

private theorem mass_lt_corner_cutoff_of_trace {A x h : ℝ}
    (hx : (2820692027533121 : ℝ) / 40210595100000000 < x)
    (hh : h < 23243417 / 10 ^ 8)
    (htrace : (A + x) ^ 2 ≤ 2 * (h - A ^ 2)) : A < 369 / 1000 := by
  by_contra hn
  have hA : (369 / 1000 : ℝ) ≤ A := le_of_not_gt hn
  have hA2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 369 / 1000) hA 2
  have hsum : (369 / 1000 : ℝ) + 2820692027533121 / 40210595100000000 ≤ A + x :=
    add_le_add hA hx.le
  have hsum2 := pow_le_pow_left₀ (by norm_num :
    (0 : ℝ) ≤ 369 / 1000 + 2820692027533121 / 40210595100000000) hsum 2
  norm_num at hA2 hsum2
  nlinarith only [htrace, hA2, hsum2, hh]

private theorem UniversalPhysicalPrimal.corner_mass_lt_cutoff
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Icc (363 / 589 : ℝ) (9 / 11))
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val})
    (hh : 1 - 2 * d < 23243417 / 10 ^ 8)
    (hc : (138261458236451 : ℝ) / 1116960975000000 < c)
    (hb : S.originalAtomMass p ≤ 1 - 2 * S.originalAtomMass r) :
    S.originalAtomMass r < 369 / 1000 := by
  have hratio := corner_gamma_ratio_floor hell hh hc
    (show 2 * (c - m * d) + m = 2 * c - (-m) * (1 - 2 * d) by ring)
  have hell' : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith only [hell.1, hell.2]
  by_contra hn
  have hprice := corner_body_cap_price_guard
    (show 0 < -m by linarith only [hell.1]) (le_of_not_gt hn) hb hratio
  have hcap := P.ae_universal_positive_body_le_multiplier S r p hpair hW hd hgap
    hN hA hAhalf hell' hmargin hprice
  have htrace := S.universal_positive_body_trace_of_cap r hW hd hgap hN hpositive
    hcap
  exact (not_lt_of_ge (le_of_not_gt hn)) (mass_lt_corner_cutoff_of_trace hratio hh htrace)

private theorem corner_error_cap_le_coarse
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : S.originalAtomMass r ∈ Ioo (1 / 3 : ℝ) (369 / 1000))
    (hell : -m ∈ Icc (363 / 589 : ℝ) (9 / 11))
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hstrict : μ.real (S.universalPartnerCommonRegion r p) +
      μ.real (S.universalExtraHoleRegion r p) < 1 - 2 * S.originalAtomMass r)
    (hBpos : 0 < μ (S.universalNegativeRegion r p)) :
    let A := S.originalAtomMass r
    let ell := -m
    let gamma := 2 * c - ell * (1 - 2 * d)
    let theta := 3 * gamma / A - (1 - ell)
    let RP := ell + gamma - (1 + ell) * A
    let RR := (2 * ell - 1) * A + 3 * gamma
    let D := 2 * ell * (1 - 2 * A) - RP
    μ.real (S.universalExtraHoleRegion r p) * max (ell - theta) 0 *
        μ.real (S.universalGoodCommonRegion r p d c) /
          μ.real (S.universalPartnerCommonRegion r p) ≤
      max (A - 3 * gamma) 0 * D ^ 2 / (4 * RP * RR) := by
  let A := S.originalAtomMass r
  let ell := -m
  let gamma := 2 * c - ell * (1 - 2 * d)
  have hApos : 0 < A := lt_trans (by norm_num) hA.1
  have hellhalf : 1 / 2 < ell := by linarith only [hell.1]
  have hdelta : 0 < 1 - ell := by linarith only [hell.2]
  have hgamma : 2 * (c - m * d) + m = gamma := by dsimp only [gamma, ell]; ring
  have hmargin' : 2 * A * (1 - ell) < 3 * gamma := by
    simpa only [A, ell, sub_neg_eq_add, ← hgamma] using hmargin
  have hgammapos : 0 < gamma := by
    have hpositive := mul_pos hApos hdelta
    nlinarith only [hpositive, hmargin']
  have hRP : 0 < ell + gamma - (1 + ell) * A :=
    corner_partner_row_pos (by linarith only [hA.2]) hellhalf hmargin'
  have hRR : 0 < (2 * ell - 1) * A + 3 * gamma := by
    have hpositive := mul_pos (show 0 < 2 * ell - 1 by linarith only [hellhalf]) hApos
    nlinarith only [hpositive, hgammapos]
  have hUmeasure : 0 < μ (S.universalPartnerCommonRegion r p) :=
    lt_of_lt_of_le hBpos (measure_mono (fun _ hx => hx.1))
  have hu : 0 < μ.real (S.universalPartnerCommonRegion r p) :=
    ENNReal.toReal_pos hUmeasure.ne' (measure_ne_top _ _)
  have hRPidentity : 2 * (c - m * d) - (1 - m) * S.originalAtomMass r =
      ell + gamma - (1 + ell) * A := by dsimp only [ell, gamma, A]; ring
  have htheta : 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m) =
      3 * gamma / A - (1 - ell) := by rw [hgamma]; dsimp only [A, ell]; ring
  have hgood := (S.universal_partner_common_good_resources r p hpair hW hd hgap hN).2
  rw [hRPidentity, htheta] at hgood
  exact corner_error_le_coarse hApos hRP hRR hu measureReal_nonneg measureReal_nonneg
    hstrict.le hgood

private theorem corner_pole_guards {A b z q : ℝ}
    (hA : 1 / 3 < A) (hbcap : b ≤ 1 - 2 * A) (hz : z ≤ 1 - 3 * A + b) :
    0 < A - z ∧ min (1 - 2 * A - b) (Real.sqrt q) < A - z := by
  have halpha := min_le_left (1 - 2 * A - b) (Real.sqrt q)
  constructor <;> linarith only [hA, hbcap, hz, halpha]

private theorem corner_deficit_coefficient_bound {theta k DH : ℝ}
    (hk : 0 < k) (hDH : 0 ≤ DH) (hDHk : DH < theta * k) :
    (if theta < 1 / 2 then DH * (1 - 2 * theta) / (k * (1 - theta) - DH) else 0) ∈
      Icc (0 : ℝ) (1 / 2) := by
  by_cases hhalf : theta < 1 / 2
  · rw [ite_eq_left hhalf]
    have hden : 0 < k * (1 - theta) - DH := by
      have hpaid := mul_pos hk (show 0 < 1 - 2 * theta by linarith only [hhalf])
      nlinarith only [hDHk, hpaid]
    have hbound : DH * (1 - 2 * theta) / (k * (1 - theta) - DH) ≤ theta := by
      apply (div_le_iff₀ hden).mpr
      have hpaid := mul_nonneg (sub_nonneg.mpr hDHk.le)
        (show 0 ≤ 1 - theta by linarith only [hhalf])
      nlinarith only [hpaid]
    exact ⟨div_nonneg (mul_nonneg hDH (by linarith only [hhalf])) hden.le,
      hbound.trans hhalf.le⟩
  · rw [ite_eq_right hhalf]
    norm_num

private theorem corner_nonpositive_copy_bound
    {A b ell gamma Rcap N n TB Zd chi Ecap : ℝ}
    (hell : 0 < ell) (hN : 0 ≤ N) (hZd : 0 ≤ Zd) (hchi : chi ≤ ell)
    (hcap : Rcap ≤ 1 - 3 * A + b)
    (hinventory : TB + Zd ≤ Rcap * N)
    (hcopy : ell * ((A - b) * N - TB + gamma * n) ≤ chi * Zd + ell * Ecap * n) :
    (gamma - Ecap) * n ≤ (1 - 4 * A + 2 * b) * N := by
  have hchiZd := mul_le_mul_of_nonneg_right hchi hZd
  have htotal := hinventory.trans (mul_le_mul_of_nonneg_right hcap hN)
  have hscaled := mul_le_mul_of_nonneg_left htotal hell.le
  have hbound : ell * ((gamma - Ecap) * n) ≤
      ell * ((1 - 4 * A + 2 * b) * N) := by
    nlinarith only [hcopy, hchiZd, hscaled]
  exact (mul_le_mul_iff_right₀ hell).mp hbound

private theorem UniversalPhysicalPrimal.corner_scalar_licenses
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : S.originalAtomMass r ∈ Ioo (1 / 3 : ℝ) (369 / 1000))
    (hell : -m ∈ Icc (363 / 589 : ℝ) (9 / 11))
    (hh : 1 - 2 * d < 23243417 / 10 ^ 8)
    (hc : (138261458236451 : ℝ) / 1116960975000000 < c)
    (hbcap : S.originalAtomMass p ≤ 1 - 2 * S.originalAtomMass r)
    (hu : μ.real (S.universalPartnerCommonRegion r p) ∈
      Ico (0 : ℝ) (1 - 2 * S.originalAtomMass r))
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hBpos : 0 < μ (S.universalNegativeRegion r p)) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let ell := -m
    let h := 1 - 2 * d
    let u := μ.real (S.universalPartnerCommonRegion r p)
    let gamma := 2 * c - ell * h
    let RP := ell + gamma - (1 + ell) * A
    let RR := (2 * ell - 1) * A + 3 * gamma
    let D := 2 * ell * (1 - 2 * A) - RP
    let Ecap := max (A - 3 * gamma) 0 * D ^ 2 / (4 * RP * RR)
    let theta := 3 * gamma / A - (1 - ell)
    let Rcap := min (1 - 3 * A + b) ((1 - u - 2 * ell * A - 3 * gamma) / ell)
    let z := S.universalSharedHoleRadius r p Rcap
    let q := S.universalHoleSquareMoment r p
    let DH := ∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ
    z ∈ Icc (0 : ℝ) Rcap ∧ z ≤ u ∧ 0 ≤ q ∧
      q + z ^ 2 ≤ h - A ^ 2 - b ^ 2 - 2 * b * (1 - A - b - u) ∧
      Ecap < 3 * gamma / 5 ∧ Ecap < 1 / 25 ∧
      1 / 200 < gamma - max (1 - 2 * theta) 0 * Rcap ∧ DH < theta * (A - z) := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let ell := -m
  let h := 1 - 2 * d
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let gamma := 2 * c - ell * h
  let Rcap := min (1 - 3 * A + b) ((1 - u - 2 * ell * A - 3 * gamma) / ell)
  let z := S.universalSharedHoleRadius r p Rcap
  let q := S.universalHoleSquareMoment r p
  let DH := ∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ
  have hAhalf : A ≤ 1 / 2 := by linarith only [hA.2]
  have hell' : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith only [hell.1, hell.2]
  have hgamma : 2 * (c - m * d) + m = gamma := by dsimp only [gamma, ell, h]; ring
  have hcap : ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalOwnMass x + S.universalGoodMissingMass r p d c x ≤ Rcap := by
    have hbound := P.ae_negative_shared_hole_cap S r p hpair hW hd hgap hN hA.1 hAhalf
      hell' hmargin hu.2
    rw [hgamma] at hbound
    convert hbound using 1
    simp only [Rcap, A, b, u, ell]
    ring_nf
  have hR : 0 ≤ Rcap := S.universalSharedHoleCapacity_nonneg r p d c Rcap hBpos hcap
  have hz : z ∈ Icc (0 : ℝ) Rcap :=
    ⟨S.universalSharedHoleRadius_nonneg r p Rcap hR,
      S.universalSharedHoleRadius_le_capacity r p Rcap⟩
  have hzu : z ≤ u := P.universalSharedHoleRadius_le_common_mass S r p hpair hW hd hgap
    hN hA.1 hAhalf hell' hmargin Rcap
  have hq : 0 ≤ q := S.universalHoleSquareMoment_nonneg r p
  have hmass := S.universalPartner_regions_mass r p hpair.1
  have hholes := P.hole_add_shared_radius_sq_le_original_missing S r p hpair hW hd hgap
    hN hA.1 hAhalf hell' hmargin Rcap hR
  have hholes' : q + z ^ 2 ≤ h - A ^ 2 - b ^ 2 - 2 * b * (1 - A - b - u) := by
    change q + z ^ 2 ≤ h - A ^ 2 - b ^ 2 -
      2 * b * μ.real (S.universalPartnerHoleRegion r p) at hholes
    have hH : μ.real (S.universalPartnerHoleRegion r p) = 1 - A - b - u := by
      dsimp only [A, b, u]
      linarith only [hmass]
    rw [hH] at hholes
    exact hholes
  have hrow : ell + gamma - (1 + ell) * A ≤ 2 * ell * u := by
    have hrow := (S.universal_partner_common_good_resources r p hpair hW hd hgap hN).1
    dsimp only [ell, gamma, h, A, u]
    nlinarith only [hrow]
  have hDH : DH ∈ Icc (0 : ℝ) ((1 - ell) * (1 - u) - 2 * gamma) := by
    refine ⟨integral_nonneg (fun x => (S.universalRootDeficit_mem_Icc r x).1), ?_⟩
    have hbound := S.universalPartnerHole_deficit_cap r p hpair hW hd hgap hN
    dsimp only [DH, ell, gamma, h, u]
    nlinarith only [hbound]
  have hlicenses := UniversalCornerScalar.price_licenses hA hell hh hc hbcap hu hrow hDH
    hz hq hholes'
  exact ⟨hz, hzu, hq, hholes', hlicenses⟩

namespace ReverseRecovery

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {S : SelectedHighLowStructure W m}

private theorem corner_price_entry (R : S.ReverseRecovery) (r p : S.I)
    (hplateau : R.plateau = {p}) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r p) (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = r.val then 0 else 1) :
    ∃ _P : S.UniversalPhysicalPrimal r c,
      (-m) ∈ Icc (363 / 589 : ℝ) (9 / 11) ∧
      (138261458236451 : ℝ) / 1116960975000000 < c ∧
      1 - 2 * d < 23243417 / 10 ^ 8 ∧
      S.originalAtomMass r ∈ Ioo (1 / 3 : ℝ) (369 / 1000) ∧
      0 < S.originalAtomMass p ∧ S.originalAtomMass p ≤ 1 - 2 * S.originalAtomMass r ∧
      μ.real (S.universalPartnerCommonRegion r p) ∈
        Ico (0 : ℝ) (1 - 2 * S.originalAtomMass r) ∧
      3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m) ∈ Ioo (0 : ℝ) 1 ∧
      2 * S.originalAtomMass r * (1 + m) < 3 * (2 * (c - m * d) + m) ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) ∧
      0 < μ.real (S.universalPartnerHoleRegion r p) ∧
      μ.real (S.universalPartnerCommonRegion r p) +
        μ.real (S.universalPartnerHoleRegion r p \ S.reverseCompulsorySource {p}) <
          1 - 2 * S.originalAtomMass r ∧
      0 < PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
        {x | S.ρ x = r.val} ∧
      0 < μ (S.universalNegativeRegion r p) ∧ 0 < S.universalNegativeChargeMass r p ∧
      S.universalNegativeChargeMass r p < (-m) * μ.real (S.universalNegativeRegion r p) := by
  obtain ⟨hell, hc, hh, hA, hAlt, _, hmargin, hpositive, hN, _, _, _, hsource, _, hstrict⟩ :=
    R.corner_universal_entry r p hplateau hW hd hgap he heq hglobal hpair hpeak huniv
  obtain ⟨P⟩ := S.exists_universal_physical_primal r hW hd hgap hN
  have hAhalf : S.originalAtomMass r ≤ 1 / 2 := by linarith only [hAlt]
  have hell' : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith only [hell.1, hell.2]
  obtain ⟨hH, hbcap, htheta⟩ :=
    P.corner_hole_licenses S r p hpair hW hd hgap hN hA hAhalf hell' hmargin hsource
  have hcut := P.corner_mass_lt_cutoff S r p hpair hW hd hgap hN hA hAhalf hell hmargin
    hpositive hh hc hbcap
  have hb : 0 < S.originalAtomMass p :=
    ENNReal.toReal_pos (S.hfibers p.val p.property).2.1.ne' (measure_ne_top _ _)
  have hu : μ.real (S.universalPartnerCommonRegion r p) < 1 - 2 * S.originalAtomMass r := by
    have hk : 0 ≤ μ.real (S.universalPartnerHoleRegion r p \ S.reverseCompulsorySource {p}) :=
      measureReal_nonneg
    linarith only [hstrict, hk]
  have htheta0 : 0 < 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m) := by
    have hA0 : 0 < S.originalAtomMass r := lt_trans (by norm_num) hA
    have hdelta : 0 < 1 + m := by linarith only [hell.2]
    have hp := mul_pos hA0 hdelta
    have hscaled : (1 + m) * S.originalAtomMass r < 3 * (2 * (c - m * d) + m) := by
      nlinarith only [hmargin, hp]
    have hd := (lt_div_iff₀ hA0).mpr hscaled
    linarith only [hd]
  have hnegative := P.corner_negative_region_pos S r p hpair hW hd hgap hN ⟨hA, hcut⟩
    hell hh hc hmargin hu
  have hNpos := S.universalNegativeChargeMass_pos r p hW hd hgap hN hnegative
  have hNn := S.universalNegativeChargeMass_lt_multiplier_mass r p hW hd hgap hN hnegative
  exact ⟨P, hell, hc, hh, ⟨hA, hcut⟩, hb, hbcap, ⟨measureReal_nonneg, hu⟩,
    ⟨htheta0, htheta⟩, hmargin, hN, hH, hstrict, hpositive, hnegative, hNpos, hNn⟩

/-- The same original universal peak and singleton recovery cannot occur
at the W/E2 corner. Every price stock is derived from its actual primal. -/
theorem no_corner_one_center_universal (R : S.ReverseRecovery) (r p : S.I)
    (hplateau : R.plateau = {p}) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r p) (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = r.val then 0 else 1) : False := by
  obtain ⟨P, hellbox, hc, hh, hA, hb, hbcap, hu, hthetaBox, hmargin, hN, _, hstrict,
    _, hBpos, hNpos, hNn⟩ :=
    R.corner_price_entry r p hplateau hW hd hgap he heq hglobal hpair hpeak huniv
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let ell := -m
  let h := 1 - 2 * d
  let gamma := 2 * (c - m * d) + m
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let B := S.universalNegativeRegion r p
  let Rcap := min (1 - 3 * A + b) ((1 - μ.real U - 2 * ell * A - 3 * gamma) / ell)
  let z := S.universalSharedHoleRadius r p Rcap
  let q := S.universalHoleSquareMoment r p
  let alpha := min (1 - 2 * A - b) (Real.sqrt q)
  let theta := 3 * gamma / A - (1 + m)
  let DH := ∫ x in H, S.universalRootDeficit r x ∂μ
  let chi := if theta < 1 / 2 then
    DH * (1 - 2 * theta) / ((A - z) * (1 - theta) - DH) else 0
  let Irec := μ.real H / (A - z) + q / ((A - z) * (A - z - alpha))
  let RP := ell + gamma - (1 + ell) * A
  let RR := (2 * ell - 1) * A + 3 * gamma
  let D := 2 * ell * (1 - 2 * A) - RP
  let Ecap := max (A - 3 * gamma) 0 * D ^ 2 / (4 * RP * RR)
  have hgamma : gamma = 2 * c - ell * h := by dsimp only [gamma, ell, h]; ring
  have htheta : theta = 3 * gamma / A - (1 - ell) := by
    dsimp only [theta, ell]
    ring
  have hell : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith only [hellbox.1, hellbox.2]
  have hAhalf : A ≤ 1 / 2 := by linarith only [hA.2]
  have hlic := P.corner_scalar_licenses S r p hpair hW hd hgap hN hA hellbox hh hc
    hbcap hu hmargin hBpos
  dsimp only at hlic
  rw [← hgamma, ← htheta] at hlic
  change z ∈ Icc (0 : ℝ) Rcap ∧ z ≤ μ.real U ∧ 0 ≤ q ∧
    q + z ^ 2 ≤ h - A ^ 2 - b ^ 2 - 2 * b * (1 - A - b - μ.real U) ∧
    Ecap < 3 * gamma / 5 ∧ Ecap < 1 / 25 ∧
    1 / 200 < gamma - max (1 - 2 * theta) 0 * Rcap ∧ DH < theta * (A - z) at hlic
  obtain ⟨hz, hzu, hq, hholes, hEthree, hEsmall, hzero, hDH⟩ := hlic
  have hRdef : Rcap = min (1 - 3 * A + b)
      ((1 - μ.real U + 2 * m * A - 3 * gamma) / (-m)) := by
    dsimp only [Rcap, ell]
    congr 1
    ring
  have hcap := P.ae_negative_shared_hole_cap S r p hpair hW hd hgap hN hA.1 hAhalf
    hell hmargin hu.2
  change ∀ᵐ x ∂μ.restrict B,
    S.universalOwnMass x + S.universalGoodMissingMass r p d c x ≤
      min (1 - 3 * A + b) ((1 - μ.real U + 2 * m * A - 3 * gamma) / (-m)) at hcap
  rw [← hRdef] at hcap
  have hown := P.ae_negative_own_le_shared_radius S r p hpair hW hd hgap hN hA.1
    hAhalf hell hmargin Rcap hcap
  have hzbad := hz.2.trans (min_le_left (1 - 3 * A + b)
    ((1 - μ.real U - 2 * ell * A - 3 * gamma) / ell))
  obtain ⟨hk, halpha⟩ := corner_pole_guards hA.1 hbcap hzbad (q := q)
  have hchi : chi ∈ Icc (0 : ℝ) (1 / 2) :=
    corner_deficit_coefficient_bound hk
      (integral_nonneg (fun x => (S.universalRootDeficit_mem_Icc r x).1)) hDH
  have hgammapos : 0 < gamma := by
    have hpositive := mul_pos (show 0 < A by linarith only [hA.1])
      (show 0 < 1 + m by linarith only [hell.2])
    change 2 * A * (1 + m) < 3 * gamma at hmargin
    nlinarith only [hmargin, hpositive]
  have hzero' : max (1 - 2 * theta) 0 * Rcap < gamma := by linarith only [hzero]
  have hendpoint := P.ae_universal_price_endpoint S r p hpair hW hd hgap hN hA.1 hbcap
    hAhalf hell hmargin Rcap hRdef hu.2 hDH hzero'
  have hBreal : 0 < μ.real B := ENNReal.toReal_pos hBpos.ne' (measure_ne_top μ B)
  have hUpos : 0 < μ.real U :=
    lt_of_lt_of_le hBreal (measureReal_mono (fun _ hx => hx.1))
  have ha := S.ae_hole_missing_mass_le_min_capacity_sqrt r p hpair hW hd hgap hell.2 hN
  have halphaAE : ∀ᵐ x ∂μ.restrict B, alpha < A - S.universalOwnMass x := by
    filter_upwards [hown] with x hx
    linarith only [halpha, hx]
  have hrow := P.ae_universal_negative_price_row S r p hpair R hW hd hgap hN hA.1
    hAhalf hell hmargin hplateau hUpos hu.2 theta alpha hthetaBox.1.le rfl ha halphaAE
  have hpartner := P.ae_partner_copy_lower_row S r p hpair hW hd hgap hN hA.1 hAhalf
    hell hmargin
  have hErr := P.integrable_universalExtraHoleCopyError S r p hpair R hW hd hgap hN
    hA.1 hAhalf hell hmargin hplateau hUpos
  have hErrBound := P.ae_universalExtraHoleCopyError_le S r p hpair R hW hd hgap hN
    hA.1 hAhalf hell hmargin hplateau hUpos
  have hcoarse := corner_error_cap_le_coarse S r p hpair hW hd hgap hN hA hellbox
    hmargin hstrict hBpos
  dsimp only at hcoarse
  rw [← hgamma, ← htheta] at hcoarse
  change μ.real (S.universalExtraHoleRegion r p) * max (ell - theta) 0 *
    μ.real (S.universalGoodCommonRegion r p d c) / μ.real U ≤ Ecap at hcoarse
  have hErrAE : ∀ᵐ x ∂μ.restrict B, S.universalExtraHoleCopyError r p d c x ≤ Ecap := by
    filter_upwards [hErrBound] with x hx
    have hphysical : S.universalExtraHoleCopyError r p d c x ≤
        μ.real (S.universalExtraHoleRegion r p) * max (ell - theta) 0 *
          μ.real (S.universalGoodCommonRegion r p d c) / μ.real U := by
      convert hx.2 using 1
      dsimp only [ell, theta, gamma, A, U]
      ring
    exact hphysical.trans hcoarse
  have hpoint : ∀ᵐ x ∂μ.restrict B,
      (A - b) * (-S.rootChargeRow r x) -
        S.universalOwnMass x * (-S.rootChargeRow r x) + gamma ≤
          (max (b * ell - gamma) 0 * Irec * (-S.rootChargeRow r x) +
            chi * ((-S.rootChargeRow r x) * S.universalGoodMissingMass r p d c x)) /
              ell + S.universalExtraHoleCopyError r p d c x := by
    filter_upwards [hpartner, hrow, hendpoint] with x hp hrw he
    have hfirst : (A - b) * (-S.rootChargeRow r x) -
        S.universalOwnMass x * (-S.rootChargeRow r x) + gamma ≤
          S.universalHoleChargeRow r p x := by
      change (A - b - S.universalOwnMass x) * (-S.rootChargeRow r x) + gamma ≤
        S.universalHoleChargeRow r p x at hp
      nlinarith only [hp]
    have hsecond := hfirst.trans hrw
    have hthird := add_le_add_left he (S.universalExtraHoleCopyError r p d c x)
    convert hsecond.trans hthird using 1
    ring
  have hjInt : IntegrableOn (fun x => -S.rootChargeRow r x *
      S.universalGoodMissingMass r p d c x) B μ := by
    convert (S.integrable_universalWeightedGoodMissing r p d c).integrableOn using 1
    ext x
    ring
  have hswap : (∫ x in B, -S.rootChargeRow r x *
      S.universalGoodMissingMass r p d c x ∂μ) =
      S.universalWeightedGoodMissingMoment r p d c := by
    change (∫ x in B, -S.rootChargeRow r x *
      S.universalGoodMissingMass r p d c x ∂μ) =
      ∫ x in B, S.universalGoodMissingMass r p d c x * (-S.rootChargeRow r x) ∂μ
    congr 1
    funext x
    ring
  have hcopy0 := UniversalSignedPrice.integrated_signed_copy B
    (fun x => -S.rootChargeRow r x) S.universalOwnMass
    (S.universalGoodMissingMass r p d c) (S.universalExtraHoleCopyError r p d c)
    A b gamma ell (max (b * ell - gamma) 0 * Irec) chi
    (by linarith only [hell.1]) ((S.integrable_universalNegativeCharge r).integrableOn)
    ((S.integrable_universalWeightedOwn r).integrableOn) hjInt hErr.1 hpoint
  rw [hswap] at hcopy0
  change ell * ((A - b) * S.universalNegativeChargeMass r p -
    S.universalWeightedOwnMoment r p + gamma * μ.real B) ≤
      max (b * ell - gamma) 0 * Irec * S.universalNegativeChargeMass r p +
        chi * S.universalWeightedGoodMissingMoment r p d c +
          ell * (∫ x in B, S.universalExtraHoleCopyError r p d c x ∂μ) at hcopy0
  have hErrInt : (∫ x in B, S.universalExtraHoleCopyError r p d c x ∂μ) ≤
      Ecap * μ.real B := by
    have hmono := integral_mono_ae hErr.1
      (integrable_const (μ := μ.restrict B) Ecap) hErrAE
    rw [setIntegral_const, smul_eq_mul] at hmono
    simpa only [mul_comm] using hmono
  have hcopy : ell * ((A - b) * S.universalNegativeChargeMass r p -
    S.universalWeightedOwnMoment r p + gamma * μ.real B) ≤
      max (b * ell - gamma) 0 * Irec * S.universalNegativeChargeMass r p +
        chi * S.universalWeightedGoodMissingMoment r p d c + ell * Ecap * μ.real B := by
    have hscaled := mul_le_mul_of_nonneg_left hErrInt
      (show 0 ≤ ell by linarith only [hell.1])
    nlinarith only [hcopy0, hscaled]
  have hownBudget := P.weighted_own_le_shared_radius S r p hpair hW hd hgap hN hA.1
    hAhalf hell hmargin Rcap hcap
  have htotal := P.weighted_hole_inventory_le_actual S r p hpair hW hd hgap hN hA.1
    hAhalf hell hmargin hu.2
  rw [← hRdef] at htotal
  have hZd : 0 ≤ S.universalWeightedGoodMissingMoment r p d c := by
    apply integral_nonneg_of_ae
    filter_upwards [S.ae_universalNegativeCharge_mem_Ioo r p hW hd hgap hN] with x hx
    exact mul_nonneg (S.universalGoodMissingMass_nonneg r p d c x) hx.1.le
  by_cases hprice : 0 < b * ell - gamma
  · rw [max_eq_left hprice.le] at hcopy
    have hF := UniversalSignedPrice.positive_price_necessary A b gamma ell Ecap
      ((b * ell - gamma) * Irec) chi z Rcap (S.universalNegativeChargeMass r p)
      (μ.real B) (S.universalWeightedOwnMoment r p)
      (S.universalWeightedGoodMissingMoment r p d c)
      hell.1 hgammapos hEthree hNpos hNn hchi.2 hZd hownBudget htotal hcopy
    have hmass : μ.real H = 1 - A - b - μ.real U := by
      have hmass := S.universalPartner_regions_mass r p hpair.1
      dsimp only [H, A, b, U]
      linarith only [hmass]
    have hzScalar : z ∈ Icc (0 : ℝ) (min (1 - 3 * A + b)
        ((1 - μ.real U - 2 * ell * A - 3 * (2 * c - ell * h)) / ell)) := by
      rw [← hgamma]
      exact hz
    have hpriceScalar : 0 < b * ell - (2 * c - ell * h) := by
      rw [← hgamma]
      exact hprice
    apply UniversalCornerScalar.positive_price_false hA hellbox hh hc hb hbcap hu
      hzScalar hzu hq hholes hpriceScalar
    dsimp only
    rw [← hgamma]
    dsimp only [Irec, alpha] at hF
    rw [hmass] at hF
    exact hF
  · rw [max_eq_right (le_of_not_gt hprice), zero_mul, zero_mul, zero_add] at hcopy
    have hraw := corner_nonpositive_copy_bound
      (show 0 < ell by linarith only [hell.1]) hNpos.le hZd
      (hchi.2.trans (by linarith only [hell.1])) (min_le_left _ _) htotal hcopy
    apply UniversalCornerScalar.nonpositive_price_false (A := A) (b := b) (ell := ell)
      (h := h) (c := c) (Ecap := Ecap) (N := S.universalNegativeChargeMass r p)
      (n := μ.real B) hA.1 hellbox hh hc
    · rw [← hgamma]
      linarith only [hprice]
    · rw [← hgamma, ← htheta]
      exact hthetaBox.2
    · exact hEsmall
    · exact hNpos
    · exact hNn
    · rw [← hgamma]
      exact hraw

end ReverseRecovery

end Erdos1017.CappedModel.SelectedHighLowStructure
