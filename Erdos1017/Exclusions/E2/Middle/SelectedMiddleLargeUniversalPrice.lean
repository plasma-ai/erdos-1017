module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalPriceJoin
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleLargeUniversalSystem
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleLargeUniversalPriceBounds

/-!
# Price-test exclusion of the large universal head

The middle large-head state cannot satisfy the certificate's five strict price
tests, with all copied rows and stocks taken from its own primal
(`no_middle_large_universal_of_price_tests`).
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

private theorem middle_integrated_price_positive
    {A b gamma ell Ecap price chi R N n TB Zd : ℝ}
    (hell : 0 < ell) (hE : Ecap < gamma) (hN : 0 < N) (hNn : N < ell * n)
    (hchi : chi ≤ ell) (hZd : 0 ≤ Zd) (hstock : TB + Zd ≤ R * N)
    (hcopy : ell * ((A - b) * N - TB + gamma * n) ≤
      price * N + chi * Zd + ell * Ecap * n) :
    0 < price + ell * (R - A + b) - gamma + Ecap := by
  have hweighted : ell * TB + chi * Zd ≤ ell * R * N := by
    have hchiZd := mul_le_mul_of_nonneg_right hchi hZd
    have hpaid := mul_le_mul_of_nonneg_left hstock hell.le
    nlinarith only [hchiZd, hpaid]
  have hstrict := mul_lt_mul_of_pos_left hNn (sub_pos.mpr hE)
  have hcombined : (gamma - Ecap) * N <
      (price + ell * (R - A + b)) * N := by
    nlinarith only [hcopy, hweighted, hstrict]
  exact (mul_pos_iff_of_pos_right hN).mp (by nlinarith only [hcombined])

private theorem middle_coarse_price_endpoint
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell' : -m < 1)
    (theta R C ax j v b gamma ell : ℝ)
    (htheta : 0 ≤ theta) (hC : 0 ≤ C)
    (hpole : 0 < S.originalAtomMass r - R - C)
    (hDH : (∫ x in S.universalPartnerHoleRegion r p,
      S.universalRootDeficit r x ∂μ) < theta * (S.originalAtomMass r - R))
    (hax : ax ≤ R)
    (ha : ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x ≤ C)
    (hDmax : ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalRootDeficit r x ≤ 1 - theta)
    (hell : 0 < ell) (hv : v ∈ Icc (0 : ℝ) ell)
    (hj : 0 ≤ j) (hjR : j ≤ R)
    (hzero : max (1 - 2 * theta) 0 * R < gamma) :
    let DH := ∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ
    let chi := if theta < 1 / 2 then
      DH * (1 - 2 * theta) / ((S.originalAtomMass r - R) * (1 - theta) - DH) else 0
    UniversalSignedPrice.priceFunction μ (S.universalPartnerHoleRegion r p)
      (S.universalPartnerHoleMissingMass r p) (S.universalRootDeficit r)
      (S.originalAtomMass r) b gamma theta ax j v ≤ v / ell *
        (max (b * ell - gamma) 0 *
          (μ.real (S.universalPartnerHoleRegion r p) / (S.originalAtomMass r - R - C)) +
            j * chi) := by
  let H := S.universalPartnerHoleRegion r p
  let a := S.universalPartnerHoleMissingMass r p
  let D := S.universalRootDeficit r
  let A := S.originalAtomMass r
  let DH := ∫ x in H, D x ∂μ
  let chi := if theta < 1 / 2 then
    DH * (1 - 2 * theta) / ((A - R) * (1 - theta) - DH) else 0
  have hk : 0 < A - R := by linarith only [hpole, hC]
  have hCk : C < A - R := by linarith only [hpole]
  have hCax : C < A - ax := by linarith only [hpole, hax]
  have hden : ∀ᵐ x ∂μ.restrict H, 0 < A - a x - ax := by
    filter_upwards [ha] with x hx
    dsimp only [a, A] at *
    linarith only [hpole, hax, hx]
  have hrec := S.integrable_hole_reciprocal r p ax C hCax ha
  have hdef := S.integrable_hole_positive_deficit_ratio r p theta ax C htheta hCax ha
  have hrecBound : (∫ x in H, 1 / (A - a x - ax) ∂μ) ≤
      μ.real H / (A - R - C) := by
    have hmono := integral_mono_ae hrec
      (integrable_const (μ := μ.restrict H) (1 / (A - R - C))) (by
        filter_upwards [ha] with x hx
        apply one_div_le_one_div_of_le hpole
        change S.universalPartnerHoleMissingMass r p x ≤ C at hx
        linarith only [hx, hax])
    rw [setIntegral_const, smul_eq_mul] at hmono
    simpa only [div_eq_mul_inv, one_mul] using hmono
  have hdefBound : (∫ x in H, max (D x - theta) 0 / (A - a x - ax) ∂μ) ≤ chi := by
    by_cases hhalf : theta < 1 / 2
    · simp only [chi, ite_eq_left hhalf]
      exact S.hole_positive_deficit_ratio_le_shared r p hpair hW hd hgap hell'
        theta R ax C htheta hhalf hk hDH hax hCk ha hDmax
    · have hzero := UniversalSignedPrice.nonpositive_deficit_integral_eq_zero
        μ H a D theta (A - ax) (le_of_not_gt hhalf) hDmax
      have hzero' : (∫ x in H, max (D x - theta) 0 / (A - a x - ax) ∂μ) = 0 := by
        convert hzero using 1
        congr 1
        funext x
        ring
      simp only [chi, ite_eq_right hhalf]
      exact hzero'.le
  have hpriceV := S.integrable_universalSignedPrice r p theta ax C j v b gamma
    htheta hj hCax ha
  have hpriceEll := S.integrable_universalSignedPrice r p theta ax C j ell b gamma
    htheta hj hCax ha
  have hpoint : ∀ᵐ x ∂μ.restrict H, D x ≤ 1 - theta ∧ 0 < A - a x - ax :=
    hDmax.and hden
  have hchord := UniversalSignedPrice.priceFunction_chord μ H a D A b gamma theta
    ax j R v ell hell hv hj hjR hzero hpoint hpriceV hpriceEll
  have hendpoint := UniversalSignedPrice.priceFunction_endpoint_le μ H a D A b gamma
    theta ax j ell (μ.real H / (A - R - C)) chi hj hden hpriceEll hrec hdef
    hrecBound hdefBound
  exact hchord.trans (mul_le_mul_of_nonneg_left hendpoint (div_nonneg hv.1 hell.le))

private theorem middle_deficit_coefficient_bound {theta k DH : ℝ}
    (hk : 0 < k) (hDHk : DH < theta * k) :
    (if theta < 1 / 2 then DH * (1 - 2 * theta) / (k * (1 - theta) - DH) else 0) ≤
      1 / 2 := by
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
    exact hbound.trans hhalf.le
  · rw [ite_eq_right hhalf]
    norm_num

private theorem UniversalPhysicalPrimal.middle_signed_price_necessary
    (S : SelectedHighLowStructure W m) (Rec : S.ReverseRecovery) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (hr : Rec.plateau = {p})
    (hu : 0 < μ.real (S.universalPartnerCommonRegion r p))
    (hucap : μ.real (S.universalPartnerCommonRegion r p) < 1 - 2 * S.originalAtomMass r)
    (hBpos : 0 < μ (S.universalNegativeRegion r p))
    (Rcap C Ecap : ℝ) (hC : 0 ≤ C)
    (hRcap : min (1 - 3 * S.originalAtomMass r + S.originalAtomMass p)
      ((1 - μ.real (S.universalPartnerCommonRegion r p) + 2 * m * S.originalAtomMass r -
        3 * (2 * (c - m * d) + m)) / (-m)) ≤ Rcap)
    (ha : ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x ≤ C)
    (hpole : 0 < S.originalAtomMass r - Rcap - C)
    (hDH : (∫ x in S.universalPartnerHoleRegion r p,
      S.universalRootDeficit r x ∂μ) <
        (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) *
          (S.originalAtomMass r - Rcap))
    (hzero : max (1 - 2 * (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
      (1 + m))) 0 * Rcap < 2 * (c - m * d) + m)
    (hErrBudget : μ.real (S.universalExtraHoleRegion r p) *
      max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))) 0 *
        μ.real (S.universalGoodCommonRegion r p d c) /
          μ.real (S.universalPartnerCommonRegion r p) ≤ Ecap)
    (hE : Ecap < 2 * (c - m * d) + m) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let ell := -m
    let gamma := 2 * (c - m * d) + m
    0 < max (b * ell - gamma) 0 * μ.real (S.universalPartnerHoleRegion r p) /
      (A - Rcap - C) + ell * (Rcap - A + b) - gamma + Ecap := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let ell := -m
  let gamma := 2 * (c - m * d) + m
  let theta := 3 * gamma / A - (1 + m)
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalNegativeRegion r p
  let DH := ∫ x in H, S.universalRootDeficit r x ∂μ
  let chi := if theta < 1 / 2 then
    DH * (1 - 2 * theta) / ((A - Rcap) * (1 - theta) - DH) else 0
  let price := max (b * ell - gamma) 0 * (μ.real H / (A - Rcap - C))
  have htheta : 0 ≤ theta := by
    have hApos : 0 < A := by linarith only [hA]
    have hscaled : (1 + m) * A < 3 * gamma := by
      have hpositive := mul_pos hApos (show 0 < 1 + m by linarith only [hell.2])
      change 2 * A * (1 + m) < 3 * gamma at hmargin
      nlinarith only [hmargin, hpositive]
    have hdiv := (lt_div_iff₀ hApos).mpr hscaled
    dsimp only [theta]
    linarith only [hdiv]
  have hk : 0 < A - Rcap := by linarith only [hpole, hC]
  have hchi : chi ≤ ell := (middle_deficit_coefficient_bound hk hDH).trans
    (by linarith only [hell.1])
  have hactual := P.ae_negative_shared_hole_cap S r p hpair hW hd hgap hN hA hAhalf
    hell hmargin hucap
  have hcap : ∀ᵐ x ∂μ.restrict B,
      S.universalOwnMass x + S.universalGoodMissingMass r p d c x ≤ Rcap :=
    hactual.mono (fun _ hx => hx.trans hRcap)
  have hown : ∀ᵐ x ∂μ.restrict B, S.universalOwnMass x ≤ Rcap := by
    filter_upwards [hcap] with x hx
    linarith only [hx, S.universalGoodMissingMass_nonneg r p d c x]
  have halphaAE : ∀ᵐ x ∂μ.restrict B, C < A - S.universalOwnMass x := by
    filter_upwards [hown] with x hx
    linarith only [hpole, hx]
  have hrow := P.ae_universal_negative_price_row S r p hpair Rec hW hd hgap hN hA
    hAhalf hell hmargin hr hu hucap theta C htheta rfl ha halphaAE
  have hDmax := P.ae_hole_deficit_le_one_sub_threshold S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  have hnegative := S.ae_universalNegativeCharge_mem_Ioo r p hW hd hgap hN
  have hendpoint : ∀ᵐ x ∂μ.restrict B,
      UniversalSignedPrice.priceFunction μ H (S.universalPartnerHoleMissingMass r p)
        (S.universalRootDeficit r) A b gamma theta (S.universalOwnMass x)
        (S.universalGoodMissingMass r p d c x) (-S.rootChargeRow r x) ≤
          (-S.rootChargeRow r x) / ell *
            (price + S.universalGoodMissingMass r p d c x * chi) := by
    filter_upwards [hcap, hown, hnegative] with x hx hax hv
    have hj : S.universalGoodMissingMass r p d c x ≤ Rcap := by
      linarith only [hx, (S.universalOwnMass_mem_Icc x).1]
    exact middle_coarse_price_endpoint S r p hpair hW hd hgap hell.2 theta Rcap C
      (S.universalOwnMass x) (S.universalGoodMissingMass r p d c x) (-S.rootChargeRow r x)
      b gamma ell htheta hC hpole hDH hax ha hDmax
      (by linarith only [hell.1]) ⟨hv.1.le, hv.2.le⟩
      (S.universalGoodMissingMass_nonneg r p d c x) hj hzero
  have hpartner := P.ae_partner_copy_lower_row S r p hpair hW hd hgap hN hA hAhalf
    hell hmargin
  have hErr := P.integrable_universalExtraHoleCopyError S r p hpair Rec hW hd hgap hN
    hA hAhalf hell hmargin hr hu
  have hErrBound := P.ae_universalExtraHoleCopyError_le S r p hpair Rec hW hd hgap hN
    hA hAhalf hell hmargin hr hu
  have hErrAE : ∀ᵐ x ∂μ.restrict B, S.universalExtraHoleCopyError r p d c x ≤ Ecap := by
    filter_upwards [hErrBound] with x hx
    have hbound : S.universalExtraHoleCopyError r p d c x ≤
        μ.real (S.universalExtraHoleRegion r p) * max (ell - theta) 0 *
          μ.real (S.universalGoodCommonRegion r p d c) /
            μ.real (S.universalPartnerCommonRegion r p) := by
      convert hx.2 using 1
      dsimp only [ell, theta, gamma, A]
      ring
    exact hbound.trans hErrBudget
  have hpoint : ∀ᵐ x ∂μ.restrict B,
      (A - b) * (-S.rootChargeRow r x) -
        S.universalOwnMass x * (-S.rootChargeRow r x) + gamma ≤
          (price * (-S.rootChargeRow r x) +
            chi * ((-S.rootChargeRow r x) * S.universalGoodMissingMass r p d c x)) /
              ell + S.universalExtraHoleCopyError r p d c x := by
    filter_upwards [hpartner, hrow, hendpoint] with x hp hrw he
    have hfirst : (A - b) * (-S.rootChargeRow r x) -
        S.universalOwnMass x * (-S.rootChargeRow r x) + gamma ≤
          S.universalHoleChargeRow r p x := by
      change (A - b - S.universalOwnMass x) * (-S.rootChargeRow r x) + gamma ≤
        S.universalHoleChargeRow r p x at hp
      nlinarith only [hp]
    have hbound := (hfirst.trans hrw).trans
      (add_le_add_left he (S.universalExtraHoleCopyError r p d c x))
    convert hbound using 1
    ring
  have hjInt : IntegrableOn (fun x => -S.rootChargeRow r x *
      S.universalGoodMissingMass r p d c x) B μ := by
    convert (S.integrable_universalWeightedGoodMissing r p d c).integrableOn using 1
    ext x
    ring
  have hcopy := UniversalSignedPrice.integrated_signed_copy B
    (fun x => -S.rootChargeRow r x) S.universalOwnMass
    (S.universalGoodMissingMass r p d c) (S.universalExtraHoleCopyError r p d c)
    A b gamma ell price chi (by linarith only [hell.1])
    ((S.integrable_universalNegativeCharge r).integrableOn)
    ((S.integrable_universalWeightedOwn r).integrableOn) hjInt hErr.1 hpoint
  have hswap : (∫ x in B, -S.rootChargeRow r x *
      S.universalGoodMissingMass r p d c x ∂μ) =
      S.universalWeightedGoodMissingMoment r p d c := by
    change (∫ x in B, -S.rootChargeRow r x *
      S.universalGoodMissingMass r p d c x ∂μ) =
      ∫ x in B, S.universalGoodMissingMass r p d c x * (-S.rootChargeRow r x) ∂μ
    congr 1
    funext x
    ring
  rw [hswap] at hcopy
  have hErrInt : (∫ x in B, S.universalExtraHoleCopyError r p d c x ∂μ) ≤
      Ecap * μ.real B := by
    have hmono := integral_mono_ae hErr.1
      (integrable_const (μ := μ.restrict B) Ecap) hErrAE
    rw [setIntegral_const, smul_eq_mul] at hmono
    simpa only [mul_comm] using hmono
  have hcopy' : ell * ((A - b) * S.universalNegativeChargeMass r p -
    S.universalWeightedOwnMoment r p + gamma * μ.real B) ≤
      price * S.universalNegativeChargeMass r p +
        chi * S.universalWeightedGoodMissingMoment r p d c + ell * Ecap * μ.real B := by
    have hscaled := mul_le_mul_of_nonneg_left hErrInt
      (show 0 ≤ ell by linarith only [hell.1])
    change ell * ((A - b) * S.universalNegativeChargeMass r p -
      S.universalWeightedOwnMoment r p + gamma * μ.real B) ≤
        price * S.universalNegativeChargeMass r p +
          chi * S.universalWeightedGoodMissingMoment r p d c +
            ell * (∫ x in B, S.universalExtraHoleCopyError r p d c x ∂μ) at hcopy
    nlinarith only [hcopy, hscaled]
  have hstock := S.universalWeightedHoleInventory_le r p d c Rcap hcap
  have hZd : 0 ≤ S.universalWeightedGoodMissingMoment r p d c := by
    apply integral_nonneg_of_ae
    filter_upwards [hnegative] with x hx
    exact mul_nonneg (S.universalGoodMissingMass_nonneg r p d c x) hx.1.le
  have hNpos := S.universalNegativeChargeMass_pos r p hW hd hgap hN hBpos
  have hNn := S.universalNegativeChargeMass_lt_multiplier_mass r p hW hd hgap hN hBpos
  have hpositive := middle_integrated_price_positive (by linarith only [hell.1]) hE
    hNpos hNn hchi hZd hstock hcopy'
  convert hpositive using 1
  dsimp only [price]
  ring

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual middle large-head state cannot satisfy the certificate's
strict price tests `PriceTests`. All copied rows and stocks use its own primal. -/
theorem no_middle_large_universal_of_price_tests
    (S : SelectedHighLowStructure W m) (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = r.val then 0 else 1)
    (hnecessary : (S.middleLargeUniversalPoint r p q).Necessary)
    (htests : (S.middleLargeUniversalPoint r p q).PriceTests) : False := by
  let X := S.middleLargeUniversalPoint r p q
  let A := S.originalAtomMass r
  let gamma := 2 * (c - m * d) + m
  let H := S.universalPartnerHoleRegion r p
  let DH := ∫ x in H, S.universalRootDeficit r x ∂μ
  obtain ⟨P, _, hA, _, hm, hell45, hgamma, _, hyupper, hymax,
    _, _, _, _, hmargin⟩ :=
    S.middle_large_universal_initial_guards r p hpair hW hq hdq hgap hglobal hpeak huniv
  obtain ⟨Rec, hr, _, _, _, hstrict⟩ :=
    S.middle_large_universal_partner_recovery r p hpair hW hq hdq hgap hglobal
      hpeak huniv hA.1
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸
    Benchmark.e2_density_mem ⟨by linarith only [hq.1], hq.2.le⟩
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  have hycap : (1 - m - 4 * (c - m * d)) / (1 + m) < 369 / 1000 := by
    linarith only [hyupper, hymax]
  have hBpos := P.middle_large_universal_negative_region_pos_of_ratio S Rec r p hpair
    hW hd hgap hr hN hA.1 hA.2 hell45 hycap hmargin
  have hell : -m ∈ Ioo (1 / 2 : ℝ) 1 :=
    ⟨by linarith only [hell45.1], hell45.2⟩
  have hAhalf : A ≤ 1 / 2 := by linarith only [hA.2]
  have hApos : 0 < X.A := by change 0 < A; linarith only [hA.1]
  have hellEq : X.ell = -m := by
    change MiddleE2LargeUniversal.ellq q = -m
    rw [hm, neg_neg]
    rfl
  have hgEq : X.g = LowerE2Scalar.gapFloor q := by
    change MiddleE2LargeUniversal.gq q = LowerE2Scalar.gapFloor q
    simp only [MiddleE2LargeUniversal.gq, MiddleE2LargeUniversal.rq,
      LowerE2Scalar.gapFloor, LowerE2Scalar.denominator, pow_two]
  have hyEq : X.y = 9 * q / (2 * LowerE2Scalar.denominator q) := by
    change MiddleE2LargeUniversal.yq q = _
    simp only [MiddleE2LargeUniversal.yq, MiddleE2LargeUniversal.rq,
      LowerE2Scalar.denominator, pow_two]
  have hdeEq : X.de = 1 + m := by
    change 1 - X.ell = 1 + m
    rw [hellEq]
    ring
  have hgammaFloor : X.g ≤ gamma := by rw [hgEq]; exact hgamma.le
  have hgpos : 0 < X.g := by
    rw [hgEq]
    have hqpos : 0 < q := by linarith only [hq.1]
    unfold LowerE2Scalar.gapFloor LowerE2Scalar.denominator
    positivity
  have hdelta : 0 < 1 + m := by linarith only [hell.2]
  have hDH0 : 0 ≤ DH :=
    integral_nonneg (fun x => (S.universalRootDeficit_mem_Icc r x).1)
  have hbudget : DH ≤ X.de * X.p := by
    have hcap := S.universalPartnerHole_deficit_cap r p hpair hW hd hgap hN
    have hratio := (div_lt_iff₀ hdelta).mp hyupper
    rw [← hyEq] at hratio
    rw [hdeEq]
    dsimp only [MiddleE2LargeUniversal.Point.p]
    change DH ≤ (1 + m) * (X.y - μ.real (S.universalPartnerCommonRegion r p))
    change DH ≤ _ at hcap
    nlinarith only [hcap, hratio]
  have hlicenses := MiddleE2LargeUniversal.Point.actual_price_licenses hnecessary htests
    hApos hgammaFloor hDH0 hbudget
  dsimp only at hlicenses
  rw [hdeEq] at hlicenses
  obtain ⟨hpole, _, _, hDH, hzero⟩ := hlicenses
  have ⟨_, hu, _, _, _, hEgap, hG⟩ := htests
  have ⟨_, _, _, _, _, _, _, heta, _, _, hC, _⟩ := hnecessary
  have hCcap := S.ae_middle_large_universal_hole_missing_le_cap r p hpair hW hq hdq
    hgap hglobal hpeak huniv
  have hRcap := MiddleE2LargeUniversal.Point.actual_radius_le
    (show 0 < X.ell by rw [hellEq]; linarith only [hell.1]) hgammaFloor
  rw [hellEq] at hRcap
  have hRcap' : min (1 - 3 * S.originalAtomMass r + S.originalAtomMass p)
      ((1 - μ.real (S.universalPartnerCommonRegion r p) + 2 * m * S.originalAtomMass r -
        3 * gamma) / (-m)) ≤ X.RC := by
    convert hRcap using 1
    change min (1 - 3 * A + X.b) ((1 - X.u + 2 * m * A - 3 * gamma) / (-m)) =
      min (1 - 3 * A + X.b) ((1 - X.u - 2 * (-m) * A - 3 * gamma) / (-m))
    congr 1
    ring
  have hmassMargin : X.u + μ.real (S.universalExtraHoleRegion r p) ≤ X.r0 := by
    rw [S.universal_extra_hole_mass_eq r p hpair hW hd hgap hell.2]
    exact hstrict.le
  have hresource : (X.ell + (3 * gamma / X.A - X.de)) *
      μ.real (S.universalGoodCommonRegion r p d c) ≤
        2 * X.ell * X.u - (X.ell + gamma - (1 + X.ell) * X.A) := by
    rw [hellEq, hdeEq]
    have hresources := (S.universal_partner_common_good_resources r p hpair hW hd hgap hN).2
    convert hresources using 1 <;> dsimp only [gamma, X, middleLargeUniversalPoint]
    ring
  have herror := MiddleE2LargeUniversal.Point.actual_error_le hApos
    (show 1 / 2 < X.ell by rw [hellEq]; exact hell.1) hgpos hu hgammaFloor
    (measureReal_nonneg (μ := μ) (s := S.universalExtraHoleRegion r p))
    (measureReal_nonneg (μ := μ) (s := S.universalGoodCommonRegion r p d c))
    hmassMargin hresource
  rw [hellEq, hdeEq] at herror
  have hucap : μ.real (S.universalPartnerCommonRegion r p) < 1 - 2 * A := by
    have hnonneg : 0 ≤ μ.real H - μ.real (S.reverseCompulsorySource {p}) := by
      rw [← S.universal_extra_hole_mass_eq r p hpair hW hd hgap hell.2]
      exact measureReal_nonneg
    linarith only [hstrict, hnonneg]
  have hzero' : max (1 - 2 * (3 * gamma / A - (1 + m))) 0 * X.RC < gamma := by
    simpa only [X, A, middleLargeUniversalPoint, max_comm] using hzero
  have hE : X.E < gamma := by linarith only [hEgap, hgammaFloor]
  have hpositive := P.middle_signed_price_necessary S Rec r p hpair hW hd hgap hN
    hA.1 hAhalf hell hmargin hr hu hucap hBpos X.RC X.C X.E hC hRcap' hCcap
    hpole hDH hzero' herror hE
  have hmass : μ.real H = X.eta := by
    have hmass := S.universalPartner_regions_mass r p hpair.1
    dsimp only [MiddleE2LargeUniversal.Point.eta, X, middleLargeUniversalPoint, H]
    linarith only [hmass]
  have hbill := MiddleE2LargeUniversal.Point.actual_price_bill_le htests heta hgammaFloor
    (le_rfl : X.E ≤ X.E)
  rw [MiddleE2LargeUniversal.Point.price_pole_eq] at hbill
  rw [hmass] at hpositive
  have hpositive' : 0 < max 0 (X.b * X.ell - gamma) * X.eta / (X.A - X.RC - X.C) +
      X.ell * (X.RC - X.A + X.b) - gamma + X.E := by
    rw [hellEq]
    simpa only [X, middleLargeUniversalPoint, gamma, max_comm] using hpositive
  linarith only [hpositive', hbill, hG]

end Erdos1017.CappedModel.SelectedHighLowStructure
