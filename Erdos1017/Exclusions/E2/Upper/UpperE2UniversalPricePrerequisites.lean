module

public import Erdos1017.Exclusions.E2.Upper.UpperE2UniversalPrerequisites

/-!
# Scalar prerequisites for the universal price

The shared hole inventory and bad-degree cap give the own-part denominator
bound, the two-endpoint deficit certificate gives a strict threshold gap and a
deficit coefficient strictly below one half, and the error polynomial and
common-mass resources pay the error cap below three fifths.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.UpperE2UniversalScalar

/-- The shared hole inventory and bad-degree cap give the original
own-part denominator bound before any deficit certificate is used. -/
theorem hole_inventory_denominator_bound {A b u z : ℝ}
    (hA : (1 / 3 : ℝ) ≤ A) (hb : b ≤ 1 - 2 * A) (hu : u ≤ 1 - 2 * A)
    (hz : z ≤ 1 - 3 * A + b)
    (hpack : z ^ 2 ≤ 3509 / 14884 - A ^ 2 - b ^ 2 -
      2 * b * (1 - A - b - u)) :
    18 * A - 22 * A ^ 2 - 3 - 3509 / 14884 + (2 - 8 * A) * u ≤
      2 * (2 - 4 * A - u) * (A - z) := by
  have hfirst : 0 ≤ b - (z + 3 * A - 1) := by linarith only [hz]
  have hsecond : 0 ≤ 2 * (1 - A - u) - b - (z + 3 * A - 1) := by
    linarith only [hA, hb, hu, hz]
  have hprod := mul_nonneg hfirst hsecond
  nlinarith only [hpack, hprod]

/-- The exact two-endpoint deficit certificate gives a strict original
threshold gap from the same hole inventory and partner-row resource. -/
theorem deficit_cap_lt_threshold {A b u z ell gamma : ℝ}
    (hA : A ∈ Icc (1 / 3 : ℝ) (93 / 250))
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11))
    (hgamma : (7 / 122 : ℝ) ≤ gamma)
    (hb : b ≤ 1 - 2 * A) (hu : u ≤ 1 - 2 * A)
    (hz : z ≤ 1 - 3 * A + b)
    (hresource : ell + gamma - (1 + ell) * A ≤ 2 * ell * u)
    (hpack : z ^ 2 ≤ 3509 / 14884 - A ^ 2 - b ^ 2 -
      2 * b * (1 - A - b - u)) :
    (1 - ell) * (1 - u) - 2 * gamma <
      (3 * gamma / A - (1 - ell)) * (A - z) := by
  have hA0 : 0 < A := by linarith only [hA.1]
  have hell0 : 0 < 2 * ell := by linarith only [hell.1]
  have hlow : dhRp A ell / (2 * ell) ≤ u := by
    apply (div_le_iff₀ hell0).mpr
    dsimp only [dhRp]
    linarith only [hresource, hgamma]
  have hQ := dh_quadratic_pos hA hell ⟨hlow, hu⟩
  have hden : 0 < 2 * (2 - 4 * A - u) := by linarith only [hu, hA.2]
  have hk : 0 ≤ A - z := by linarith only [hz, hb, hA.1]
  have hdelta : 0 ≤ 1 - ell := by linarith only [hell.2]
  have hdeltaA := mul_le_mul_of_nonneg_right hA.2 hdelta
  have hdeltamax := mul_le_mul_of_nonneg_left
    (show 1 - ell ≤ 1 / 5 by linarith only [hell.1])
    (by norm_num : (0 : ℝ) ≤ 93 / 250)
  have htheta : 0 < 3 * (7 / 122 : ℝ) - A * (1 - ell) := by
    nlinarith only [hdeltaA, hdeltamax]
  have hpacking := hole_inventory_denominator_bound hA.1 hb hu hz hpack
  have hscaled := mul_nonneg htheta.le (sub_nonneg.mpr hpacking)
  have hid : 2 * (2 - 4 * A - u) *
      ((3 * (7 / 122) - A * (1 - ell)) * (A - z) -
        A * ((1 - ell) * (1 - u) - 2 * (7 / 122))) =
      dhQuadratic A ell u + (3 * (7 / 122) - A * (1 - ell)) *
        (2 * (2 - 4 * A - u) * (A - z) -
          (18 * A - 22 * A ^ 2 - 3 - 3509 / 14884 + (2 - 8 * A) * u)) := by
    dsimp only [dhQuadratic, dhG0, dhG1, dhG2]
    ring
  have hbase : 0 < (3 * (7 / 122) - A * (1 - ell)) * (A - z) -
      A * ((1 - ell) * (1 - u) - 2 * (7 / 122)) := by
    apply (mul_pos_iff_of_pos_left hden).mp
    rw [hid]
    exact add_pos_of_pos_of_nonneg hQ hscaled
  have hincrease := mul_nonneg (sub_nonneg.mpr hgamma)
    (show 0 ≤ 3 * (A - z) + 2 * A by linarith only [hk, hA0])
  have hthetaeq : A * (3 * gamma / A - (1 - ell)) =
      3 * gamma - A * (1 - ell) := by
    field_simp [hA0.ne']
  have hfinal : 0 < A * ((3 * gamma / A - (1 - ell)) * (A - z) -
      ((1 - ell) * (1 - u) - 2 * gamma)) := by
    have h := congrArg (fun t : ℝ => t * (A - z)) hthetaeq
    nlinarith only [hbase, hincrease, h]
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hA0).mp hfinal)

/-- A deficit below the paid threshold gives a coefficient strictly
below one half, including the zero-deficit boundary. -/
theorem deficit_ratio_lt_half {theta k DH : ℝ}
    (htheta : theta ∈ Ico (0 : ℝ) (1 / 2)) (hk : 0 < k)
    (hDH : 0 ≤ DH) (hgap : DH < theta * k) :
    0 < k * (1 - theta) - DH ∧
      0 ≤ DH * (1 - 2 * theta) / (k * (1 - theta) - DH) ∧
      DH * (1 - 2 * theta) / (k * (1 - theta) - DH) < 1 / 2 := by
  have hhalf : 0 < 1 - 2 * theta := by linarith only [htheta.2]
  have hprod := mul_pos hk hhalf
  have hden : 0 < k * (1 - theta) - DH := by nlinarith only [hgap, hprod]
  refine ⟨hden, div_nonneg (mul_nonneg hDH hhalf.le) hden.le, ?_⟩
  have hscaled := mul_pos (sub_pos.mpr hgap)
    (show 0 < 1 - theta by linarith only [htheta.2])
  have hratio : DH * (1 - 2 * theta) / (k * (1 - theta) - DH) < theta := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith only [hscaled]
  exact hratio.trans htheta.2

/-- The exact zero-price polynomial pays the full strict numerator
margin on both positive-factor branches and their zero boundaries. -/
theorem zero_price_numerator_margin {A ell gamma u R : ℝ}
    (hA : A ∈ Icc (1 / 3 : ℝ) (93 / 250))
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11))
    (hgamma : gammaFloor ell ≤ gamma) (hR0 : 0 ≤ R)
    (hresource : ell + gamma - (1 + ell) * A ≤ 2 * ell * u)
    (hR : R ≤ (1 - u - 2 * ell * A - 3 * gamma) / ell) :
    1 / 200 < gamma - max (1 - 2 * (3 * gamma / A - (1 - ell))) 0 * R := by
  let theta := 3 * gamma / A - (1 - ell)
  let T := (3 - 2 * ell) * A - 6 * gamma
  let B := ell + A * (1 + ell - 4 * ell ^ 2) - gamma * (1 + 6 * ell)
  let T0 := (3 - 2 * ell) * A - 6 * gammaFloor ell
  let B0 := ell + A * (1 + ell - 4 * ell ^ 2) - gammaFloor ell * (1 + 6 * ell)
  have hA0 : 0 < A := by linarith only [hA.1]
  have hell0 : 0 < ell := by linarith only [hell.1]
  have hfloor : (7 / 122 : ℝ) ≤ gammaFloor ell := by
    dsimp only [gammaFloor]
    linarith only [hell.2]
  have hcoeff : A * (1 - 2 * theta) = T := by
    dsimp only [theta, T]
    field_simp [hA0.ne']
    ring
  by_cases hpositive : 0 < 1 - 2 * theta
  · have hT : 0 < T := hcoeff ▸ mul_pos hA0 hpositive
    have hrow := (le_div_iff₀ hell0).mp hR
    have hrowscaled := mul_le_mul_of_nonneg_left hrow (show 0 ≤ 2 * ell by positivity)
    have hB : 2 * ell ^ 2 * R ≤ B := by
      dsimp only [B]
      nlinarith only [hrowscaled, hresource]
    have hB0 : 0 ≤ B := (mul_nonneg (by positivity) hR0).trans hB
    have hTle : T ≤ T0 := by dsimp only [T, T0]; linarith only [hgamma]
    have hBle : B ≤ B0 := by
      have h := mul_nonneg (sub_nonneg.mpr hgamma)
        (show 0 ≤ 1 + 6 * ell by linarith only [hell0])
      dsimp only [B, B0]
      nlinarith only [h]
    have hmono := mul_le_mul hTle hBle hB0 (hT.le.trans hTle)
    have hpaid := (mul_le_mul_of_nonneg_left hB hT.le).trans hmono
    have hcoeffR := congrArg (fun x : ℝ => x * (2 * ell ^ 2 * R)) hcoeff
    have hpoly := zero_price_margin hA hell
    change (1 / 200 : ℝ) * 2 * ell ^ 2 * A <
      2 * ell ^ 2 * A * gammaFloor ell - T0 * B0 at hpoly
    have hden : 0 < 2 * ell ^ 2 * A := by positivity
    have hincrease := mul_nonneg hden.le (sub_nonneg.mpr hgamma)
    have hpaid' : 0 < (2 * ell ^ 2 * A) * (gamma - (1 - 2 * theta) * R - 1 / 200) := by
      nlinarith only [hpoly, hpaid, hcoeffR, hincrease]
    have hresult := (mul_pos_iff_of_pos_left hden).mp hpaid'
    change 1 / 200 < gamma - max (1 - 2 * theta) 0 * R
    rw [max_eq_left hpositive.le]
    linarith only [hresult]
  · change 1 / 200 < gamma - max (1 - 2 * theta) 0 * R
    rw [max_eq_right (le_of_not_gt hpositive), zero_mul, sub_zero]
    linarith only [hgamma, hfloor]

/-- The correlated intercept floor keeps both positive row resources
strictly positive on the full closed upper-E2 parameter box. -/
theorem error_resources_pos {A ell : ℝ}
    (hA : A ∈ Icc (1 / 3 : ℝ) (93 / 250))
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11)) :
    0 < errorRp A ell ∧ 0 < errorRr A ell := by
  have hA0 : 0 ≤ A := by linarith only [hA.1]
  have hfloor : (7 / 122 : ℝ) ≤ gammaFloor ell := by
    dsimp only [gammaFloor]
    linarith only [hell.2]
  constructor
  · have hprod := mul_nonneg (sub_nonneg.mpr hell.1)
      (show 0 ≤ 1 - A by linarith only [hA.2])
    dsimp only [errorRp]
    nlinarith only [hprod, hfloor, hA.2]
  · have hprod := mul_nonneg (show 0 ≤ 2 * ell - 1 by linarith only [hell.1]) hA0
    dsimp only [errorRr]
    linarith only [hprod, hfloor]

/-- The exact error polynomial pays the original rational error cap.
Every decreasing numerator and increasing denominator retains its sign. -/
theorem error_ratio_lt_three_fifths {A ell gamma : ℝ}
    (hA : A ∈ Icc (1 / 3 : ℝ) (93 / 250))
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11))
    (hgamma : gammaFloor ell ≤ gamma)
    (hT : 0 < A - 3 * gamma)
    (hD : 0 < 2 * ell * (1 - 2 * A) - (ell + gamma - (1 + ell) * A)) :
    (A - 3 * gamma) *
        (2 * ell * (1 - 2 * A) - (ell + gamma - (1 + ell) * A)) ^ 2 /
      (4 * (ell + gamma - (1 + ell) * A) * ((2 * ell - 1) * A + 3 * gamma)) <
        3 * gamma / 5 := by
  let g0 := gammaFloor ell
  let rp0 := errorRp A ell
  let rr0 := errorRr A ell
  let d0 := errorDd A ell
  let t0 := A - 3 * g0
  let RP := ell + gamma - (1 + ell) * A
  let R := (2 * ell - 1) * A + 3 * gamma
  let D := 2 * ell * (1 - 2 * A) - RP
  let T := A - 3 * gamma
  obtain ⟨hrp0, hrr0⟩ := error_resources_pos hA hell
  change 0 < rp0 at hrp0
  change 0 < rr0 at hrr0
  have hfloor : 0 < g0 := by
    dsimp only [g0, gammaFloor]
    linarith only [hell.2]
  have hRP : rp0 ≤ RP := by
    dsimp only [rp0, errorRp, RP]
    linarith only [hgamma]
  have hR : rr0 ≤ R := by
    dsimp only [rr0, errorRr, R]
    linarith only [hgamma]
  have hDle : D ≤ d0 := by
    dsimp only [D, d0, errorDd, RP, errorRp]
    linarith only [hgamma]
  have hTle : T ≤ t0 := by
    dsimp only [T, t0, g0]
    linarith only [hgamma]
  have hD0 : 0 ≤ D := hD.le
  have hdsq : D ^ 2 ≤ d0 ^ 2 := pow_le_pow_left₀ hD0 hDle 2
  have ht0 : 0 ≤ t0 := hT.le.trans hTle
  have hnum := mul_le_mul hTle hdsq (sq_nonneg D) ht0
  have hden := mul_le_mul hRP hR hrr0.le (hrp0.le.trans hRP)
  have hden0 : 0 < 4 * RP * R :=
    mul_pos (mul_pos (by norm_num) (hrp0.trans_le hRP)) (hrr0.trans_le hR)
  have hmono := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ (12 / 5 : ℝ) * g0 by positivity)
  have hgmono := mul_nonneg (sub_nonneg.mpr hgamma)
    (mul_nonneg (hrp0.le.trans hRP) (hrr0.le.trans hR))
  have hpoly := error_polynomial_pos hA hell
  change 0 < (12 / 5 : ℝ) * g0 * rp0 * rr0 - t0 * d0 ^ 2 at hpoly
  have hpaid : T * D ^ 2 < (12 / 5 : ℝ) * gamma * RP * R := by
    nlinarith only [hnum, hmono, hgmono, hpoly]
  change T * D ^ 2 / (4 * RP * R) < 3 * gamma / 5
  apply (div_lt_iff₀ hden0).mpr
  nlinarith only [hpaid]

/-- One common mass variable pays both terms of the elementary error
resource bound; no independent numerator mass replaces it. -/
theorem common_error_resource_bound {r0 u ell RP : ℝ}
    (hu : 0 < u) (hRP : 0 < RP) (hcap : u ≤ r0) :
    (r0 - u) * (2 * ell - RP / u) ≤ (2 * ell * r0 - RP) ^ 2 / (4 * RP) := by
  have hrewrite : (r0 - u) * (2 * ell - RP / u) =
      ((r0 - u) * (2 * ell * u - RP)) / u := by
    field_simp [hu.ne']
  rw [hrewrite]
  apply (div_le_div_iff₀ hu (show 0 < 4 * RP by positivity)).mpr
  have hnonneg := add_nonneg
    (mul_nonneg hu.le (sq_nonneg (2 * ell * (r0 - u) - (2 * ell * u - RP))))
    (mul_nonneg (show 0 ≤ 4 * (r0 - u) by linarith only [hcap])
      (sq_nonneg (2 * ell * u - RP)))
  nlinarith only [hnonneg]

/-- The actual common-mass and source-margin resources give the strict
error payment with the same good-region mass throughout. -/
theorem error_cap_lt_three_fifths {A ell gamma u kappa g : ℝ}
    (hA : A ∈ Icc (1 / 3 : ℝ) (93 / 250))
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11))
    (hgamma : gammaFloor ell ≤ gamma) (hkappa : 0 ≤ kappa)
    (hmargin : u + kappa < 1 - 2 * A)
    (hresource : ell + gamma - (1 + ell) * A ≤ 2 * ell * u)
    (hgood : (ell + (3 * gamma / A - (1 - ell))) * g ≤
      2 * ell * u - (ell + gamma - (1 + ell) * A)) :
    kappa * max (ell - (3 * gamma / A - (1 - ell))) 0 * g / u <
      3 * gamma / 5 := by
  let theta := 3 * gamma / A - (1 - ell)
  let RP := ell + gamma - (1 + ell) * A
  let R := (2 * ell - 1) * A + 3 * gamma
  let T := A - 3 * gamma
  let r0 := 1 - 2 * A
  have hA0 : 0 < A := by linarith only [hA.1]
  have hell0 : 0 < ell := by linarith only [hell.1]
  have hgammapos : 0 < gamma := by
    have hfloor : (7 / 122 : ℝ) ≤ gammaFloor ell := by
      dsimp only [gammaFloor]
      linarith only [hell.2]
    linarith only [hgamma, hfloor]
  obtain ⟨hrp0, hrr0⟩ := error_resources_pos hA hell
  have hRP : 0 < RP := by dsimp only [RP, errorRp] at *; linarith only [hrp0, hgamma]
  have hR : 0 < R := by dsimp only [R, errorRr] at *; linarith only [hrr0, hgamma]
  have hu : 0 < u := by
    have hprod : 0 < 2 * ell * u := hRP.trans_le hresource
    exact (mul_pos_iff_of_pos_left (show 0 < 2 * ell by positivity)).mp hprod
  have hucap : u < r0 := by dsimp only [r0]; linarith only [hmargin, hkappa]
  by_cases htau : 0 < ell - theta
  · have hTidentity : A * (ell - theta) = T := by
      dsimp only [theta, T]
      field_simp [hA0.ne']
      ring
    have hT : 0 < T := hTidentity ▸ mul_pos hA0 htau
    have hRidentity : A * (ell + theta) = R := by
      dsimp only [theta, R]
      field_simp [hA0.ne']
      ring
    have hgoodscaled := mul_le_mul_of_nonneg_left hgood hA0.le
    have hRscaled := congrArg (fun x : ℝ => x * g) hRidentity
    have hgood' : R * g ≤ A * (2 * ell * u - RP) := by
      dsimp only [theta, RP] at *
      nlinarith only [hgoodscaled, hRscaled]
    have hw : 0 ≤ 2 * ell * u - RP := sub_nonneg.mpr hresource
    have hscaled := mul_le_mul_of_nonneg_left hgood'
      (mul_nonneg hkappa htau.le)
    have hTscaled := congrArg (fun x : ℝ => kappa * x * (2 * ell * u - RP)) hTidentity
    have hkpaid := mul_nonneg (show 0 ≤ r0 - u - kappa by
      dsimp only [r0]; linarith only [hmargin]) (mul_nonneg hT.le hw)
    have hrow : kappa * (ell - theta) * g * R ≤ T * (r0 - u) * (2 * ell * u - RP) := by
      nlinarith only [hscaled, hTscaled, hkpaid]
    have hratio : kappa * (ell - theta) * g / u ≤
        (T / R) * ((r0 - u) * (2 * ell - RP / u)) := by
      have heq : (T / R) * ((r0 - u) * (2 * ell - RP / u)) =
          T * (r0 - u) * (2 * ell * u - RP) / (R * u) := by
        field_simp [hR.ne', hu.ne']
      rw [heq]
      apply (div_le_div_iff₀ hu (mul_pos hR hu)).mpr
      have h := mul_le_mul_of_nonneg_right hrow hu.le
      nlinarith only [h]
    have hbound := mul_le_mul_of_nonneg_left
      (common_error_resource_bound (ell := ell) hu hRP hucap.le)
      (div_nonneg hT.le hR.le)
    have hD : 0 < 2 * ell * r0 - RP := by
      have h := mul_pos (show 0 < 2 * ell by positivity) (sub_pos.mpr hucap)
      nlinarith only [h, hresource]
    have herror := error_ratio_lt_three_fifths hA hell hgamma hT hD
    change T * (2 * ell * r0 - RP) ^ 2 / (4 * RP * R) < 3 * gamma / 5 at herror
    have heq : (T / R) * ((2 * ell * r0 - RP) ^ 2 / (4 * RP)) =
        T * (2 * ell * r0 - RP) ^ 2 / (4 * RP * R) := by
      field_simp [hR.ne', hRP.ne']
    change kappa * max (ell - theta) 0 * g / u < 3 * gamma / 5
    rw [max_eq_left htau.le]
    exact (hratio.trans (by simpa only [heq] using hbound)).trans_lt herror
  · change kappa * max (ell - theta) 0 * g / u < 3 * gamma / 5
    rw [max_eq_right (le_of_not_gt htau), mul_zero, zero_mul, zero_div]
    positivity

/-- The strict error-bearing denominator pays the same total good-region
mass in the numerator and common-region denominator. -/
theorem good_error_ratio_le {c w gL gH tau e den : ℝ}
    (hc : 0 < c) (hw : 0 ≤ w) (hgL : 0 ≤ gL) (hgH : 0 ≤ gH)
    (htau : 0 ≤ tau) (he : 0 ≤ e) (hecap : e ≤ tau * gL)
    (hu : 0 < w + gL + gH)
    (hden : 0 < e → c + w + gL ≤ den) :
    e / den ≤ tau * (gL + gH) / (w + gL + gH) := by
  by_cases hepos : 0 < e
  · have hdenlower := hden hepos
    have hden0 : 0 < den := by linarith only [hdenlower, hc, hw, hgL]
    apply (div_le_div_iff₀ hden0 hu).mpr
    have hmass : gL * (w + gL + gH) ≤ (gL + gH) * (c + w + gL) := by
      have h1 := mul_nonneg hc.le (add_nonneg hgL hgH)
      have h2 := mul_nonneg hw hgH
      nlinarith only [h1, h2]
    have hfirst := mul_le_mul_of_nonneg_right hecap hu.le
    have hsecond := mul_le_mul_of_nonneg_left hmass htau
    have hthird := mul_le_mul_of_nonneg_left hdenlower
      (mul_nonneg htau (add_nonneg hgL hgH))
    nlinarith only [hfirst, hsecond, hthird]
  · have hezero : e = 0 := le_antisymm (le_of_not_gt hepos) he
    rw [hezero, zero_div]
    exact div_nonneg (mul_nonneg htau (add_nonneg hgL hgH)) hu.le

end Erdos1017.UpperE2UniversalScalar
