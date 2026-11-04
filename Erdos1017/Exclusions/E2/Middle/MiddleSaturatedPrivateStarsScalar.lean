module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates
public import Erdos1017.Exclusions.Common.E2.E2PrivateCurvatureCertificates
public import Erdos1017.Exclusions.E2.Middle.MiddleSaturatedPrivateStarsAlgebra
public import Erdos1017.Exclusions.E2.Middle.MiddleSaturatedPrivateStarsCoupling
public import Mathlib.Tactic.Linarith

/-!
# Scalar contradiction for the saturated private star

With the sharp middle selector value `selectorValue` at peak mass `A` and
multiplier `ell` and the surplus cap from the saturated order-two pair, the
coupled middle saturated private star contradicts the failed insertion
(`nonpositive_star_impossible`).
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.MiddleSaturatedPrivateStarsScalar

open LowerE2Scalar
open MiddleSaturatedPrivateStarsAlgebra

/-- The sharp middle selector value at peak mass `A` and multiplier `ell`. -/
def selectorValue (A ell : ℝ) : ℝ :=
  (-1 + 8 * A - (7 + 6 * ell) * A ^ 2) / 6

private theorem selectorValue_antitone_multiplier {A ell₀ ell : ℝ}
    (hell : ell₀ ≤ ell) : selectorValue A ell ≤ selectorValue A ell₀ := by
  unfold selectorValue
  nlinarith only [mul_nonneg (sub_nonneg.mpr hell) (sq_nonneg A)]

private theorem selectorValue_le_upper {A ell hi : ℝ}
    (hA : A ≤ hi) (hc : 0 ≤ 7 + 6 * ell)
    (hvertex : (7 + 6 * ell) * (2 * hi) ≤ 8) :
    selectorValue A ell ≤ selectorValue hi ell := by
  have hbracket : 0 ≤ 8 - (7 + 6 * ell) * (hi + A) := by
    nlinarith only [hvertex, mul_nonneg hc (sub_nonneg.mpr hA)]
  have hprod := mul_nonneg (sub_nonneg.mpr hA) hbracket
  unfold selectorValue
  nlinarith only [hprod]

private theorem selectorValue_le_vertex {A ell : ℝ}
    (hc : 0 < 7 + 6 * ell) :
    selectorValue A ell ≤ (16 / (7 + 6 * ell) - 1) / 6 := by
  have hsq := mul_nonneg hc.le (sq_nonneg (A - 4 / (7 + 6 * ell)))
  have hmain : 8 * A - (7 + 6 * ell) * A ^ 2 ≤ 16 / (7 + 6 * ell) := by
    apply (le_div_iff₀ hc).mpr
    field_simp at hsq
    nlinarith only [hsq]
  unfold selectorValue
  linarith only [hmain]

/-- The surplus upper bound from the same saturated order-two pair. -/
def surplusCap (q u v : ℝ) : ℝ := 2 * (u * v - pairFloor q) / 3

private theorem multiplier_antitone {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) :
    multiplier r ≤ multiplier q := by
  have hdq : 0 < 2 + q := by linarith only [hq]
  have hdr : 0 < 2 + r := by linarith only [hq, hqr]
  unfold multiplier
  rw [div_le_div_iff₀ hdr hdq]
  nlinarith only [hqr]

private theorem gapFloor_monotone {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) :
    gapFloor q ≤ gapFloor r := by
  have hr : 0 ≤ r := hq.trans hqr
  have hdq := denominator_pos hq
  have hdr := denominator_pos hr
  have hfactor : 0 ≤ (r - q) * (1 + 2 * (r + q) + 13 * r * q) :=
    mul_nonneg (sub_nonneg.mpr hqr) (by positivity)
  unfold gapFloor
  rw [div_le_div_iff₀ (by positivity : 0 < 2 * denominator q)
    (by positivity : 0 < 2 * denominator r)]
  unfold denominator at *
  nlinarith only [hfactor]

private def pairFloorDifferenceFactor (q r : ℝ) : ℝ :=
  72 + 243 * q + 9 * q ^ 3 +
    r * (243 - 270 * q - 999 * q ^ 2 + 54 * q ^ 3) +
    r ^ 2 * (-999 * q - 3348 * q ^ 2 + 216 * q ^ 3) +
    r ^ 3 * (9 + 54 * q + 216 * q ^ 2 + 126 * q ^ 3)

private theorem pairFloorDifferenceFactor_pos {q r : ℝ}
    (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ 1 / 5) :
    0 < pairFloorDifferenceFactor q r := by
  have hr0 : 0 ≤ r := hq.trans hqr
  have hqhi : q ≤ 1 / 5 := hqr.trans hr
  have hq2 : q ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ hq hqhi 2
  have hr2 : r ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ hr0 hr 2
  have hqr1 : q * r ≤ (1 / 5 : ℝ) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hqhi hr0
    have h2 := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 1 / 5)
    nlinarith only [h1, h2]
  have hqr2 : q ^ 2 * r ≤ (1 / 5 : ℝ) ^ 3 := by
    have h1 := mul_le_mul_of_nonneg_right hq2 hr0
    have h2 := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ (1 / 5) ^ 2)
    nlinarith only [h1, h2]
  have hqr3 : q * r ^ 2 ≤ (1 / 5 : ℝ) ^ 3 := by
    have h1 := mul_le_mul_of_nonneg_right hqhi (sq_nonneg r)
    have h2 := mul_le_mul_of_nonneg_left hr2 (by norm_num : (0 : ℝ) ≤ 1 / 5)
    nlinarith only [h1, h2]
  have hqr4 : q ^ 2 * r ^ 2 ≤ (1 / 5 : ℝ) ^ 4 := by
    have h1 := mul_le_mul_of_nonneg_right hq2 (sq_nonneg r)
    have h2 := mul_le_mul_of_nonneg_left hr2 (by norm_num : (0 : ℝ) ≤ (1 / 5) ^ 2)
    nlinarith only [h1, h2]
  unfold pairFloorDifferenceFactor
  nlinarith only [hqr1, hqr2, hqr3, hqr4, hq, hr0,
    mul_nonneg hr0 (by positivity : 0 ≤ 243 + 54 * q ^ 3),
    mul_nonneg (sq_nonneg r) (by positivity : 0 ≤ 216 * q ^ 3),
    mul_nonneg (pow_nonneg hr0 3) (by positivity : 0 ≤ 9 + 54 * q +
      216 * q ^ 2 + 126 * q ^ 3)]

private theorem pairFloor_antitone {q r : ℝ}
    (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ 1 / 5) :
    pairFloor r ≤ pairFloor q := by
  have hr0 : 0 ≤ r := hq.trans hqr
  have hdq := denominator_pos hq
  have hdr := denominator_pos hr0
  have hfactor := mul_nonneg (sub_nonneg.mpr hqr)
    (pairFloorDifferenceFactor_pos hq hqr hr).le
  have hid : pairNumerator q * denominator r ^ 2 -
      pairNumerator r * denominator q ^ 2 =
        (r - q) * pairFloorDifferenceFactor q r := by
    unfold pairNumerator denominator pairFloorDifferenceFactor
    ring
  unfold pairFloor
  rw [div_le_div_iff₀ (by positivity : 0 < 16 * denominator r ^ 2)
    (by positivity : 0 < 16 * denominator q ^ 2)]
  nlinarith only [hfactor, hid]

private theorem box_parameter_bounds {q qlo qhi : ℝ}
    (hqlo : 0 ≤ qlo) (hqhi : qhi ≤ 1 / 5)
    (hq : q ∈ Icc qlo qhi) :
    multiplier qhi ≤ multiplier q ∧
      multiplier q ≤ multiplier qlo ∧
      gapFloor qlo ≤ gapFloor q ∧
      pairFloor qhi ≤ pairFloor q := by
  have hq0 : 0 ≤ q := hqlo.trans hq.1
  exact ⟨multiplier_antitone hq0 hq.2,
    multiplier_antitone hqlo hq.1,
    gapFloor_monotone hqlo hq.1,
    pairFloor_antitone hq0 hq.2 hqhi⟩

private theorem box_selector_residual_lt {q qlo qhi A gamma Dstar : ℝ}
    (hqlo : 0 ≤ qlo) (hqhi : qhi ≤ 1 / 5)
    (hq : q ∈ Icc qlo qhi)
    (hD : selectorValue A (multiplier qhi) ≤ Dstar)
    (hgamma : gapFloor q < gamma) :
    selectorValue A (multiplier q) - gamma < Dstar - gapFloor qlo := by
  have hp := box_parameter_bounds hqlo hqhi hq
  have hmono := selectorValue_antitone_multiplier (A := A) hp.1
  linarith only [hmono, hD, hp.2.2.1, hgamma]

private theorem selector_leaf_impossible {q qlo qhi A gamma tau Dstar : ℝ}
    (hqlo : 0 ≤ qlo) (hqhi : qhi ≤ 1 / 5) (hq : q ∈ Icc qlo qhi)
    (hD : selectorValue A (multiplier qhi) ≤ Dstar)
    (hgamma : gapFloor q < gamma) (htau : 0 < tau)
    (hcap : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma)
    (hell : 2 / 3 < multiplier qhi) (hnum : Dstar ≤ gapFloor qlo) : False := by
  have hres := box_selector_residual_lt hqlo hqhi hq hD hgamma
  have hparam := box_parameter_bounds hqlo hqhi hq
  have hpos : 0 < (multiplier q - 2 / 3) * tau ^ 2 :=
    mul_pos (by linarith only [hell, hparam.1]) (pow_pos htau 2)
  linarith only [hcap, hres, hpos, hnum]

private theorem head_square_leaf_impossible
    {q qlo qhi A gamma u v Dstar : ℝ}
    (hqlo : 0 ≤ qlo) (hqhi : qhi ≤ 1 / 5) (hq : q ∈ Icc qlo qhi)
    (hD : selectorValue A (multiplier qhi) ≤ Dstar)
    (hgamma : gapFloor q < gamma)
    (hhead : (multiplier q - 2 / 3) * (u ^ 2 + v ^ 2) ≤
      selectorValue A (multiplier q) - gamma)
    (hproduct : pairFloor q < u * v)
    (hell : 2 / 3 < multiplier qhi)
    (hnum : Dstar - gapFloor qlo ≤
      2 * pairFloor qhi * (multiplier qhi - 2 / 3)) : False := by
  have hres := box_selector_residual_lt hqlo hqhi hq hD hgamma
  obtain ⟨hellq, _, _, hpair⟩ := box_parameter_bounds hqlo hqhi hq
  have hcoef : 0 ≤ multiplier qhi - 2 / 3 := by linarith only [hell]
  have hsq : 2 * u * v ≤ u ^ 2 + v ^ 2 := by nlinarith only [sq_nonneg (u - v)]
  have hsum : 0 ≤ u ^ 2 + v ^ 2 := add_nonneg (sq_nonneg u) (sq_nonneg v)
  have hfirst := mul_le_mul_of_nonneg_left hsq hcoef
  have hsecond := mul_le_mul_of_nonneg_right
    (show multiplier qhi - 2 / 3 ≤ multiplier q - 2 / 3 by linarith only [hellq]) hsum
  have hthird : 2 * pairFloor qhi * (multiplier qhi - 2 / 3) <
      2 * u * v * (multiplier qhi - 2 / 3) := by
    have hp : pairFloor qhi < u * v := lt_of_le_of_lt hpair hproduct
    nlinarith only [mul_pos (sub_pos.mpr hp) (sub_pos.mpr hell)]
  linarith only [hres, hhead, hfirst, hsecond, hthird, hnum]

private theorem affine_pos_of_endpoints (C B lo hi x : ℝ)
    (hx : x ∈ Icc lo hi) (hlo : 0 < C + B * lo)
    (hhi : 0 < C + B * hi) : 0 < C + B * x := by
  by_cases heq : lo = hi
  · have hxeq : x = lo := le_antisymm (heq ▸ hx.2) hx.1
    simpa only [hxeq] using hlo
  have hgap : 0 < hi - lo := sub_pos.mpr (lt_of_le_of_ne (hx.1.trans hx.2) heq)
  by_cases hxeq : x = lo
  · simpa only [hxeq] using hlo
  have hleft := mul_nonneg (sub_nonneg.mpr hx.2) hlo.le
  have hright := mul_pos (sub_pos.mpr (lt_of_le_of_ne hx.1 (Ne.symm hxeq))) hhi
  have hid : (hi - lo) * (C + B * x) =
      (hi - x) * (C + B * lo) + (x - lo) * (C + B * hi) := by ring
  have hpos : 0 < (hi - lo) * (C + B * x) := by
    rw [hid]
    linarith only [hleft, hright]
  exact (mul_pos_iff_of_pos_left hgap).mp hpos

private theorem concave_pos_of_endpoints (C B k lo hi x : ℝ)
    (hk : 0 ≤ k) (hx : x ∈ Icc lo hi)
    (hlo : 0 < C + B * lo - k * lo ^ 2)
    (hhi : 0 < C + B * hi - k * hi ^ 2) :
    0 < C + B * x - k * x ^ 2 := by
  by_cases heq : lo = hi
  · have hxeq : x = lo := le_antisymm (heq ▸ hx.2) hx.1
    simpa only [hxeq] using hlo
  have hgap : 0 < hi - lo := sub_pos.mpr (lt_of_le_of_ne (hx.1.trans hx.2) heq)
  by_cases hxeq : x = lo
  · simpa only [hxeq] using hlo
  have hleft := mul_nonneg (sub_nonneg.mpr hx.2) hlo.le
  have hright := mul_pos (sub_pos.mpr (lt_of_le_of_ne hx.1 (Ne.symm hxeq))) hhi
  have hcurve : 0 ≤ k * (x - lo) * (hi - x) * (hi - lo) :=
    mul_nonneg (mul_nonneg (mul_nonneg hk (sub_nonneg.mpr hx.1))
      (sub_nonneg.mpr hx.2)) hgap.le
  have hid : (hi - lo) * (C + B * x - k * x ^ 2) =
      (hi - x) * (C + B * lo - k * lo ^ 2) +
        (x - lo) * (C + B * hi - k * hi ^ 2) +
          k * (x - lo) * (hi - x) * (hi - lo) := by ring
  have hpos : 0 < (hi - lo) * (C + B * x - k * x ^ 2) := by
    rw [hid]
    linarith only [hleft, hright, hcurve]
  exact (mul_pos_iff_of_pos_left hgap).mp hpos

private def cornerTests (A ell g T u L : ℝ) : Prop :=
  0 < firstMargin A ell g T u L ∧
    0 < secondMargin A ell g 0 u L ∧
    0 < secondMargin A ell g T u L ∧
    0 < thirdMargin A ell g 0 u L ∧
    0 < fourthMargin A ell g 0 u L ∧
    0 < fourthMargin A ell g T u L ∧
    0 < fifthMargin A ell g 0 u L

private theorem cornerTests_between_multiplier {A lo hi ell g T u L : ℝ}
    (hell : ell ∈ Icc lo hi) (hlo : cornerTests A lo g T u L)
    (hhi : cornerTests A hi g T u L) : cornerTests A ell g T u L := by
  rcases hlo with ⟨hlo1, hlo20, hlo2T, hlo3, hlo40, hlo4T, hlo5⟩
  rcases hhi with ⟨hhi1, _, hhi2T, hhi3, hhi40, hhi4T, hhi5⟩
  have h1 : 0 < firstMargin A ell g T u L := by
    have h := affine_pos_of_endpoints (A * (g - T + u) - L) (A * T)
      lo hi ell hell (by dsimp [firstMargin] at hlo1; nlinarith only [hlo1])
      (by dsimp [firstMargin] at hhi1; nlinarith only [hhi1])
    dsimp [firstMargin]
    nlinarith only [h]
  have h2T : 0 < secondMargin A ell g T u L := by
    have h := affine_pos_of_endpoints ((A - T + u) * g - L)
      ((A - T + u) * T) lo hi ell hell
      (by dsimp [secondMargin] at hlo2T; nlinarith only [hlo2T])
      (by dsimp [secondMargin] at hhi2T; nlinarith only [hhi2T])
    dsimp [secondMargin]
    nlinarith only [h]
  have h3 : 0 < thirdMargin A ell g 0 u L := by
    have h := affine_pos_of_endpoints (A * g - L)
      (A / 2 * (3 * A + 3 * u - 1) + L / 2) lo hi ell hell
      (by dsimp [thirdMargin] at hlo3; nlinarith only [hlo3])
      (by dsimp [thirdMargin] at hhi3; nlinarith only [hhi3])
    dsimp [thirdMargin]
    nlinarith only [h]
  have h40 : 0 < fourthMargin A ell g 0 u L := by
    have h := affine_pos_of_endpoints ((A + u) * g - L)
      (A / 2 * (3 * A + u - 1) + L / 2) lo hi ell hell
      (by dsimp [fourthMargin] at hlo40; nlinarith only [hlo40])
      (by dsimp [fourthMargin] at hhi40; nlinarith only [hhi40])
    dsimp [fourthMargin]
    nlinarith only [h]
  have h4T : 0 < fourthMargin A ell g T u L := by
    have h := affine_pos_of_endpoints ((A - T + u) * g - L)
      ((A - T + u) * T + A / 2 * (3 * A + u - 1) + L / 2)
      lo hi ell hell
      (by dsimp [fourthMargin] at hlo4T; nlinarith only [hlo4T])
      (by dsimp [fourthMargin] at hhi4T; nlinarith only [hhi4T])
    dsimp [fourthMargin]
    nlinarith only [h]
  have h5 : 0 < fifthMargin A ell g 0 u L := by
    have h := affine_pos_of_endpoints (A * g - L) (A * u)
      lo hi ell hell (by dsimp [fifthMargin] at hlo5; nlinarith only [hlo5])
      (by dsimp [fifthMargin] at hhi5; nlinarith only [hhi5])
    dsimp [fifthMargin]
    nlinarith only [h]
  have h20 : 0 < secondMargin A ell g 0 u L := by
    simpa only [secondMargin, mul_zero, add_zero, sub_zero] using hlo20
  exact ⟨h1, h20, h2T, h3, h40, h4T, h5⟩

private theorem cornerTests_mono_gap {A ell g₀ g T u L : ℝ}
    (hA : 0 < A) (hu : 0 ≤ u) (hbase : 0 < A - T + u)
    (hg : g₀ ≤ g) (hcorner : cornerTests A ell g₀ T u L) :
    cornerTests A ell g T u L := by
  rcases hcorner with ⟨h1, h20, h2T, h3, h40, h4T, h5⟩
  have hpayA := mul_nonneg hA.le (sub_nonneg.mpr hg)
  have hpay0 := mul_nonneg (by linarith only [hA, hu] : 0 ≤ A + u)
    (sub_nonneg.mpr hg)
  have hpayT := mul_nonneg hbase.le (sub_nonneg.mpr hg)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold firstMargin at *
    nlinarith only [h1, hpayA]
  · unfold secondMargin at *
    nlinarith only [h20, hpay0]
  · unfold secondMargin at *
    nlinarith only [h2T, hpayT]
  · unfold thirdMargin at *
    nlinarith only [h3, hpayA]
  · unfold fourthMargin at *
    nlinarith only [h40, hpay0]
  · unfold fourthMargin at *
    nlinarith only [h4T, hpayT]
  · unfold fifthMargin at *
    nlinarith only [h5, hpayA]

private theorem cornerTests_mono_peak {A₀ A ell g T u L : ℝ}
    (hA₀ : 1 / 4 ≤ A₀) (hA : A₀ ≤ A)
    (hell : 0 < ell) (hg : 0 < g) (hT : 0 ≤ T)
    (hu : 0 ≤ u) (hL : 0 ≤ L)
    (hcorner : cornerTests A₀ ell g T u L) :
    cornerTests A ell g T u L := by
  rcases hcorner with ⟨h1, h20, h2T, h3, h40, h4T, h5⟩
  have hAdiff : 0 ≤ A - A₀ := sub_nonneg.mpr hA
  have hA₀pos : 0 < A₀ := by linarith only [hA₀]
  have hgeom3 : 0 ≤ 3 * (A + A₀) + 3 * u - 1 := by
    linarith only [hA₀, hA, hu]
  have hgeom4 : 0 ≤ 3 * (A + A₀) + u - 1 := by
    linarith only [hA₀, hA, hu]
  have hbracket1 : 0 < g - (1 - ell) * T + u := by
    unfold firstMargin at h1
    nlinarith only [h1, hL, hA₀pos]
  have hpay1 := mul_nonneg hAdiff hbracket1.le
  have hpay20 := mul_nonneg hAdiff hg.le
  have hpay2T := mul_nonneg hAdiff (by positivity : 0 ≤ g + ell * T)
  have hpay3 : 0 ≤ (A - A₀) *
      (g + ell / 2 * (3 * (A + A₀) + 3 * u - 1)) := mul_nonneg hAdiff (by
    have h := mul_nonneg hell.le hgeom3
    linarith only [hg, h])
  have hpay40 : 0 ≤ (A - A₀) *
      (g + ell / 2 * (3 * (A + A₀) + u - 1)) := mul_nonneg hAdiff (by
    have h := mul_nonneg hell.le hgeom4
    linarith only [hg, h])
  have hpay4T : 0 ≤ (A - A₀) *
      (g + ell * T + ell / 2 * (3 * (A + A₀) + u - 1)) := mul_nonneg hAdiff (by
    have h := mul_nonneg hell.le hgeom4
    have ht : 0 ≤ ell * T := by positivity
    linarith only [hg, h, ht])
  have hpay5 := mul_nonneg hAdiff (by positivity : 0 ≤ g + ell * u)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold firstMargin at *
    nlinarith only [h1, hpay1]
  · unfold secondMargin at *
    nlinarith only [h20, hpay20]
  · unfold secondMargin at *
    nlinarith only [h2T, hpay2T]
  · unfold thirdMargin at *
    nlinarith only [h3, hpay3, hgeom3]
  · unfold fourthMargin at *
    nlinarith only [h40, hpay40, hgeom4]
  · unfold fourthMargin at *
    nlinarith only [h4T, hpay4T, hgeom4]
  · unfold fifthMargin at *
    nlinarith only [h5, hpay5]

private theorem margins_pos_of_cornerTests {A ell g T tau u L : ℝ}
    (hA : 0 < A) (hell : ell ∈ Icc (1 / 2 : ℝ) 1)
    (htau : tau ∈ Icc (0 : ℝ) T)
    (hcorner : cornerTests A ell g T u L) :
    0 < firstMargin A ell g tau u L ∧
      0 < secondMargin A ell g tau u L ∧
      0 < thirdMargin A ell g tau u L ∧
      0 < fourthMargin A ell g tau u L ∧
      0 < fifthMargin A ell g tau u L := by
  rcases hcorner with ⟨h1, h20, h2T, h3, h40, h4T, h5⟩
  have hell0 : 0 ≤ ell := by linarith only [hell.1]
  have hfirst : 0 < firstMargin A ell g tau u L := by
    have hprod := mul_nonneg (mul_nonneg hA.le (sub_nonneg.mpr hell.2))
      (sub_nonneg.mpr htau.2)
    unfold firstMargin at *
    nlinarith only [h1, hprod]
  have hsecond : 0 < secondMargin A ell g tau u L := by
    have hlo : 0 < (A + u) * g - L + ((A + u) * ell - g) * 0 - ell * 0 ^ 2 := by
      unfold secondMargin at h20
      nlinarith only [h20]
    have hhi : 0 < (A + u) * g - L + ((A + u) * ell - g) * T - ell * T ^ 2 := by
      unfold secondMargin at h2T
      nlinarith only [h2T]
    have h := concave_pos_of_endpoints ((A + u) * g - L)
      ((A + u) * ell - g) ell 0 T tau hell0 htau hlo hhi
    unfold secondMargin
    nlinarith only [h]
  have hfourth : 0 < fourthMargin A ell g tau u L := by
    have hlo : 0 < (A + u) * g + ell * A / 2 * (3 * A + u - 1) -
        (1 - ell / 2) * L + ((A + u) * ell - g) * 0 - ell * 0 ^ 2 := by
      unfold fourthMargin at h40
      nlinarith only [h40]
    have hhi : 0 < (A + u) * g + ell * A / 2 * (3 * A + u - 1) -
        (1 - ell / 2) * L + ((A + u) * ell - g) * T - ell * T ^ 2 := by
      unfold fourthMargin at h4T
      nlinarith only [h4T]
    have h := concave_pos_of_endpoints
      ((A + u) * g + ell * A / 2 * (3 * A + u - 1) - (1 - ell / 2) * L)
      ((A + u) * ell - g) ell 0 T tau hell0 htau hlo hhi
    unfold fourthMargin
    nlinarith only [h]
  have hthird : 0 < thirdMargin A ell g tau u L := by
    simpa only [thirdMargin] using h3
  have hfifth : 0 < fifthMargin A ell g tau u L := by
    simpa only [fifthMargin] using h5
  exact ⟨hfirst, hsecond, hthird, hfourth, hfifth⟩

private theorem margins_pos_of_rational_corners
    {A₀ A ell₀ ell₁ ell g₀ g T tau u L : ℝ}
    (hA₀ : 1 / 4 ≤ A₀) (hA : A₀ ≤ A)
    (hell : ell ∈ Icc ell₀ ell₁)
    (hell₀ : 1 / 2 ≤ ell₀) (hell₁ : ell₁ ≤ 1)
    (hg₀ : 0 < g₀) (hg : g₀ ≤ g)
    (hT : 0 ≤ T) (htau : tau ∈ Icc (0 : ℝ) T)
    (hu : 0 ≤ u) (hL : 0 ≤ L)
    (hbase : 0 < A₀ - T + u)
    (hlo : cornerTests A₀ ell₀ g₀ T u L)
    (hhi : cornerTests A₀ ell₁ g₀ T u L) :
    0 < firstMargin A ell g tau u L ∧
      0 < secondMargin A ell g tau u L ∧
      0 < thirdMargin A ell g tau u L ∧
      0 < fourthMargin A ell g tau u L ∧
      0 < fifthMargin A ell g tau u L := by
  have hcorner₀ := cornerTests_between_multiplier hell hlo hhi
  have hcorner₁ := cornerTests_mono_gap (by linarith only [hA₀]) hu hbase hg hcorner₀
  have hcorner₂ := cornerTests_mono_peak hA₀ hA
    (by linarith only [hell₀, hell.1]) (lt_of_lt_of_le hg₀ hg) hT hu hL hcorner₁
  exact margins_pos_of_cornerTests (by linarith only [hA₀, hA])
    ⟨hell₀.trans hell.1, hell.2.trans hell₁⟩ htau hcorner₂

private theorem margins_mono_canonical {A ell g tau u₀ u L₀ L : ℝ}
    (hA : 0 < A) (hell : ell ∈ Icc (9 / 11 : ℝ) 1)
    (hg : 0 < g) (htau : 0 ≤ tau) (hu : u₀ ≤ u) (hL : L₀ ≤ L) :
    firstMargin A ell g tau u₀ L ≤ firstMargin A ell g tau u L₀ ∧
      secondMargin A ell g tau u₀ L ≤ secondMargin A ell g tau u L₀ ∧
      thirdMargin A ell g tau u₀ L ≤ thirdMargin A ell g tau u L₀ ∧
      fourthMargin A ell g tau u₀ L ≤ fourthMargin A ell g tau u L₀ ∧
      fifthMargin A ell g tau u₀ L ≤ fifthMargin A ell g tau u L₀ := by
  have hdu : 0 ≤ u - u₀ := sub_nonneg.mpr hu
  have hdL : 0 ≤ L - L₀ := sub_nonneg.mpr hL
  have hell0 : 0 ≤ ell := by linarith only [hell.1]
  have hcoef2 : 0 ≤ g + ell * tau := by positivity
  have hcoef3 : 0 ≤ 3 * ell * A / 2 := by positivity
  have hcoef4 : 0 ≤ g + ell * tau + ell * A / 2 := by positivity
  have hcoef5 : 0 ≤ ell * A := by positivity
  have hpay1 := mul_nonneg hA.le hdu
  have hpay2 := mul_nonneg hcoef2 hdu
  have hpay3 := mul_nonneg hcoef3 hdu
  have hpay4 := mul_nonneg hcoef4 hdu
  have hpay5 := mul_nonneg hcoef5 hdu
  have hpayL := mul_nonneg (by linarith only [hell.2] : 0 ≤ 1 - ell / 2) hdL
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold firstMargin
    nlinarith only [hpay1, hdL]
  · unfold secondMargin
    nlinarith only [hpay2, hdL]
  · unfold thirdMargin
    nlinarith only [hpay3, hpayL]
  · unfold fourthMargin
    nlinarith only [hpay4, hpayL]
  · unfold fifthMargin
    nlinarith only [hpay5, hdL]

private theorem positive_box_margins
    {q qlo qhi A A₀ gamma tau Dstar T u₀ Lupper : ℝ}
    (hqlo : 0 < qlo) (hqhi : qhi ≤ 1 / 5)
    (hq : q ∈ Icc qlo qhi) (hA₀ : 1 / 4 ≤ A₀) (hA : A₀ ≤ A)
    (hD : selectorValue A (multiplier qhi) ≤ Dstar)
    (hgamma : gapFloor q < gamma) (htau : 0 < tau)
    (hcap : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma)
    (hell : 9 / 11 ≤ multiplier qhi) (hellhi : multiplier qlo ≤ 1)
    (hT : 0 < T)
    (hTcert : Dstar - gapFloor qlo < (multiplier qhi - 2 / 3) * T ^ 2)
    (hu₀ : 0 ≤ u₀) (hucert : u₀ * T ≤ max (pairFloor qhi) 0)
    (hL : 0 ≤ Lupper)
    (hLcert : max (-2 * pairFloor qhi) 0 ≤ 3 * Lupper)
    (hbase : 0 < A₀ - T + u₀)
    (hcornerlo : cornerTests A₀ (multiplier qhi) (gapFloor qlo) T u₀ Lupper)
    (hcornerhi : cornerTests A₀ (multiplier qlo) (gapFloor qlo) T u₀ Lupper) :
    let zeta := max (pairFloor q) 0 / tau
    let Lzero := max (-2 * pairFloor q) 0 / 3
    0 < firstMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < secondMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < thirdMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fourthMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fifthMargin A (multiplier q) (gapFloor q) tau zeta Lzero := by
  let zeta := max (pairFloor q) 0 / tau
  let Lzero := max (-2 * pairFloor q) 0 / 3
  obtain ⟨helllo, hellup, hglo, hplo⟩ := box_parameter_bounds hqlo.le hqhi hq
  have hcoef : 0 < multiplier qhi - 2 / 3 := by linarith only [hell]
  have hres := box_selector_residual_lt hqlo.le hqhi hq hD hgamma
  have hdiff := mul_nonneg (sub_nonneg.mpr helllo) (sq_nonneg tau)
  have hbound : (multiplier qhi - 2 / 3) * tau ^ 2 <
      Dstar - gapFloor qlo := by
    nlinarith only [hcap, hdiff, hres]
  have hsq : tau ^ 2 < T ^ 2 := by
    by_contra h
    have hdiff' : 0 ≤ tau ^ 2 - T ^ 2 := by linarith
    have hmul := mul_nonneg hcoef.le hdiff'
    nlinarith only [hmul, lt_trans hbound hTcert]
  have htT : tau < T := by nlinarith only [hsq, htau, hT]
  have hmaxp : max (pairFloor qhi) 0 ≤ max (pairFloor q) 0 :=
    max_le_max hplo le_rfl
  have hucert' : u₀ * tau ≤ max (pairFloor q) 0 := by
    have hm := mul_le_mul_of_nonneg_left htT.le hu₀
    linarith only [hm, hucert, hmaxp]
  have huzeta : u₀ ≤ zeta := by
    dsimp [zeta]
    exact (le_div_iff₀ htau).mpr hucert'
  have hmaxL : max (-2 * pairFloor q) 0 ≤ max (-2 * pairFloor qhi) 0 :=
    max_le_max (by linarith only [hplo]) le_rfl
  have hLzero : Lzero ≤ Lupper := by
    dsimp [Lzero]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
    linarith only [hmaxL, hLcert]
  have hnum := margins_pos_of_rational_corners hA₀ hA
    ⟨helllo, hellup⟩ (by linarith only [hell]) hellhi
    (by
      unfold gapFloor
      have hden := denominator_pos hqlo.le
      exact div_pos (mul_pos hqlo (by linarith only [hqlo])) (by positivity))
    hglo hT.le ⟨htau.le, htT.le⟩ hu₀ hL hbase hcornerlo hcornerhi
  have hmon := margins_mono_canonical (A := A) (by linarith only [hA₀, hA])
    ⟨hell.trans helllo, hellup.trans hellhi⟩ (lt_of_lt_of_le (by
      unfold gapFloor
      have hden := denominator_pos hqlo.le
      exact div_pos (mul_pos hqlo (by linarith only [hqlo])) (by positivity)) hglo)
    htau.le huzeta hLzero
  rcases hnum with ⟨h1, h2, h3, h4, h5⟩
  rcases hmon with ⟨hm1, hm2, hm3, hm4, hm5⟩
  exact ⟨lt_of_lt_of_le h1 hm1, lt_of_lt_of_le h2 hm2,
    lt_of_lt_of_le h3 hm3, lt_of_lt_of_le h4 hm4,
    lt_of_lt_of_le h5 hm5⟩

private theorem first_box_corners :
    cornerTests (11 / 40) (1191 / 1369) (209 / 5249) (229 / 1000) (2 / 25) 0 ∧
      cornerTests (11 / 40) (301 / 339) (209 / 5249) (229 / 1000) (2 / 25) 0 := by
  constructor <;> norm_num [cornerTests, firstMargin, secondMargin, thirdMargin,
    fourthMargin, fifthMargin]

private theorem second_box_corners :
    cornerTests (139 / 480) (589 / 691) (36401 / 816241) (201 / 1000) (23 / 500) (0) ∧
      cornerTests (139 / 480) (1191 / 1369) (36401 / 816241) (201 / 1000) (23 / 500) (0) := by
  constructor <;> norm_num [cornerTests, firstMargin, secondMargin, thirdMargin,
    fourthMargin, fifthMargin]

private theorem third_box_corners :
    cornerTests (73 / 240) (589 / 691) (209 / 5249) (34 / 125) (17 / 500) (0) ∧
      cornerTests (73 / 240) (301 / 339) (209 / 5249) (34 / 125) (17 / 500) (0) := by
  constructor <;> norm_num [cornerTests, firstMargin, secondMargin, thirdMargin,
    fourthMargin, fifthMargin]

private theorem fourth_box_corners :
    cornerTests (139 / 480) (2343 / 2777) (10761 / 219241) (147 / 1000) (37 / 1000) (0) ∧
      cornerTests (139 / 480) (589 / 691) (10761 / 219241) (147 / 1000) (37 / 1000) (0) := by
  constructor <;> norm_num [cornerTests, firstMargin, secondMargin, thirdMargin,
    fourthMargin, fifthMargin]

private theorem fifth_box_corners :
    cornerTests (139 / 480) (233 / 279) (185969 / 3629809) (121 / 1000) (9 / 500) (0) ∧
      cornerTests (139 / 480) (2343 / 2777) (185969 / 3629809) (121 / 1000) (9 / 500) (0) := by
  constructor <;> norm_num [cornerTests, firstMargin, secondMargin, thirdMargin,
    fourthMargin, fifthMargin]

private theorem sixth_box_corners :
    cornerTests (19 / 64) (2317 / 2803) (667 / 12507) (17 / 200) (0) (1 / 1000) ∧
      cornerTests (19 / 64) (233 / 279) (667 / 12507) (17 / 200) (0) (1 / 1000) := by
  constructor <;> norm_num [cornerTests, firstMargin, secondMargin, thirdMargin,
    fourthMargin, fifthMargin]

private theorem seventh_box_corners :
    cornerTests (73 / 240) (233 / 279) (10761 / 219241) (193 / 1000) (11 / 1000) (0) ∧
      cornerTests (73 / 240) (589 / 691) (10761 / 219241) (193 / 1000) (11 / 1000) (0) := by
  constructor <;> norm_num [cornerTests, firstMargin, secondMargin, thirdMargin,
    fourthMargin, fifthMargin]

private theorem eighth_box_corners :
    cornerTests (73 / 240) (9 / 11) (667 / 12507) (161 / 1000) (0) (3 / 1000) ∧
      cornerTests (73 / 240) (233 / 279) (667 / 12507) (161 / 1000) (0) (3 / 1000) := by
  constructor <;> norm_num [cornerTests, firstMargin, secondMargin, thirdMargin,
    fourthMargin, fifthMargin]

private theorem first_box_margins {q A gamma tau : ℝ}
    (hq : q ∈ Icc (19 / 160 : ℝ) (89 / 640))
    (hA : A ∈ Icc (11 / 40 : ℝ) (73 / 240))
    (hgamma : gapFloor q < gamma) (htau : 0 < tau)
    (hcap : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma) :
    let zeta := max (pairFloor q) 0 / tau
    let Lzero := max (-2 * pairFloor q) 0 / 3
    0 < firstMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < secondMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < thirdMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fourthMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fifthMargin A (multiplier q) (gapFloor q) tau zeta Lzero := by
  have hD : selectorValue A (multiplier (89 / 640)) ≤
      (23875799 / 473126400 : ℝ) := by
    calc
      _ ≤ selectorValue (73 / 240) (multiplier (89 / 640)) :=
        selectorValue_le_upper hA.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
      _ = _ := by norm_num [selectorValue, multiplier]
  exact positive_box_margins (T := 229 / 1000) (u₀ := 2 / 25) (Lupper := 0)
    (by norm_num) (by norm_num) hq
    (by norm_num) hA.1 hD hgamma htau hcap
    (by norm_num [multiplier]) (by norm_num [multiplier])
    (by norm_num) (by norm_num [multiplier, gapFloor, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num)
    (by convert first_box_corners.1 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])
    (by convert first_box_corners.2 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])

private theorem second_box_margins {q A gamma tau : ℝ}
    (hq : q ∈ Icc (89 / 640 : ℝ) (51 / 320))
    (hA : A ∈ Icc (139 / 480 : ℝ) (73 / 240))
    (hgamma : gapFloor q < gamma) (htau : 0 < tau)
    (hcap : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma) :
    let zeta := max (pairFloor q) 0 / tau
    let Lzero := max (-2 * pairFloor q) 0 / 3
    0 < firstMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < secondMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < thirdMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fourthMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fifthMargin A (multiplier q) (gapFloor q) tau zeta Lzero := by
  have hD : selectorValue A (multiplier (51 / 320)) ≤ (12439901 / 238809600 : ℝ) := by
    calc
      _ ≤ selectorValue (73 / 240) (multiplier (51 / 320)) :=
        selectorValue_le_upper hA.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
      _ = _ := by norm_num [selectorValue, multiplier]
  exact positive_box_margins (T := 201 / 1000) (u₀ := 23 / 500) (Lupper := 0)
    (by norm_num) (by norm_num) hq
    (by norm_num) hA.1 hD hgamma htau hcap
    (by norm_num [multiplier]) (by norm_num [multiplier])
    (by norm_num) (by norm_num [multiplier, gapFloor, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num)
    (by convert second_box_corners.1 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])
    (by convert second_box_corners.2 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])

private theorem third_box_margins {q A gamma tau : ℝ}
    (hq : q ∈ Icc (19 / 160 : ℝ) (51 / 320))
    (hA : A ∈ Icc (73 / 240 : ℝ) (1 / 3))
    (hgamma : gapFloor q < gamma) (htau : 0 < tau)
    (hcap : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma) :
    let zeta := max (pairFloor q) 0 / tau
    let Lzero := max (-2 * pairFloor q) 0 / 3
    0 < firstMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < secondMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < thirdMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fourthMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fifthMargin A (multiplier q) (gapFloor q) tau zeta Lzero := by
  have hD : selectorValue A (multiplier (51 / 320)) ≤ (895 / 16742 : ℝ) := by
    calc
      _ ≤ (16 / (7 + 6 * multiplier (51 / 320)) - 1) / 6 :=
        selectorValue_le_vertex (by norm_num [multiplier])
      _ = _ := by norm_num [multiplier]
  exact positive_box_margins (T := 34 / 125) (u₀ := 17 / 500) (Lupper := 0)
    (by norm_num) (by norm_num) hq
    (by norm_num) hA.1 hD hgamma htau hcap
    (by norm_num [multiplier]) (by norm_num [multiplier])
    (by norm_num) (by norm_num [multiplier, gapFloor, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num)
    (by convert third_box_corners.1 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])
    (by convert third_box_corners.2 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])

private theorem fourth_box_margins {q A gamma tau : ℝ}
    (hq : q ∈ Icc (51 / 320 : ℝ) (217 / 1280))
    (hA : A ∈ Icc (139 / 480 : ℝ) (73 / 240))
    (hgamma : gapFloor q < gamma) (htau : 0 < tau)
    (hcap : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma) :
    let zeta := max (pairFloor q) 0 / tau
    let Lzero := max (-2 * pairFloor q) 0 / 3
    0 < firstMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < secondMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < thirdMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fourthMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fifthMargin A (multiplier q) (gapFloor q) tau zeta Lzero := by
  have hD : selectorValue A (multiplier (217 / 1280)) ≤ (50763607 / 959731200 : ℝ) := by
    calc
      _ ≤ selectorValue (73 / 240) (multiplier (217 / 1280)) :=
        selectorValue_le_upper hA.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
      _ = _ := by norm_num [selectorValue, multiplier]
  exact positive_box_margins (T := 147 / 1000) (u₀ := 37 / 1000) (Lupper := 0)
    (by norm_num) (by norm_num) hq
    (by norm_num) hA.1 hD hgamma htau hcap
    (by norm_num [multiplier]) (by norm_num [multiplier])
    (by norm_num) (by norm_num [multiplier, gapFloor, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num)
    (by convert fourth_box_corners.1 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])
    (by convert fourth_box_corners.2 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])

private theorem fifth_box_margins {q A gamma tau : ℝ}
    (hq : q ∈ Icc (217 / 1280 : ℝ) (23 / 128))
    (hA : A ∈ Icc (139 / 480 : ℝ) (73 / 240))
    (hgamma : gapFloor q < gamma) (htau : 0 < tau)
    (hcap : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma) :
    let zeta := max (pairFloor q) 0 / tau
    let Lzero := max (-2 * pairFloor q) 0 / 3
    0 < firstMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < secondMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < thirdMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fourthMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fifthMargin A (multiplier q) (gapFloor q) tau zeta Lzero := by
  have hD : selectorValue A (multiplier (23 / 128)) ≤ (1725587 / 32140800 : ℝ) := by
    calc
      _ ≤ selectorValue (73 / 240) (multiplier (23 / 128)) :=
        selectorValue_le_upper hA.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
      _ = _ := by norm_num [selectorValue, multiplier]
  exact positive_box_margins (T := 121 / 1000) (u₀ := 9 / 500) (Lupper := 0)
    (by norm_num) (by norm_num) hq
    (by norm_num) hA.1 hD hgamma htau hcap
    (by norm_num [multiplier]) (by norm_num [multiplier])
    (by norm_num) (by norm_num [multiplier, gapFloor, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num)
    (by convert fifth_box_corners.1 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])
    (by convert fifth_box_corners.2 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])

private theorem sixth_box_margins {q A gamma tau : ℝ}
    (hq : q ∈ Icc (23 / 128 : ℝ) (243 / 1280))
    (hA : A ∈ Icc (19 / 64 : ℝ) (73 / 240))
    (hgamma : gapFloor q < gamma) (htau : 0 < tau)
    (hcap : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma) :
    let zeta := max (pairFloor q) 0 / tau
    let Lzero := max (-2 * pairFloor q) 0 / 3
    0 < firstMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < secondMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < thirdMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fourthMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fifthMargin A (multiplier q) (gapFloor q) tau zeta Lzero := by
  have hD : selectorValue A (multiplier (243 / 1280)) ≤ (52771613 / 968716800 : ℝ) := by
    calc
      _ ≤ selectorValue (73 / 240) (multiplier (243 / 1280)) :=
        selectorValue_le_upper hA.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
      _ = _ := by norm_num [selectorValue, multiplier]
  exact positive_box_margins (T := 17 / 200) (u₀ := 0) (Lupper := 1 / 1000)
    (by norm_num) (by norm_num) hq
    (by norm_num) hA.1 hD hgamma htau hcap
    (by norm_num [multiplier]) (by norm_num [multiplier])
    (by norm_num) (by norm_num [multiplier, gapFloor, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num)
    (by convert sixth_box_corners.1 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])
    (by convert sixth_box_corners.2 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])

private theorem seventh_box_margins {q A gamma tau : ℝ}
    (hq : q ∈ Icc (51 / 320 : ℝ) (23 / 128))
    (hA : A ∈ Icc (73 / 240 : ℝ) (1 / 3))
    (hgamma : gapFloor q < gamma) (htau : 0 < tau)
    (hcap : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma) :
    let zeta := max (pairFloor q) 0 / tau
    let Lzero := max (-2 * pairFloor q) 0 / 3
    0 < firstMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < secondMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < thirdMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fourthMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fifthMargin A (multiplier q) (gapFloor q) tau zeta Lzero := by
  have hD : selectorValue A (multiplier (23 / 128)) ≤ (371 / 6702 : ℝ) := by
    calc
      _ ≤ (16 / (7 + 6 * multiplier (23 / 128)) - 1) / 6 :=
        selectorValue_le_vertex (by norm_num [multiplier])
      _ = _ := by norm_num [multiplier]
  exact positive_box_margins (T := 193 / 1000) (u₀ := 11 / 1000) (Lupper := 0)
    (by norm_num) (by norm_num) hq
    (by norm_num) hA.1 hD hgamma htau hcap
    (by norm_num [multiplier]) (by norm_num [multiplier])
    (by norm_num) (by norm_num [multiplier, gapFloor, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num)
    (by convert seventh_box_corners.1 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])
    (by convert seventh_box_corners.2 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])

private theorem eighth_box_margins {q A gamma tau : ℝ}
    (hq : q ∈ Icc (23 / 128 : ℝ) (1 / 5))
    (hA : A ∈ Icc (73 / 240 : ℝ) (1 / 3))
    (hgamma : gapFloor q < gamma) (htau : 0 < tau)
    (hcap : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma) :
    let zeta := max (pairFloor q) 0 / tau
    let Lzero := max (-2 * pairFloor q) 0 / 3
    0 < firstMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < secondMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < thirdMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fourthMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fifthMargin A (multiplier q) (gapFloor q) tau zeta Lzero := by
  have hD : selectorValue A (multiplier (1 / 5)) ≤ (17 / 297 : ℝ) := by
    calc
      _ ≤ selectorValue (1 / 3) (multiplier (1 / 5)) :=
        selectorValue_le_upper hA.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
      _ = _ := by norm_num [selectorValue, multiplier]
  exact positive_box_margins (T := 161 / 1000) (u₀ := 0) (Lupper := 3 / 1000)
    (by norm_num) (by norm_num) hq
    (by norm_num) hA.1 hD hgamma htau hcap
    (by norm_num [multiplier]) (by norm_num [multiplier])
    (by norm_num) (by norm_num [multiplier, gapFloor, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num) (by norm_num [pairFloor, pairNumerator, denominator])
    (by norm_num)
    (by convert eighth_box_corners.1 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])
    (by convert eighth_box_corners.2 using 1 <;>
      norm_num [multiplier, gapFloor, denominator])

private theorem closed_box_cover (q A : ℝ)
    (hq : q ∈ Icc (19 / 160 : ℝ) (1 / 5))
    (hA : A ∈ Icc (1 / 4 : ℝ) (1 / 3)) :
    (q ∈ Icc (19 / 160 : ℝ) (89 / 640 : ℝ) ∧
      A ∈ Icc (11 / 40 : ℝ) (73 / 240 : ℝ)) ∨
    (q ∈ Icc (89 / 640 : ℝ) (191 / 1280 : ℝ) ∧
      A ∈ Icc (11 / 40 : ℝ) (139 / 480 : ℝ)) ∨
    (q ∈ Icc (191 / 1280 : ℝ) (51 / 320 : ℝ) ∧
      A ∈ Icc (11 / 40 : ℝ) (139 / 480 : ℝ)) ∨
    (q ∈ Icc (89 / 640 : ℝ) (51 / 320 : ℝ) ∧
      A ∈ Icc (139 / 480 : ℝ) (73 / 240 : ℝ)) ∨
    (q ∈ Icc (19 / 160 : ℝ) (51 / 320 : ℝ) ∧
      A ∈ Icc (73 / 240 : ℝ) (1 / 3 : ℝ)) ∨
    (q ∈ Icc (51 / 320 : ℝ) (217 / 1280 : ℝ) ∧
      A ∈ Icc (11 / 40 : ℝ) (139 / 480 : ℝ)) ∨
    (q ∈ Icc (217 / 1280 : ℝ) (23 / 128 : ℝ) ∧
      A ∈ Icc (11 / 40 : ℝ) (139 / 480 : ℝ)) ∨
    (q ∈ Icc (51 / 320 : ℝ) (217 / 1280 : ℝ) ∧
      A ∈ Icc (139 / 480 : ℝ) (73 / 240 : ℝ)) ∨
    (q ∈ Icc (217 / 1280 : ℝ) (23 / 128 : ℝ) ∧
      A ∈ Icc (139 / 480 : ℝ) (73 / 240 : ℝ)) ∨
    (q ∈ Icc (23 / 128 : ℝ) (1 / 5 : ℝ) ∧
      A ∈ Icc (11 / 40 : ℝ) (139 / 480 : ℝ)) ∨
    (q ∈ Icc (23 / 128 : ℝ) (473 / 2560 : ℝ) ∧
      A ∈ Icc (139 / 480 : ℝ) (19 / 64 : ℝ)) ∨
    (q ∈ Icc (473 / 2560 : ℝ) (243 / 1280 : ℝ) ∧
      A ∈ Icc (139 / 480 : ℝ) (19 / 64 : ℝ)) ∨
    (q ∈ Icc (23 / 128 : ℝ) (243 / 1280 : ℝ) ∧
      A ∈ Icc (19 / 64 : ℝ) (73 / 240 : ℝ)) ∨
    (q ∈ Icc (243 / 1280 : ℝ) (1 / 5 : ℝ) ∧
      A ∈ Icc (139 / 480 : ℝ) (73 / 240 : ℝ)) ∨
    (q ∈ Icc (51 / 320 : ℝ) (23 / 128 : ℝ) ∧
      A ∈ Icc (73 / 240 : ℝ) (1 / 3 : ℝ)) ∨
    (q ∈ Icc (23 / 128 : ℝ) (1 / 5 : ℝ) ∧
      A ∈ Icc (73 / 240 : ℝ) (1 / 3 : ℝ)) ∨
    (q ∈ Icc (19 / 160 : ℝ) (89 / 640 : ℝ) ∧
      A ∈ Icc (1 / 4 : ℝ) (11 / 40 : ℝ)) ∨
    (q ∈ Icc (89 / 640 : ℝ) (51 / 320 : ℝ) ∧
      A ∈ Icc (1 / 4 : ℝ) (11 / 40 : ℝ)) ∨
    (q ∈ Icc (51 / 320 : ℝ) (23 / 128 : ℝ) ∧
      A ∈ Icc (1 / 4 : ℝ) (11 / 40 : ℝ)) ∨
    (q ∈ Icc (23 / 128 : ℝ) (1 / 5 : ℝ) ∧
      A ∈ Icc (1 / 4 : ℝ) (11 / 40 : ℝ)) := by
  rcases hq with ⟨hqlo, hqhi⟩
  rcases hA with ⟨hAlo, hAhi⟩
  rcases le_total A (11 / 40 : ℝ) with hsplit | hsplit
  · rcases le_total q (51 / 320 : ℝ) with hcut1 | hcut1
    · rcases le_total q (89 / 640 : ℝ) with hcut2 | hcut2
      · have hbox : q ∈ Icc (19 / 160 : ℝ) (89 / 640 : ℝ) ∧
            A ∈ Icc (1 / 4 : ℝ) (11 / 40 : ℝ) := by
          constructor <;> constructor <;> linarith
        exact Or.inr <|
          Or.inr <|
            Or.inr <|
              Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inr <|
                                Or.inr <|
                                  Or.inr <|
                                    Or.inr <|
                                      Or.inr <|
                                        Or.inl hbox
      · have hbox : q ∈ Icc (89 / 640 : ℝ) (51 / 320 : ℝ) ∧
            A ∈ Icc (1 / 4 : ℝ) (11 / 40 : ℝ) := by
          constructor <;> constructor <;> linarith
        exact Or.inr <|
          Or.inr <|
            Or.inr <|
              Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inr <|
                                Or.inr <|
                                  Or.inr <|
                                    Or.inr <|
                                      Or.inr <|
                                        Or.inr <|
                                          Or.inl hbox
    · rcases le_total q (23 / 128 : ℝ) with hcut3 | hcut3
      · have hbox : q ∈ Icc (51 / 320 : ℝ) (23 / 128 : ℝ) ∧
            A ∈ Icc (1 / 4 : ℝ) (11 / 40 : ℝ) := by
          constructor <;> constructor <;> linarith
        exact Or.inr <|
          Or.inr <|
            Or.inr <|
              Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inr <|
                                Or.inr <|
                                  Or.inr <|
                                    Or.inr <|
                                      Or.inr <|
                                        Or.inr <|
                                          Or.inr <|
                                            Or.inl hbox
      · have hbox : q ∈ Icc (23 / 128 : ℝ) (1 / 5 : ℝ) ∧
            A ∈ Icc (1 / 4 : ℝ) (11 / 40 : ℝ) := by
          constructor <;> constructor <;> linarith
        exact Or.inr <|
          Or.inr <|
            Or.inr <|
              Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inr <|
                                Or.inr <|
                                  Or.inr <|
                                    Or.inr <|
                                      Or.inr <|
                                        Or.inr <|
                                          Or.inr <|
                                            Or.inr <|
                                              hbox
  · rcases le_total q (51 / 320 : ℝ) with hcut4 | hcut4
    · rcases le_total A (73 / 240 : ℝ) with hcut5 | hcut5
      · rcases le_total q (89 / 640 : ℝ) with hcut6 | hcut6
        · have hbox : q ∈ Icc (19 / 160 : ℝ) (89 / 640 : ℝ) ∧
              A ∈ Icc (11 / 40 : ℝ) (73 / 240 : ℝ) := by
            constructor <;> constructor <;> linarith
          exact Or.inl hbox
        · rcases le_total A (139 / 480 : ℝ) with hcut7 | hcut7
          · rcases le_total q (191 / 1280 : ℝ) with hcut8 | hcut8
            · have hbox : q ∈ Icc (89 / 640 : ℝ) (191 / 1280 : ℝ) ∧
                  A ∈ Icc (11 / 40 : ℝ) (139 / 480 : ℝ) := by
                constructor <;> constructor <;> linarith
              exact Or.inr <|
                Or.inl hbox
            · have hbox : q ∈ Icc (191 / 1280 : ℝ) (51 / 320 : ℝ) ∧
                  A ∈ Icc (11 / 40 : ℝ) (139 / 480 : ℝ) := by
                constructor <;> constructor <;> linarith
              exact Or.inr <|
                Or.inr <|
                  Or.inl hbox
          · have hbox : q ∈ Icc (89 / 640 : ℝ) (51 / 320 : ℝ) ∧
                A ∈ Icc (139 / 480 : ℝ) (73 / 240 : ℝ) := by
              constructor <;> constructor <;> linarith
            exact Or.inr <|
              Or.inr <|
                Or.inr <|
                  Or.inl hbox
      · have hbox : q ∈ Icc (19 / 160 : ℝ) (51 / 320 : ℝ) ∧
            A ∈ Icc (73 / 240 : ℝ) (1 / 3 : ℝ) := by
          constructor <;> constructor <;> linarith
        exact Or.inr <|
          Or.inr <|
            Or.inr <|
              Or.inr <|
                Or.inl hbox
    · rcases le_total A (73 / 240 : ℝ) with hcut9 | hcut9
      · rcases le_total q (23 / 128 : ℝ) with hcut10 | hcut10
        · rcases le_total A (139 / 480 : ℝ) with hcut11 | hcut11
          · rcases le_total q (217 / 1280 : ℝ) with hcut12 | hcut12
            · have hbox : q ∈ Icc (51 / 320 : ℝ) (217 / 1280 : ℝ) ∧
                  A ∈ Icc (11 / 40 : ℝ) (139 / 480 : ℝ) := by
                constructor <;> constructor <;> linarith
              exact Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inl hbox
            · have hbox : q ∈ Icc (217 / 1280 : ℝ) (23 / 128 : ℝ) ∧
                  A ∈ Icc (11 / 40 : ℝ) (139 / 480 : ℝ) := by
                constructor <;> constructor <;> linarith
              exact Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inl hbox
          · rcases le_total q (217 / 1280 : ℝ) with hcut13 | hcut13
            · have hbox : q ∈ Icc (51 / 320 : ℝ) (217 / 1280 : ℝ) ∧
                  A ∈ Icc (139 / 480 : ℝ) (73 / 240 : ℝ) := by
                constructor <;> constructor <;> linarith
              exact Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inl hbox
            · have hbox : q ∈ Icc (217 / 1280 : ℝ) (23 / 128 : ℝ) ∧
                  A ∈ Icc (139 / 480 : ℝ) (73 / 240 : ℝ) := by
                constructor <;> constructor <;> linarith
              exact Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inl hbox
        · rcases le_total A (139 / 480 : ℝ) with hcut14 | hcut14
          · have hbox : q ∈ Icc (23 / 128 : ℝ) (1 / 5 : ℝ) ∧
                A ∈ Icc (11 / 40 : ℝ) (139 / 480 : ℝ) := by
              constructor <;> constructor <;> linarith
            exact Or.inr <|
              Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inl hbox
          · rcases le_total q (243 / 1280 : ℝ) with hcut15 | hcut15
            · rcases le_total A (19 / 64 : ℝ) with hcut16 | hcut16
              · rcases le_total q (473 / 2560 : ℝ) with hcut17 | hcut17
                · have hbox : q ∈ Icc (23 / 128 : ℝ) (473 / 2560 : ℝ) ∧
                      A ∈ Icc (139 / 480 : ℝ) (19 / 64 : ℝ) := by
                    constructor <;> constructor <;> linarith
                  exact Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inr <|
                                Or.inr <|
                                  Or.inr <|
                                    Or.inr <|
                                      Or.inl hbox
                · have hbox : q ∈ Icc (473 / 2560 : ℝ) (243 / 1280 : ℝ) ∧
                      A ∈ Icc (139 / 480 : ℝ) (19 / 64 : ℝ) := by
                    constructor <;> constructor <;> linarith
                  exact Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inr <|
                                Or.inr <|
                                  Or.inr <|
                                    Or.inr <|
                                      Or.inr <|
                                        Or.inl hbox
              · have hbox : q ∈ Icc (23 / 128 : ℝ) (243 / 1280 : ℝ) ∧
                    A ∈ Icc (19 / 64 : ℝ) (73 / 240 : ℝ) := by
                  constructor <;> constructor <;> linarith
                exact Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inr <|
                                Or.inr <|
                                  Or.inr <|
                                    Or.inr <|
                                      Or.inr <|
                                        Or.inl hbox
            · have hbox : q ∈ Icc (243 / 1280 : ℝ) (1 / 5 : ℝ) ∧
                  A ∈ Icc (139 / 480 : ℝ) (73 / 240 : ℝ) := by
                constructor <;> constructor <;> linarith
              exact Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inr <|
                                Or.inr <|
                                  Or.inr <|
                                    Or.inr <|
                                      Or.inr <|
                                        Or.inl hbox
      · rcases le_total q (23 / 128 : ℝ) with hcut18 | hcut18
        · have hbox : q ∈ Icc (51 / 320 : ℝ) (23 / 128 : ℝ) ∧
              A ∈ Icc (73 / 240 : ℝ) (1 / 3 : ℝ) := by
            constructor <;> constructor <;> linarith
          exact Or.inr <|
            Or.inr <|
              Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inr <|
                                Or.inr <|
                                  Or.inr <|
                                    Or.inr <|
                                      Or.inl hbox
        · have hbox : q ∈ Icc (23 / 128 : ℝ) (1 / 5 : ℝ) ∧
              A ∈ Icc (73 / 240 : ℝ) (1 / 3 : ℝ) := by
            constructor <;> constructor <;> linarith
          exact Or.inr <|
            Or.inr <|
              Or.inr <|
                Or.inr <|
                  Or.inr <|
                    Or.inr <|
                      Or.inr <|
                        Or.inr <|
                          Or.inr <|
                            Or.inr <|
                              Or.inr <|
                                Or.inr <|
                                  Or.inr <|
                                    Or.inr <|
                                      Or.inr <|
                                        Or.inl hbox

private theorem canonical_margins
    {q A gamma tau u v : ℝ}
    (hq : q ∈ Icc (19 / 160 : ℝ) (1 / 5))
    (hA : A ∈ Icc (1 / 4 : ℝ) (1 / 3))
    (hgamma : gapFloor q < gamma) (htau : 0 < tau)
    (hcap : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma)
    (hhead : (multiplier q - 2 / 3) * (u ^ 2 + v ^ 2) ≤
      selectorValue A (multiplier q) - gamma)
    (hproduct : pairFloor q < u * v) :
    let zeta := max (pairFloor q) 0 / tau
    let Lzero := max (-2 * pairFloor q) 0 / 3
    0 < firstMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < secondMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < thirdMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fourthMargin A (multiplier q) (gapFloor q) tau zeta Lzero ∧
      0 < fifthMargin A (multiplier q) (gapFloor q) tau zeta Lzero := by
  rcases closed_box_cover q A hq hA with
    hbox | hbox | hbox | hbox | hbox |
    hbox | hbox | hbox | hbox | hbox |
    hbox | hbox | hbox | hbox | hbox |
    hbox | hbox | hbox | hbox | hbox
  · exact first_box_margins hbox.1 hbox.2 hgamma htau hcap
  · have hD : selectorValue A (multiplier (191 / 1280)) ≤
        selectorValue (139 / 480) (multiplier (191 / 1280)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| head_square_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma hhead hproduct
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, pairFloor,
        pairNumerator, denominator])
  · have hD : selectorValue A (multiplier (51 / 320)) ≤
        selectorValue (139 / 480) (multiplier (51 / 320)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| head_square_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma hhead hproduct
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, pairFloor,
        pairNumerator, denominator])
  · exact second_box_margins hbox.1 hbox.2 hgamma htau hcap
  · exact third_box_margins hbox.1 hbox.2 hgamma htau hcap
  · have hD : selectorValue A (multiplier (217 / 1280)) ≤
        selectorValue (139 / 480) (multiplier (217 / 1280)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| head_square_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma hhead hproduct
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, pairFloor,
        pairNumerator, denominator])
  · have hD : selectorValue A (multiplier (23 / 128)) ≤
        selectorValue (139 / 480) (multiplier (23 / 128)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| head_square_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma hhead hproduct
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, pairFloor,
        pairNumerator, denominator])
  · exact fourth_box_margins hbox.1 hbox.2 hgamma htau hcap
  · exact fifth_box_margins hbox.1 hbox.2 hgamma htau hcap
  · have hD : selectorValue A (multiplier (1 / 5)) ≤
        selectorValue (139 / 480) (multiplier (1 / 5)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| selector_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma htau hcap
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, denominator])
  · have hD : selectorValue A (multiplier (473 / 2560)) ≤
        selectorValue (19 / 64) (multiplier (473 / 2560)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| selector_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma htau hcap
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, denominator])
  · have hD : selectorValue A (multiplier (243 / 1280)) ≤
        selectorValue (19 / 64) (multiplier (243 / 1280)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| selector_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma htau hcap
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, denominator])
  · exact sixth_box_margins hbox.1 hbox.2 hgamma htau hcap
  · have hD : selectorValue A (multiplier (1 / 5)) ≤
        selectorValue (73 / 240) (multiplier (1 / 5)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| selector_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma htau hcap
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, denominator])
  · exact seventh_box_margins hbox.1 hbox.2 hgamma htau hcap
  · exact eighth_box_margins hbox.1 hbox.2 hgamma htau hcap
  · have hD : selectorValue A (multiplier (89 / 640)) ≤
        selectorValue (11 / 40) (multiplier (89 / 640)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| head_square_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma hhead hproduct
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, pairFloor,
        pairNumerator, denominator])
  · have hD : selectorValue A (multiplier (51 / 320)) ≤
        selectorValue (11 / 40) (multiplier (51 / 320)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| head_square_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma hhead hproduct
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, pairFloor,
        pairNumerator, denominator])
  · have hD : selectorValue A (multiplier (23 / 128)) ≤
        selectorValue (11 / 40) (multiplier (23 / 128)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| selector_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma htau hcap
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, denominator])
  · have hD : selectorValue A (multiplier (1 / 5)) ≤
        selectorValue (11 / 40) (multiplier (1 / 5)) :=
        selectorValue_le_upper hbox.2.2 (by norm_num [multiplier])
          (by norm_num [multiplier])
    exact False.elim <| selector_leaf_impossible
      (by norm_num) (by norm_num) hbox.1 hD hgamma htau hcap
      (by norm_num [multiplier])
      (by norm_num [selectorValue, multiplier, gapFloor, denominator])

/-- The coupled middle saturated private star contradicts the original failed insertion. -/
theorem nonpositive_star_impossible
    (q A gamma tau u v a f L beta : ℝ)
    (hq : q ∈ Icc (19 / 160 : ℝ) (1 / 5))
    (hA : A ∈ Icc (1 / 4 : ℝ) (1 / 3))
    (hgamma : gapFloor q < gamma)
    (htau : 0 < tau) (htauA : tau ≤ A)
    (hselector : (multiplier q - 2 / 3) * tau ^ 2 ≤
      selectorValue A (multiplier q) - gamma)
    (hhead : (multiplier q - 2 / 3) * (u ^ 2 + v ^ 2) ≤
      selectorValue A (multiplier q) - gamma)
    (hu : 0 < u) (hv : 0 < v) (hvA : v < A) (hvtau : v ≤ tau)
    (hproduct : pairFloor q < u * v)
    (ha : 0 ≤ a) (hf : 0 ≤ f) (hw : a + u + f ≤ tau)
    (hL : L ≤ surplusCap q u v)
    (hbeta : beta ∈ Icc (-multiplier q) 0)
    (hinsertion : ((A * (3 * A + u - 1) + L) / 2 + A * f) * beta ≥
      (A - a) * (gamma + multiplier q * (a + u + f)) - A * f - L) : False := by
  have hApos : 0 < A := by linarith only [hA.1]
  have hq0 : 0 ≤ q := by linarith only [hq.1]
  have hell : multiplier q ∈ Icc (9 / 11 : ℝ) 1 := ⟨
    E2PrivateCurvature.multiplier_ge_nine_elevenths
      ⟨hq0, hq.2⟩,
    by
      unfold multiplier
      apply (div_le_iff₀ (by linarith only [hq0])).mpr
      linarith only [hq0]⟩
  have hg : 0 < gapFloor q := by
    unfold gapFloor
    exact div_pos (mul_pos (by linarith only [hq.1])
      (by linarith only [hq.1]))
      (mul_pos (by norm_num) (denominator_pos hq0))
  have hcanonical := canonical_margins hq hA hgamma htau hselector hhead hproduct
  have hcoupled := MiddleSaturatedPrivateStarsCoupling.all_margins_ge_canonical
    A (multiplier q) (gapFloor q) tau u v (pairFloor q) (surplusCap q u v)
    hApos hu hv hvA hvtau htau hell hg hproduct
    (by unfold surplusCap; exact le_refl _)
  dsimp only at hcanonical hcoupled
  rcases hcanonical with ⟨hc1, hc2, hc3, hc4, hc5⟩
  rcases hcoupled with ⟨hk1, hk2, hk3, hk4, hk5⟩
  exact nonpositive_star_impossible_of_margins
    A (multiplier q) (gapFloor q) gamma tau u a f L (surplusCap q u v) beta
    hApos hu ha hf hw htauA
    ⟨by linarith only [hell.1], hell.2⟩ hgamma.le hL hbeta
    (lt_of_lt_of_le hc1 hk1) (lt_of_lt_of_le hc2 hk2)
    (lt_of_lt_of_le hc3 hk3) (lt_of_lt_of_le hc4 hk4)
    (lt_of_lt_of_le hc5 hk5) hinsertion

end Erdos1017.MiddleSaturatedPrivateStarsScalar
