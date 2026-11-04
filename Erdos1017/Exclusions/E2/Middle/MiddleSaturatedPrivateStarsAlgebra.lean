module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Five endpoint margins for the saturated private stars

Five scalar margins (`firstMargin` to `fifthMargin`) are defined at the
zero-charge and lowest-charge endpoints, with or without a self atom or
additional forbidden mass, and their positivity excludes the failed-insertion
inequality at any nonpositive charge while keeping one shared surplus.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.MiddleSaturatedPrivateStarsAlgebra

/-- The zero-charge endpoint at the largest missing mass and no self atom. -/
def firstMargin (A ell g tau u L : ℝ) : ℝ :=
  A * (g - (1 - ell) * tau + u) - L

/-- The zero-charge endpoint at the largest possible self atom. -/
def secondMargin (A ell g tau u L : ℝ) : ℝ :=
  (A - tau + u) * (g + ell * tau) - L

/-- The lowest-charge endpoint with no additional forbidden mass. -/
def thirdMargin (A ell g _tau u L : ℝ) : ℝ :=
  A * (g + ell / 2 * (3 * A + 3 * u - 1)) - (1 - ell / 2) * L

/-- The lowest-charge endpoint at the largest possible self atom. -/
def fourthMargin (A ell g tau u L : ℝ) : ℝ :=
  (A - tau + u) * (g + ell * tau) + ell * A / 2 * (3 * A + u - 1) -
    (1 - ell / 2) * L

/-- The zero-charge endpoint with no additional forbidden mass. -/
def fifthMargin (A ell g _tau u L : ℝ) : ℝ :=
  A * (g + ell * u) - L

private theorem quadratic_pos_of_endpoints (C B k lo hi x : ℝ)
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

/-- The five positive endpoints exclude the actual failed-insertion
inequality at any nonpositive charge, retaining one shared surplus. -/
theorem nonpositive_star_impossible_of_margins
    (A ell g gamma tau u a f L Lmax beta : ℝ)
    (hA : 0 < A) (hu : 0 < u) (ha : 0 ≤ a) (hf : 0 ≤ f)
    (hw : a + u + f ≤ tau) (htau : tau ≤ A)
    (hell : ell ∈ Icc (1 / 2 : ℝ) 1) (hgamma : g ≤ gamma)
    (hL : L ≤ Lmax) (hbeta : beta ∈ Icc (-ell) 0)
    (hfirst : 0 < firstMargin A ell g tau u Lmax)
    (hsecond : 0 < secondMargin A ell g tau u Lmax)
    (hthird : 0 < thirdMargin A ell g tau u Lmax)
    (hfourth : 0 < fourthMargin A ell g tau u Lmax)
    (hfifth : 0 < fifthMargin A ell g tau u Lmax)
    (hinsertion : ((A * (3 * A + u - 1) + L) / 2 + A * f) * beta ≥
      (A - a) * (gamma + ell * (a + u + f)) - A * f - L) : False := by
  let w := a + u + f
  let R := (A * (3 * A + u - 1) + Lmax) / 2
  have hell0 : 0 < ell := by linarith only [hell.1]
  have huw : u ≤ w := by dsimp only [w]; linarith only [ha, hf]
  have hw' : w ≤ tau := hw
  have haA : a < A := by linarith only [hu, hf, hw, htau]
  have ha' : a ∈ Icc (0 : ℝ) (w - u) := by
    constructor
    · exact ha
    · dsimp only [w]
      linarith only [hf]
  have hz0 : 0 < A * (g + ell * w) - A * (w - u) - Lmax := by
    have hprod := mul_nonneg (mul_nonneg hA.le (sub_nonneg.mpr hell.2))
      (sub_nonneg.mpr hw')
    dsimp only [firstMargin] at hfirst
    nlinarith only [hfirst, hprod]
  have hz1 : 0 < (A - w + u) * (g + ell * w) - Lmax := by
    have hlo : 0 < (A + u) * g - Lmax + ((A + u) * ell - g) * u - ell * u ^ 2 := by
      dsimp only [fifthMargin] at hfifth
      nlinarith only [hfifth]
    have hhi : 0 < (A + u) * g - Lmax + ((A + u) * ell - g) * tau -
        ell * tau ^ 2 := by
      dsimp only [secondMargin] at hsecond
      nlinarith only [hsecond]
    have h := quadratic_pos_of_endpoints ((A + u) * g - Lmax)
      ((A + u) * ell - g) ell u tau w hell0.le ⟨huw, hw'⟩ hlo hhi
    nlinarith only [h]
  have hn0 : 0 < A * (g + ell * w) - A * (w - u) - Lmax +
      ell * (R + A * (w - u)) := by
    have hprod := mul_nonneg (mul_nonneg hA.le (show 0 ≤ 2 * ell - 1 by
      linarith only [hell.1])) (sub_nonneg.mpr huw)
    dsimp only [thirdMargin] at hthird
    dsimp only [R]
    nlinarith only [hthird, hprod]
  have hn1 : 0 < (A - w + u) * (g + ell * w) - Lmax + ell * R := by
    have hlo : 0 < (A + u) * g - Lmax + ell * R +
        ((A + u) * ell - g) * u - ell * u ^ 2 := by
      dsimp only [thirdMargin, R] at *
      nlinarith only [hthird]
    have hhi : 0 < (A + u) * g - Lmax + ell * R +
        ((A + u) * ell - g) * tau - ell * tau ^ 2 := by
      dsimp only [fourthMargin, R] at *
      nlinarith only [hfourth]
    have h := quadratic_pos_of_endpoints ((A + u) * g - Lmax + ell * R)
      ((A + u) * ell - g) ell u tau w hell0.le ⟨huw, hw'⟩ hlo hhi
    nlinarith only [h]
  have hzero : 0 < (A - a) * (g + ell * w) - A * f - Lmax := by
    have hlo : 0 < A * (g + ell * w) - A * (w - u) - Lmax +
        (A - g - ell * w) * 0 - 0 * (0 : ℝ) ^ 2 := by
      simpa only [mul_zero, zero_mul, sub_zero, add_zero] using hz0
    have hhi : 0 < A * (g + ell * w) - A * (w - u) - Lmax +
        (A - g - ell * w) * (w - u) - 0 * (w - u) ^ 2 := by
      nlinarith only [hz1]
    have h := quadratic_pos_of_endpoints (A * (g + ell * w) - A * (w - u) - Lmax)
      (A - g - ell * w) 0 0 (w - u) a (by norm_num) ha' hlo hhi
    dsimp only [w] at h ⊢
    nlinarith only [h]
  have hnegative : 0 < (A - a) * (g + ell * w) - A * f - Lmax +
      ell * (R + A * f) := by
    have hlo : 0 < A * (g + ell * w) - A * (w - u) - Lmax +
        ell * (R + A * (w - u)) + (A - g - ell * w - ell * A) * 0 -
          0 * (0 : ℝ) ^ 2 := by
      simpa only [mul_zero, zero_mul, sub_zero, add_zero] using hn0
    have hhi : 0 < A * (g + ell * w) - A * (w - u) - Lmax +
        ell * (R + A * (w - u)) + (A - g - ell * w - ell * A) * (w - u) -
          0 * (w - u) ^ 2 := by
      nlinarith only [hn1]
    have h := quadratic_pos_of_endpoints
      (A * (g + ell * w) - A * (w - u) - Lmax + ell * (R + A * (w - u)))
      (A - g - ell * w - ell * A) 0 0 (w - u) a (by norm_num) ha' hlo hhi
    dsimp only [w] at h ⊢
    nlinarith only [h]
  have hstar : 0 < (A - a) * (g + ell * w) - A * f - Lmax -
      (R + A * f) * beta := by
    have hlo : 0 < (A - a) * (g + ell * w) - A * f - Lmax +
        (-(R + A * f)) * (-ell) - 0 * (-ell) ^ 2 := by
      nlinarith only [hnegative]
    have hhi : 0 < (A - a) * (g + ell * w) - A * f - Lmax +
        (-(R + A * f)) * 0 - 0 * (0 : ℝ) ^ 2 := by
      simpa only [mul_zero, zero_mul, sub_zero, add_zero] using hzero
    have h := quadratic_pos_of_endpoints ((A - a) * (g + ell * w) - A * f - Lmax)
      (-(R + A * f)) 0 (-ell) 0 beta (by norm_num) hbeta hlo hhi
    nlinarith only [h]
  have hpayGamma := mul_nonneg (sub_pos.mpr haA).le (sub_nonneg.mpr hgamma)
  have hpayL := mul_nonneg (sub_nonneg.mpr hL)
    (show 0 ≤ 1 + beta / 2 by linarith only [hbeta.1, hell.2])
  dsimp only [R, w] at hstar
  nlinarith only [hinsertion, hstar, hpayGamma, hpayL]

end Erdos1017.MiddleSaturatedPrivateStarsAlgebra
