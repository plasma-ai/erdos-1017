module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# High-slope inside-source payment at the third cusp

The third-cusp high-slope inside-source payment holds with the endpoint
`ell = 1` included and without dividing by `ell - 1`, built from the radical,
head, remainder and correlated coefficients (`source_payment`,
`source_payment_sqrt`).
-/

@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

namespace Erdos1017.CuspThreeHighSourcePayment

/-- The cleared radical cubic is concave in `r` with value `2t^2` at zero, so a
nonnegative endpoint value persists below the endpoint. -/
theorem cubic_of_endpoint {t r R : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hR : 0 < R)
    (hend : 0 ≤ 3 * R * t + 2 * t ^ 2 - R ^ 3 - 2 * R ^ 2 * t - 3 * R * t ^ 2) :
    0 ≤ 3 * r * t + 2 * t ^ 2 - r ^ 3 - 2 * r ^ 2 * t - 3 * r * t ^ 2 := by
  have hconc : R * (3 * r * t + 2 * t ^ 2 - r ^ 3 - 2 * r ^ 2 * t - 3 * r * t ^ 2) =
      (R - r) * (2 * t ^ 2) +
        r * (3 * R * t + 2 * t ^ 2 - R ^ 3 - 2 * R ^ 2 * t - 3 * R * t ^ 2) +
        r * R * (R - r) * (R + r + 2 * t) := by
    ring
  have h1 : 0 ≤ (R - r) * (2 * t ^ 2) := mul_nonneg (sub_nonneg.mpr hrR) (by positivity)
  have h2 := mul_nonneg hr hend
  have h3 : 0 ≤ r * R * (R - r) * (R + r + 2 * t) :=
    mul_nonneg (mul_nonneg (mul_nonneg hr hR.le) (sub_nonneg.mpr hrR)) (by linarith)
  refine le_of_not_gt fun hneg => ?_
  have hprod := mul_neg_of_pos_of_neg hR hneg
  linarith

/-- Radical coefficient: with `Gn = r^2 + 2rt + 3t^2 - t` and `Gd = 2tr(r+t)`,
the missing-square slack `m ≤ min (r^2) (9/25)` pays `m * Gn ≤ Gd`. -/
theorem radical_gain {t r m : ℝ} (ht : 0 < t) (hr : 0 < r)
    (hrhi : r ^ 2 ≤ 2 * t - t ^ 2) (hm : 0 ≤ m) (hmr : m ≤ r ^ 2)
    (hm9 : m ≤ 9 / 25) :
    m * (r ^ 2 + 2 * r * t + 3 * t ^ 2 - t) ≤ 2 * t * r * (r + t) := by
  have hGd : 0 < 2 * t * r * (r + t) := by positivity
  rcases le_or_gt (r ^ 2 + 2 * r * t + 3 * t ^ 2 - t) 0 with hGn | hGn
  · linarith [mul_nonpos_of_nonneg_of_nonpos hm hGn]
  rcases le_total r (3 / 5) with hr35 | hr35
  · have hP : 0 ≤ 3 * r * t + 2 * t ^ 2 - r ^ 3 - 2 * r ^ 2 * t - 3 * r * t ^ 2 := by
      rcases le_total t (1 / 5) with ht5 | ht5
      · have hbase : 0 ≤ 2 * t - t ^ 2 := by
          nlinarith [mul_pos ht (by linarith : (0 : ℝ) < 2 - t)]
        obtain ⟨R, hR0, hR2⟩ : ∃ R : ℝ, 0 ≤ R ∧ R ^ 2 = 2 * t - t ^ 2 :=
          ⟨Real.sqrt (2 * t - t ^ 2), Real.sqrt_nonneg _, Real.sq_sqrt hbase⟩
        have hrR : r ≤ R := by
          refine le_of_not_gt fun hlt => ?_
          nlinarith [mul_self_lt_mul_self hR0 hlt]
        have hu : 0 ≤ 1 / 5 - t := by linarith
        have hcubic : 0 ≤ 2 - 13 * t + 20 * t ^ 2 - 8 * t ^ 3 := by
          nlinarith [mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu]
        have hside : 2 * t * (1 - t) ≤ R * (1 - 2 * t) := by
          have hleft : 0 ≤ R * (1 - 2 * t) := mul_nonneg hR0 (by linarith)
          refine le_of_not_gt fun hlt => ?_
          have hsq := mul_self_lt_mul_self hleft hlt
          have hexp : R * (1 - 2 * t) * (R * (1 - 2 * t)) =
              (2 * t - t ^ 2) * (1 - 2 * t) ^ 2 := by
            linear_combination (1 - 2 * t) ^ 2 * hR2
          nlinarith [mul_nonneg ht.le hcubic]
        have hend : 0 ≤ 3 * R * t + 2 * t ^ 2 - R ^ 3 - 2 * R ^ 2 * t - 3 * R * t ^ 2 := by
          have heq : 3 * R * t + 2 * t ^ 2 - R ^ 3 - 2 * R ^ 2 * t - 3 * R * t ^ 2 =
              t * (R * (1 - 2 * t) - 2 * t * (1 - t)) := by
            linear_combination (-(R + 2 * t)) * hR2
          rw [heq]
          exact mul_nonneg ht.le (by linarith)
        exact cubic_of_endpoint ht.le hr.le hrR (lt_of_lt_of_le hr hrR) hend
      · exact cubic_of_endpoint ht.le hr.le hr35 (by norm_num)
          (by nlinarith [sq_nonneg t])
    have hcub : r ^ 2 * (r ^ 2 + 2 * r * t + 3 * t ^ 2 - t) ≤ 2 * t * r * (r + t) := by
      nlinarith [mul_nonneg hr.le hP]
    have hscale := mul_le_mul_of_nonneg_right hmr hGn.le
    linarith
  · have ht5 : 1 / 5 ≤ t := by
      refine le_of_not_gt fun hlt => ?_
      nlinarith [sq_nonneg (r - 3 / 5),
        mul_pos (by linarith : (0 : ℝ) < 1 / 5 - t) (by linarith : (0 : ℝ) < 9 / 5 - t)]
    have hs : 0 ≤ r - 3 / 5 := by linarith
    have hw : 0 ≤ t - 1 / 5 := by linarith
    have hP3 : 0 ≤ 50 * t * r * (r + t) - 9 * r * (r + t) - 9 * t * (r + 3 * t - 1) := by
      have heq : 50 * t * r * (r + t) - 9 * r * (r + t) - 9 * t * (r + 3 * t - 1) =
          (t - 1 / 5) * (50 * (r - 3 / 5) ^ 2 + (50 * t + 52) * (r - 3 / 5) +
            3 * t + 84 / 5) + (r - 4 / 5) ^ 2 + 2 / 25 := by
        ring
      have hin : 0 ≤ 50 * (r - 3 / 5) ^ 2 + (50 * t + 52) * (r - 3 / 5) +
          3 * t + 84 / 5 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 50 * t + 52) hs, sq_nonneg (r - 3 / 5)]
      rw [heq]
      nlinarith [mul_nonneg hw hin, sq_nonneg (r - 4 / 5)]
    have hscale := mul_le_mul_of_nonneg_right hm9 hGn.le
    linarith

/-- Original-head coefficient, paid by the original reserve alone. -/
theorem head_price {ell X y : ℝ} (hell : 1 ≤ ell) (hell4 : ell < 4 / 3) (hX : 0 < X)
    (hy : 16 / 25 < y) (hy1 : y < 1)
    (hreserve : (4 / 3 - ell) * y < (2 - ell) * X ^ 2) :
    (4 / 3 - ell) * (max (1 / 2 - X) 0 / X) * (1 - y) ≤
      (4 / 3 - ell) * y + (ell - 1) / 2 := by
  have hδ : 0 < 4 / 3 - ell := by linarith
  have ha : 0 < 5 / 3 - ell := by linarith
  have hb : 0 < 2 - ell := by linarith
  have hm : 0 < 1 - y := by linarith
  rcases le_total (1 / 2 - X) 0 with hfar | hnear
  · rw [max_eq_right hfar, zero_div, mul_zero, zero_mul]
    nlinarith [mul_pos hδ (by linarith : (0 : ℝ) < y)]
  rw [max_eq_left hnear]
  have hbal : (4 / 3 - ell) * (2 - ell) ≤ (5 / 3 - ell) ^ 2 := by nlinarith
  have hm2 : (1 - y) ^ 2 ≤ 81 / 625 := by nlinarith [mul_pos hm (sub_pos.mpr hy)]
  have hgap : (4 / 3 - ell) * (2 - ell) * (1 - y) ^ 2 < y * (5 / 3 - ell) ^ 2 := by
    have h1 := mul_le_mul hbal hm2 (sq_nonneg _) (sq_nonneg _)
    nlinarith [mul_pos (sub_pos.mpr hy) (pow_pos ha 2), pow_pos ha 2]
  have hsq : ((4 / 3 - ell) * (1 - y)) ^ 2 < (X * (5 / 3 - ell)) ^ 2 := by
    have hr := mul_lt_mul_of_pos_right hreserve (pow_pos ha 2)
    have hg := mul_lt_mul_of_pos_left hgap hδ
    have hbsq : (2 - ell) * ((4 / 3 - ell) * (1 - y)) ^ 2 <
        (2 - ell) * (X * (5 / 3 - ell)) ^ 2 := by
      nlinarith
    exact lt_of_mul_lt_mul_left hbsq hb.le
  have hlin : (4 / 3 - ell) * (1 - y) ≤ X * (5 / 3 - ell) := by
    refine le_of_not_gt fun hlt => ?_
    nlinarith [mul_self_lt_mul_self (mul_nonneg hX.le ha.le) hlt]
  have heq : (4 / 3 - ell) * ((1 / 2 - X) / X) * (1 - y) =
      (4 / 3 - ell) * (1 / 2 - X) * (1 - y) / X := by
    ring
  rw [heq, div_le_iff₀ hX]
  nlinarith

/-- Remainder coefficient: the full hole bound gives `LJ * (1 - y) ≤ y`. -/
theorem remainder_price {X t y : ℝ} (ht : 0 < t) (hsum : X + t < 1) (hy0 : 0 ≤ y)
    (hhole : 1 - t ^ 2 - 2 * X * t ≤ y) :
    max (1 / 2 - t) 0 / t * (1 - y) ≤ y := by
  rcases le_total (1 / 2 - t) 0 with hfar | hnear
  · rw [max_eq_right hfar, zero_div, zero_mul]
    exact hy0
  rw [max_eq_left hnear, div_mul_eq_mul_div, div_le_iff₀ ht]
  nlinarith [mul_pos ht (by linarith : (0 : ℝ) < 2 - t - 2 * X)]

/-- Correlated coefficient: unconditionally `LD * (1 - y) ≤ y`; no `LI` fallback
and no head inequality `X > (1 - t) / 2` are needed. -/
theorem correlated_price {X t r y LC LD : ℝ} (hX : 0 < X) (ht : 0 < t)
    (hsum : X + t < 1) (hy : 16 / 25 < y) (hy1 : y < 1) (hr : 0 < r)
    (hr2 : r ^ 2 = t ^ 2 + 2 * X * t) (hhole : 1 - t ^ 2 - 2 * X * t ≤ y)
    (hLC : LC = max (-(1 / 2 - X) * (1 / 2 - t)) 0 / (X * t))
    (hLD : LD = (LC * (r - t) + 1 - t) / r) :
    LD * (1 - y) ≤ y := by
  subst hLD hLC
  have hm : 0 < 1 - y := by linarith
  have hmr : 1 - y ≤ r ^ 2 := by rw [hr2]; linarith
  have hX0 : X ≠ 0 := hX.ne'
  have ht0 : t ≠ 0 := ht.ne'
  have hr0 : r ≠ 0 := hr.ne'
  rcases le_or_gt (-(1 / 2 - X) * (1 / 2 - t)) 0 with hC | hC
  · rw [max_eq_right hC, zero_div, zero_mul, zero_add, div_mul_eq_mul_div, div_le_iff₀ hr]
    have hlin : 1 - y ≤ y * r := by
      refine le_of_not_gt fun hlt => ?_
      have hsq := mul_self_lt_mul_self (mul_nonneg (by linarith) hr.le) hlt
      have h1 := mul_le_mul_of_nonneg_left hmr hm.le
      have h2 := mul_le_mul_of_nonneg_right (by linarith : 1 - y ≤ 9 / 25) (sq_nonneg r)
      have h3 := mul_le_mul_of_nonneg_right (by nlinarith : (9 / 25 : ℝ) ≤ y ^ 2)
        (sq_nonneg r)
      nlinarith
    nlinarith [mul_pos ht hm]
  · rw [max_eq_left hC.le]
    have hrhi : r ^ 2 ≤ 2 * t - t ^ 2 := by
      rw [hr2]
      nlinarith [mul_pos ht (by linarith : (0 : ℝ) < 1 - X - t)]
    have hgain := radical_gain ht hr hrhi hm.le hmr (by linarith)
    have hkey : ((X - 1 / 2) * (1 / 2 - t) * (r - t) + X * t * (1 - t + r)) *
        (2 * (r + t)) = (r ^ 2 + 2 * r * t + 3 * t ^ 2 - t) * X := by
      linear_combination (t - 1 / 2) * hr2
    have hval : (-(1 / 2 - X) * (1 / 2 - t) / (X * t) * (r - t) + 1 - t) / r =
        ((X - 1 / 2) * (1 / 2 - t) * (r - t) + X * t * (1 - t)) / (X * t * r) := by
      field_simp
      ring
    rw [hval, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    refine le_of_not_gt fun hlt => ?_
    have e1 := mul_le_mul_of_nonneg_left hgain hX.le
    have e2 := mul_pos (by linarith : (0 : ℝ) < 2 * (r + t)) (sub_pos.mpr hlt)
    have e3 : ((X - 1 / 2) * (1 / 2 - t) * (r - t) + X * t * (1 - t + r)) *
        (2 * (r + t)) * (1 - y) = (r ^ 2 + 2 * r * t + 3 * t ^ 2 - t) * X * (1 - y) := by
      rw [hkey]
    linarith

/-- Third-cusp high-slope inside-source payment, endpoint `ell = 1` included,
without dividing by `ell - 1`. -/
theorem source_payment {X t y ell q r LI LJ LC LD L : ℝ}
    (hX : 0 < X) (ht : 0 < t) (hsum : X + t < 1)
    (hy : 16 / 25 < y) (hy1 : y < 1) (hell : 1 ≤ ell) (hell4 : ell < 4 / 3)
    (hq : 0 ≤ q) (hqhalf : q < 1 / 2)
    (hreserve : (4 / 3 - ell) * y < (2 - ell) * X ^ 2)
    (hhole : 1 - t ^ 2 - 2 * X * t ≤ y)
    (hr : 0 < r) (hr2 : r ^ 2 = t ^ 2 + 2 * X * t)
    (hLI : LI = max (1 / 2 - X) 0 / X) (hLJ : LJ = max (1 / 2 - t) 0 / t)
    (hLC : LC = max (-(1 / 2 - X) * (1 / 2 - t)) 0 / (X * t))
    (hLD : LD = (LC * (r - t) + 1 - t) / r) (hL : L = max LI (max LJ LD)) :
    L * ((4 / 3 - ell) * (1 - y) - (ell - 1) * q) / 2 ≤
      (4 / 3 - ell) * y / 2 + (ell - 1) / 4 + ell * q / 2 - max (q - 1 / 4) 0 := by
  have hδ : 0 < 4 / 3 - ell := by linarith
  have hI := head_price hell hell4 hX hy hy1 hreserve
  rw [← hLI] at hI
  have hJ0 := remainder_price ht hsum (by linarith) hhole
  rw [← hLJ] at hJ0
  have hJ : (4 / 3 - ell) * LJ * (1 - y) ≤ (4 / 3 - ell) * y + (ell - 1) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hJ0 hδ.le]
  have hD0 := correlated_price hX ht hsum hy hy1 hr hr2 hhole hLC hLD
  have hD : (4 / 3 - ell) * LD * (1 - y) ≤ (4 / 3 - ell) * y + (ell - 1) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hD0 hδ.le]
  have hLI0 : 0 ≤ LI := by
    rw [hLI]
    exact div_nonneg (le_max_right _ _) hX.le
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact le_trans hLI0 (le_max_left _ _)
  have hLall : (4 / 3 - ell) * L * (1 - y) ≤ (4 / 3 - ell) * y + (ell - 1) / 2 := by
    rw [hL]
    rcases max_choice LI (max LJ LD) with h | h <;> rw [h]
    · exact hI
    · rcases max_choice LJ LD with h' | h' <;> rw [h']
      · exact hJ
      · exact hD
  have hW : L * ((4 / 3 - ell) * (1 - y) - (ell - 1) * q) ≤ (4 / 3 - ell) * L * (1 - y) := by
    nlinarith [mul_nonneg hL0 (mul_nonneg (by linarith : (0 : ℝ) ≤ ell - 1) hq)]
  have hqterm : max (q - 1 / 4) 0 ≤ ell * q / 2 :=
    max_le (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ell - 1) hq])
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ell) hq])
  linarith

/-- The same payment with the literal radical `r = √(t^2 + 2Xt)`. -/
theorem source_payment_sqrt {X t y ell q : ℝ} (hX : 0 < X) (ht : 0 < t)
    (hsum : X + t < 1) (hy : 16 / 25 < y) (hy1 : y < 1)
    (hell : 1 ≤ ell) (hell4 : ell < 4 / 3) (hq : 0 ≤ q) (hqhalf : q < 1 / 2)
    (hreserve : (4 / 3 - ell) * y < (2 - ell) * X ^ 2)
    (hhole : 1 - t ^ 2 - 2 * X * t ≤ y) :
    max (max (1 / 2 - X) 0 / X) (max (max (1 / 2 - t) 0 / t)
        ((max (-(1 / 2 - X) * (1 / 2 - t)) 0 / (X * t) *
            (Real.sqrt (t ^ 2 + 2 * X * t) - t) + 1 - t) /
          Real.sqrt (t ^ 2 + 2 * X * t))) *
        ((4 / 3 - ell) * (1 - y) - (ell - 1) * q) / 2 ≤
      (4 / 3 - ell) * y / 2 + (ell - 1) / 4 + ell * q / 2 - max (q - 1 / 4) 0 := by
  have hpos : 0 < t ^ 2 + 2 * X * t := by positivity
  exact source_payment (r := Real.sqrt (t ^ 2 + 2 * X * t)) hX ht hsum hy hy1 hell
    hell4 hq hqhalf hreserve hhole (Real.sqrt_pos.2 hpos) (Real.sq_sqrt hpos.le)
    rfl rfl rfl rfl rfl

end Erdos1017.CuspThreeHighSourcePayment
