module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Payment for the fourth-cusp inside source

The normalized fourth-cusp inside-source payment `P(q)` is nonnegative on the
closed budget interval, including the kink at `q = 1/4`, with the shifted price
paid in the chart `X ≥ 1/2 ≥ t` and the correlated price bounded by `1/8`.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CuspFourSourcePeakPayment

/-- A three-way price maximum pays a common bound when each price does. -/
theorem max3_mul_le {a b d c v : ℝ}
    (ha : a * c ≤ v) (hb : b * c ≤ v) (hd : d * c ≤ v) : max a (max b d) * c ≤ v := by
  rcases le_total b d with h1 | h1
  · rw [max_eq_right h1]
    rcases le_total a d with h2 | h2
    · rw [max_eq_right h2]; exact hd
    · rw [max_eq_left h2]; exact ha
  · rw [max_eq_left h1]
    rcases le_total a b with h2 | h2
    · rw [max_eq_right h2]; exact hb
    · rw [max_eq_left h2]; exact ha

set_option maxHeartbeats 800000 in
/-- In the chart `X ≥ 1/2 ≥ t`, with `2Xt = r^2 - t^2`, the shifted price
`LD + 1 = N / (2tr(r+t))` is paid by any `s ≤ min(r^2, 3/5)`. -/
theorem chart_payment {t r s : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) (hr : 0 < r)
    (hlow : t + t ^ 2 ≤ r ^ 2) (hhigh : r ^ 2 ≤ 2 * t - t ^ 2)
    (hs : s ≤ r ^ 2) (hs35 : s ≤ 3 / 5) :
    4 * s * (r ^ 2 + 2 * r * t + 3 * t ^ 2 - t) ≤ 9 * t * r * (r + t) := by
  have hN : 0 ≤ r ^ 2 + 2 * r * t + 3 * t ^ 2 - t := by
    nlinarith [mul_nonneg hr.le ht.le, sq_nonneg t]
  rcases le_total t (3 / 8) with ht38 | ht38
  · obtain ⟨R, hRdef⟩ : ∃ R, R = Real.sqrt (2 * t - t ^ 2) := ⟨_, rfl⟩
    have hR0 : 0 ≤ R := by rw [hRdef]; exact Real.sqrt_nonneg _
    have hR2 : R ^ 2 = 2 * t - t ^ 2 := by
      rw [hRdef]; exact Real.sq_sqrt ((sq_nonneg r).trans hhigh)
    have hrR : r ≤ R := (sq_le_sq₀ hr.le hR0).1 (by rw [hR2]; exact hhigh)
    have h0 : (0 : ℝ) ≤ 3 / 8 - t := by linarith
    have hcubic : 0 ≤ 25 - 117 * t + 160 * t ^ 2 - 64 * t ^ 3 := by
      nlinarith [pow_nonneg h0 3, mul_nonneg ht.le (sq_nonneg (3 / 8 - t)),
        mul_nonneg (sq_nonneg t) h0, pow_nonneg ht.le 3]
    have hRsq : (t * (7 - 8 * t)) ^ 2 ≤ (R * (5 - 8 * t)) ^ 2 := by
      have he : (R * (5 - 8 * t)) ^ 2 = (2 * t - t ^ 2) * (5 - 8 * t) ^ 2 := by
        rw [mul_pow, hR2]
      rw [he]
      nlinarith [mul_nonneg ht.le hcubic]
    have hlhs : 0 ≤ t * (7 - 8 * t) := mul_nonneg ht.le (by linarith)
    have hrhs : 0 ≤ R * (5 - 8 * t) := mul_nonneg hR0 (by linarith)
    have hRF : t * (7 - 8 * t) ≤ R * (5 - 8 * t) := (sq_le_sq₀ hlhs hrhs).1 hRsq
    have hR3 : R ^ 3 = R * (2 * t - t ^ 2) := by rw [← hR2]; ring
    have hR2t : R ^ 2 * t = (2 * t - t ^ 2) * t := by rw [hR2]
    have hFR : 4 * R ^ 3 + 8 * R ^ 2 * t + 12 * R * t ^ 2 - 13 * R * t - 9 * t ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hRF)]
    have hW : 0 ≤ 4 * r * R * (r + R) + 4 * t * (r ^ 2 + 3 * r * R + R ^ 2) +
        8 * t ^ 2 * (r + R) + 12 * t ^ 3 - 4 * t ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hr.le hR0) (add_nonneg hr.le hR0),
        mul_nonneg ht.le (sq_nonneg r), mul_nonneg (mul_nonneg ht.le hr.le) hR0,
        mul_nonneg (sq_nonneg t) (add_nonneg hr.le hR0), pow_nonneg ht.le 3,
        mul_nonneg (sq_nonneg t) (by linarith : (0 : ℝ) ≤ 1 - t)]
    have hF : 4 * r ^ 3 + 8 * r ^ 2 * t + 12 * r * t ^ 2 - 13 * r * t - 9 * t ^ 2 ≤ 0 := by
      have hmono := mul_nonneg (sub_nonneg.mpr hrR) hW
      have hFRt := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ r + t) hFR
      have hpos : 0 < R + t := by linarith
      by_contra! hcon
      have hprod := mul_pos hcon hpos
      linarith [hmono, hFRt, hprod]
    have hsN := mul_le_mul_of_nonneg_right hs hN
    have hrF := mul_nonpos_of_nonneg_of_nonpos hr.le hF
    linarith [hsN, hrF]
  · rcases le_total (r ^ 2) (3 / 5) with hr35 | hr35
    · have hr45 : r ≤ 4 / 5 := by nlinarith [sq_nonneg (r - 4 / 5)]
      have ha : 0 ≤ 13 * t - 12 * t ^ 2 - 4 * r ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ht38) (sub_nonneg.mpr ht2)]
      have hc : 0 ≤ 3 + 15 * t ^ 2 - 33 / 4 * t := by nlinarith [sq_nonneg (t - 11 / 40)]
      have hF : 4 * r ^ 3 + 8 * r ^ 2 * t + 12 * r * t ^ 2 - 13 * r * t - 9 * t ^ 2 ≤ 0 := by
        nlinarith [mul_nonneg (mul_nonneg hr.le (sub_nonneg.mpr hr45)) ha,
          mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr35), mul_nonneg (sub_nonneg.mpr hr35) hc]
      have hsN := mul_le_mul_of_nonneg_right hs hN
      have hrF := mul_nonpos_of_nonneg_of_nonpos hr.le hF
      linarith [hsN, hrF]
    · have hsN := mul_le_mul_of_nonneg_right hs35 hN
      have hc2 : 0 ≤ 225 / 8 * t ^ 2 + 30 * t - 12 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ht38) ht.le]
      have hG : 0 ≤ (45 * t - 12) * r ^ 2 + (45 * t ^ 2 - 24 * t) * r + 12 * t - 36 * t ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg ht.le (by linarith : (0 : ℝ) ≤ 24 - 45 * t))
            (sq_nonneg (r - 4 / 5)),
          mul_nonneg hc2 (sub_nonneg.mpr hr35),
          mul_nonneg (sub_nonneg.mpr ht38) (sub_nonneg.mpr ht2)]
      linarith [hsN, hG]

set_option maxHeartbeats 800000 in
/-- The correlated price satisfies `LD (1-y) - y ≤ 1/8` on the whole normalized
inside-source domain; no fallback to `LI` is needed. -/
theorem correlated_le {X t y r LC LD : ℝ} (hX : 0 < X) (ht : 0 < t) (hsum : X + t < 1)
    (hhead : (1 - t) / 2 < X) (hy : 2 / 5 < y) (hy1 : y < 1)
    (hsquare : 1 - t ^ 2 - 2 * X * t ≤ y) (hr : 0 < r) (hr2 : r ^ 2 = t ^ 2 + 2 * X * t)
    (hLC : LC * (X * t) = max (-(1 / 2 - X) * (1 / 2 - t)) 0)
    (hLD : LD * r = LC * (r - t) + 1 - t) :
    LD * (1 - y) ≤ y + 1 / 8 := by
  have hrt : t ≤ r := (sq_le_sq₀ ht.le hr.le).1 (by nlinarith [mul_pos hX ht])
  rcases le_total X (1 / 2) with hX12 | hX12
  · rcases le_total t (1 / 2) with ht12 | ht12
    · have hprod : -(1 / 2 - X) * (1 / 2 - t) ≤ 0 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hX12) (sub_nonneg.mpr ht12)]
      rw [max_eq_right hprod] at hLC
      have hLC0 : LC = 0 := (mul_eq_zero.mp hLC).resolve_right (mul_pos hX ht).ne'
      rw [hLC0, zero_mul, zero_add] at hLD
      have hgap : 0 ≤ 1 - r ^ 2 - (1 - t) ^ 2 := by
        nlinarith [mul_pos ht (by linarith : (0 : ℝ) < 1 - t - X)]
      have hc1 := mul_nonneg hgap (sq_nonneg (1 - y))
      have hc2 := mul_nonneg (by linarith : (0 : ℝ) ≤ r ^ 2 - (1 - y))
        (add_nonneg (sq_nonneg (1 - y)) (sq_nonneg (y + 1 / 8)))
      have hc3 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - y)
        (by nlinarith [sq_nonneg (y - 2 / 5)] : (0 : ℝ) ≤ 2 * y ^ 2 - 3 / 4 * y + 1 / 64)
      have hlhs : 0 ≤ (1 - t) * (1 - y) := mul_nonneg (by linarith) (by linarith)
      have hrhs : 0 ≤ r * (y + 1 / 8) := mul_nonneg hr.le (by linarith)
      have hkey : (1 - t) * (1 - y) ≤ r * (y + 1 / 8) :=
        (sq_le_sq₀ hlhs hrhs).1 (by nlinarith [hc1, hc2, hc3])
      have he : LD * (1 - y) * r = (1 - t) * (1 - y) := by rw [← hLD]; ring
      by_contra! hcon
      have hm := mul_lt_mul_of_pos_right hcon hr
      linarith [hm, he, hkey]
    · have hprod : 0 ≤ -(1 / 2 - X) * (1 / 2 - t) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hX12) (sub_nonneg.mpr ht12)]
      rw [max_eq_left hprod] at hLC
      have hrX : r ≤ t + X := (sq_le_sq₀ hr.le (by linarith)).1 (by nlinarith [sq_nonneg X])
      have he : LD * (r * (r + t)) =
          2 * (-(1 / 2 - X) * (1 / 2 - t)) + (1 - t) * (r + t) := by
        linear_combination (r + t) * hLD + LC * hr2 + 2 * hLC
      have hb : 8 * (2 * (-(1 / 2 - X) * (1 / 2 - t)) + (1 - t) * (r + t)) ≤
          7 * (r * (r + t)) := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 15 * t - 15 / 2) (sub_nonneg.mpr hrt),
          mul_nonneg (by linarith : (0 : ℝ) ≤ 30 * t - 17 / 2)
            (by linarith : (0 : ℝ) ≤ X - (1 - t) / 2),
          mul_nonneg (sub_nonneg.mpr ht12) (by linarith : (0 : ℝ) ≤ 15 * t + 11 / 4)]
      have hP : 0 < r * (r + t) := by positivity
      have hLD78 : LD ≤ 7 / 8 := by
        by_contra! hcon
        linarith [mul_lt_mul_of_pos_right hcon hP]
      nlinarith [mul_le_mul_of_nonneg_right hLD78 (by linarith : (0 : ℝ) ≤ 1 - y)]
  · have ht12 : t < 1 / 2 := by linarith
    have hprod : 0 ≤ -(1 / 2 - X) * (1 / 2 - t) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hX12) (by linarith : (0 : ℝ) ≤ 1 / 2 - t)]
    rw [max_eq_left hprod] at hLC
    have hN : (LD + 1) * (2 * t * r * (r + t)) = r ^ 2 + 2 * r * t + 3 * t ^ 2 - t := by
      linear_combination (2 * t * (r + t)) * hLD + (4 * t) * hLC +
        (2 * t * LC + 2 * t - 1) * hr2
    have hchart := chart_payment (s := 1 - y) ht ht12.le hr
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hX12) ht.le])
      (by nlinarith [mul_pos ht (by linarith : (0 : ℝ) < 1 - t - X)])
      (by linarith) (by linarith)
    have hP : 0 < 2 * t * r * (r + t) := by positivity
    have he : (LD + 1) * (1 - y) * (2 * t * r * (r + t)) =
        (1 - y) * (r ^ 2 + 2 * r * t + 3 * t ^ 2 - t) := by rw [← hN]; ring
    by_contra! hcon
    have hm := mul_lt_mul_of_pos_right (show 9 / 8 < (LD + 1) * (1 - y) by linarith) hP
    linarith [hm, he, hchart]

set_option maxHeartbeats 800000 in
/-- The normalized fourth-cusp inside-source payment `P(q) ≥ 0` on the closed budget
interval `0 ≤ q ≤ min(rho (1-y), 5y/2 - 1)`, including the kink at `q = 1/4`. -/
theorem payment_nonneg {X t y rho q r LI LJ LC LD L : ℝ}
    (hX : 0 < X) (ht : 0 < t) (hsum : X + t < 1) (hhead : (1 - t) / 2 < X)
    (hy : 2 / 5 < y) (hy1 : y < 1) (hrho : 0 < rho) (hrho4 : rho < 4)
    (hq : 0 ≤ q) (hqmax : q ≤ rho * (1 - y)) (hqH : q ≤ 5 / 2 * y - 1)
    (hreserve : rho * y < (1 + 2 * rho) * X ^ 2) (hsquare : 1 - t ^ 2 - 2 * X * t ≤ y)
    (hr : 0 < r) (hr2 : r ^ 2 = t ^ 2 + 2 * X * t)
    (hLI : LI = max (1 / 2 - X) 0 / X) (hLJ : LJ = max (1 / 2 - t) 0 / t)
    (hLC : LC = max (-(1 / 2 - X) * (1 / 2 - t)) 0 / (X * t))
    (hLD : LD = (LC * (r - t) + 1 - t) / r) (hL : L = max LI (max LJ LD)) :
    0 ≤ rho * y + 1 / 2 + (3 + 2 * rho) * q - 4 * (1 + rho) * max (q - 1 / 4) 0 -
      L * (rho * (1 - y) - q) := by
  have hXt : 0 < X * t := mul_pos hX ht
  have hLIX : LI * X = max (1 / 2 - X) 0 := by rw [hLI]; exact div_mul_cancel₀ _ hX.ne'
  have hLJt : LJ * t = max (1 / 2 - t) 0 := by rw [hLJ]; exact div_mul_cancel₀ _ ht.ne'
  have hLCXt : LC * (X * t) = max (-(1 / 2 - X) * (1 / 2 - t)) 0 := by
    rw [hLC]; exact div_mul_cancel₀ _ hXt.ne'
  have hLDr : LD * r = LC * (r - t) + 1 - t := by rw [hLD]; exact div_mul_cancel₀ _ hr.ne'
  have h6 := correlated_le hX ht hsum hhead hy hy1 hsquare hr hr2 hLCXt hLDr
  have hLI0 : 0 ≤ LI := by rw [hLI]; exact div_nonneg (le_max_right _ _) hX.le
  have hL0 : 0 ≤ L := by rw [hL]; exact hLI0.trans (le_max_left _ _)
  have hXlow : rho * (1 - y) ≤ X * (1 + 2 * rho) := by
    by_contra! hcon
    have h0 : 0 ≤ X * (1 + 2 * rho) := by positivity
    have h1 := mul_le_mul hcon.le hcon.le h0 (h0.trans hcon.le)
    have h2 := mul_lt_mul_of_pos_left hreserve (by linarith : (0 : ℝ) < 1 + 2 * rho)
    have hq4 : 0 < 4 * y - 1 - y ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hy) (sub_pos.mpr hy1)]
    have h3 := mul_pos hrho (add_pos (by linarith : (0 : ℝ) < y) (mul_pos hrho hq4))
    nlinarith [h1, h2, h3]
  have hAI : LI * (rho * (1 - y)) ≤ rho * y + 1 / 2 := by
    rcases le_total (1 / 2 - X) 0 with hneg | hpos
    · rw [max_eq_right hneg] at hLIX
      rw [(mul_eq_zero.mp hLIX).resolve_right hX.ne']
      nlinarith [mul_pos hrho (by linarith : (0 : ℝ) < y)]
    · rw [max_eq_left hpos] at hLIX
      have he : LI * (rho * (1 - y)) * X = (1 / 2 - X) * (rho * (1 - y)) := by
        rw [← hLIX]; ring
      by_contra! hcon
      nlinarith [mul_lt_mul_of_pos_right hcon hX, he, hXlow]
  have hJ1 : LJ * (1 - y) ≤ y := by
    rcases le_total (1 / 2 - t) 0 with hneg | hpos
    · rw [max_eq_right hneg] at hLJt
      rw [(mul_eq_zero.mp hLJt).resolve_right ht.ne']
      linarith
    · rw [max_eq_left hpos] at hLJt
      have he : LJ * (1 - y) * t = (1 / 2 - t) * (1 - y) := by rw [← hLJt]; ring
      by_contra! hcon
      nlinarith [mul_lt_mul_of_pos_right hcon ht, he,
        mul_nonneg ht.le (by linarith : (0 : ℝ) ≤ 2 - t - 2 * X)]
  have hAJ : LJ * (rho * (1 - y)) ≤ rho * y + 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hJ1 hrho.le]
  have hAD : LD * (rho * (1 - y)) ≤ rho * y + 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h6 hrho.le]
  have hB0 : 0 ≤ rho * (1 - y) - q := by linarith
  rcases le_total q (1 / 4) with hq4 | hq4
  · rw [max_eq_right (by linarith : q - 1 / 4 ≤ 0)]
    have hA : L * (rho * (1 - y)) ≤ rho * y + 1 / 2 := by
      rw [hL]; exact max3_mul_le hAI hAJ hAD
    nlinarith [mul_nonneg hL0 hq, mul_nonneg (by linarith : (0 : ℝ) ≤ 3 + 2 * rho) hq]
  · rw [max_eq_left (by linarith : 0 ≤ q - 1 / 4)]
    have hBI : LI * (1 - y) ≤ y + 1 / 8 := by
      rcases le_total (1 / 2 - X) 0 with hneg | hpos
      · rw [max_eq_right hneg] at hLIX
        rw [(mul_eq_zero.mp hLIX).resolve_right hX.ne']
        linarith
      · rw [max_eq_left hpos] at hLIX
        have he : LI * (1 - y) * X = (1 / 2 - X) * (1 - y) := by rw [← hLIX]; ring
        by_contra! hcon
        nlinarith [mul_lt_mul_of_pos_right hcon hX, he]
    have hB : L * (1 - y) ≤ y + 1 / 8 := by
      rw [hL]; exact max3_mul_le hBI (by linarith) h6
    have hLB := mul_le_mul_of_nonneg_right hB hB0
    have hW : 0 ≤ 3 / 2 * (1 - y) + q * (2 * y - 7 / 8) + rho * (1 - y) * (7 / 8 - 2 * q) := by
      rcases le_total q (7 / 16) with hq716 | hq716
      · linarith [mul_nonneg (mul_nonneg hrho.le (by linarith : (0 : ℝ) ≤ 1 - y))
            (by linarith : (0 : ℝ) ≤ 7 / 8 - 2 * q),
          mul_nonneg hq (by linarith : (0 : ℝ) ≤ 2 * y - 7 / 8)]
      · have h4 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - rho)
          (by linarith : (0 : ℝ) ≤ 1 - y)) (by linarith : (0 : ℝ) ≤ 2 * q - 7 / 8)
        rcases le_total (71 / 8) (10 * y) with hy71 | hy71
        · linarith [h4, mul_nonneg hq (by linarith : (0 : ℝ) ≤ 10 * y - 71 / 8)]
        · linarith [h4, sq_nonneg (y - 119 / 160),
            mul_nonneg (by linarith : (0 : ℝ) ≤ 5 / 2 * y - 1 - q)
              (by linarith : (0 : ℝ) ≤ 71 / 8 - 10 * y)]
    by_contra! hcon
    have hm := mul_neg_of_pos_of_neg (by linarith : (0 : ℝ) < 1 - y) hcon
    linarith [hm, hLB, hW]

/-- The same payment with the literal radical `r = √(t^2 + 2Xt)`. -/
theorem payment_nonneg_sqrt {X t y rho q : ℝ}
    (hX : 0 < X) (ht : 0 < t) (hsum : X + t < 1) (hhead : (1 - t) / 2 < X)
    (hy : 2 / 5 < y) (hy1 : y < 1) (hrho : 0 < rho) (hrho4 : rho < 4)
    (hq : 0 ≤ q) (hqmax : q ≤ rho * (1 - y)) (hqH : q ≤ 5 / 2 * y - 1)
    (hreserve : rho * y < (1 + 2 * rho) * X ^ 2) (hsquare : 1 - t ^ 2 - 2 * X * t ≤ y) :
    0 ≤ rho * y + 1 / 2 + (3 + 2 * rho) * q - 4 * (1 + rho) * max (q - 1 / 4) 0 -
      max (max (1 / 2 - X) 0 / X) (max (max (1 / 2 - t) 0 / t)
          ((max (-(1 / 2 - X) * (1 / 2 - t)) 0 / (X * t) *
              (Real.sqrt (t ^ 2 + 2 * X * t) - t) + 1 - t) /
            Real.sqrt (t ^ 2 + 2 * X * t))) *
        (rho * (1 - y) - q) := by
  have hpos : 0 < t ^ 2 + 2 * X * t := by positivity
  exact payment_nonneg (r := Real.sqrt (t ^ 2 + 2 * X * t)) hX ht hsum hhead hy hy1 hrho
    hrho4 hq hqmax hqH hreserve hsquare (Real.sqrt_pos.2 hpos) (Real.sq_sqrt hpos.le)
    rfl rfl rfl rfl rfl

end Erdos1017.CuspFourSourcePeakPayment
