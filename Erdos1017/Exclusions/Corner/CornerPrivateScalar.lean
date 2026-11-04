module

public import Erdos1017.Benchmark.BenchmarkFamilyGuards

/-!
# Scalar exclusion of the private corner sectors

The correlated corner tangent and the private trace give the same triangle
margin on both sides of the partner/intercept comparison, and the small-partner,
large-partner and saturated sectors are each excluded on the correlated corner
rectangle.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.CornerPrivateScalar

private theorem tangent_eq (h : ℝ) :
    Benchmark.mixedTangent (117 / 100) (h / 2) =
      217 / 702 * h + 4640687 / 89356878 := by
  norm_num [Benchmark.mixedTangent, Benchmark.mixedValue, Benchmark.mixedDensity,
    Benchmark.mixedDenominator]
  ring

private theorem rectangle_guards {h delta : ℝ}
    (hh : h ∈ Icc (23 / 100 : ℝ) (467 / 2000))
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (226 / 589)) :
    123 / 1000 < Benchmark.mixedTangent (117 / 100) (h / 2) ∧
      57 / 1000 < 2 * Benchmark.mixedTangent (117 / 100) (h / 2) - (1 - delta) * h ∧
      7 / 500 < 2 * Benchmark.mixedTangent (117 / 100) (h / 2) - h ∧
      79 / 100 * delta <
        3 * (2 * Benchmark.mixedTangent (117 / 100) (h / 2) - (1 - delta) * h) ∧
      2 * Benchmark.mixedTangent (117 / 100) (h / 2) - (1 - delta) * h < 1 / 2 := by
  rw [tangent_eq]
  have hll := mul_nonneg (sub_nonneg.mpr hdelta.1) (sub_nonneg.mpr hh.1)
  have hlu := mul_nonneg (sub_nonneg.mpr hdelta.1) (sub_nonneg.mpr hh.2)
  have hul := mul_nonneg (sub_nonneg.mpr hdelta.2) (sub_nonneg.mpr hh.1)
  have huu := mul_nonneg (sub_nonneg.mpr hdelta.2) (sub_nonneg.mpr hh.2)
  refine ⟨by linarith [hh.1], ?_, by linarith [hh.2], ?_, ?_⟩ <;>
    nlinarith [hh.1, hh.2, hdelta.1, hdelta.2]

private theorem alpha_lt_radius {A b h : ℝ}
    (hh : h ≤ (467 / 2000 : ℝ)) (hA : (1 / 3 : ℝ) < A) (hb : 0 ≤ b)
    (hbody : (A + b) ^ 2 ≤ h) : A + b < 121 / 250 := by
  nlinarith

/-- The correlated corner tangent and actual private trace give the same
triangle margin on both sides of the partner/intercept comparison. -/
theorem triangle_margin {A b k h delta c : ℝ}
    (hh : h ∈ Icc (23 / 100 : ℝ) (467 / 2000))
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (226 / 589))
    (hA : 1 / 3 < A) (hb : 0 ≤ b) (hk : 0 ≤ k)
    (hc : Benchmark.mixedTangent (117 / 100) (h / 2) < c)
    (hbody : (A + b) ^ 2 ≤ h)
    (htrace : b ≤ 2 * c - (1 - delta) * h →
      2 * (A + b) ^ 2 + (A + (2 * c - (1 - delta) * h) - b) ^ 2 + 4 * b * k ≤
        2 * h) :
    2 * delta * A < 3 * (2 * c - (1 - delta) * h) := by
  let gamma := 2 * c - (1 - delta) * h
  have hguards := rectangle_guards hh hdelta
  have hfloor : 2 * Benchmark.mixedTangent (117 / 100) (h / 2) -
      (1 - delta) * h < gamma := by dsimp only [gamma]; linarith only [hc]
  have hd : 0 < delta := by linarith [hdelta.1]
  have hA0 : 0 ≤ A := by linarith
  by_cases hbg : b ≤ gamma
  · have ht := htrace hbg
    have hterm : A ^ 2 ≤ (A + gamma - b) ^ 2 := by
      nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hbg)]
    have hmass : A ^ 2 ≤ (A + b) ^ 2 := by nlinarith [mul_nonneg hA0 hb]
    have hsmall : A < (79 / 200 : ℝ) := by
      change 2 * (A + b) ^ 2 + (A + gamma - b) ^ 2 + 4 * b * k ≤ 2 * h at ht
      nlinarith [hh.2, mul_nonneg hb hk]
    have hmargin : (79 / 100 : ℝ) * delta < 3 * gamma := by
      linarith only [hguards.2.2.2.1, hfloor]
    change 2 * delta * A < 3 * gamma
    nlinarith [mul_pos hd (sub_pos.mpr hsmall)]
  · have hbg : gamma < b := lt_of_not_ge hbg
    have hcap := alpha_lt_radius hh.2 hA hb hbody
    have hlinear : 7 / 500 + 23 / 100 * delta < gamma := by
      have hp := mul_nonneg hd.le (sub_nonneg.mpr hh.1)
      nlinarith only [hguards.2.2.1, hfloor, hp]
    have hp := mul_pos (show 0 < 3 + 2 * delta by linarith) (sub_pos.mpr hlinear)
    have ha := mul_pos hd (show 0 < 121 / 250 - A - gamma by linarith)
    change 2 * delta * A < 3 * gamma
    nlinarith [sq_nonneg (delta - 25 / 92)]

/-- The small-partner trace and unsaturated physical quota conflict on
the correlated tangent rectangle, including the partner/intercept boundary. -/
theorem unsaturated_small_b_false {A b k h delta c : ℝ}
    (hh : h ∈ Icc (23 / 100 : ℝ) (467 / 2000))
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (226 / 589))
    (hA : 1 / 3 < A) (hb : 0 ≤ b) (hk : 0 ≤ k)
    (hc : Benchmark.mixedTangent (117 / 100) (h / 2) < c)
    (hbody : (A + b) ^ 2 ≤ h)
    (hbg : b ≤ 2 * c - (1 - delta) * h)
    (htrace : 2 * (A + b) ^ 2 +
      (A + (2 * c - (1 - delta) * h) - b) ^ 2 + 4 * b * k ≤ 2 * h)
    (hdemand : 2 * c ≤ (A + b) * (1 - A - b) - b * k) : False := by
  let alpha := A + b
  let B0 := Benchmark.mixedTangent (117 / 100) (h / 2)
  let g0 := 2 * B0 - (1 - delta) * h
  let z := 2 / 3 - alpha + g0
  let L := alpha * (1 - alpha) - 2 * B0
  have hguards := rectangle_guards hh hdelta
  have halpha : (1 / 3 : ℝ) ≤ alpha := by dsimp only [alpha]; linarith
  have halpha' : alpha < (1 / 2 : ℝ) := by
    have h := alpha_lt_radius hh.2 hA hb hbody
    dsimp only [alpha]
    linarith
  have hg0 : 0 < g0 := by dsimp only [g0, B0]; linarith [hguards.2.1]
  have hz : 0 < z := by dsimp only [z]; linarith
  have hactual : 0 ≤ A + (2 * c - (1 - delta) * h) - b := by linarith
  have hcompare : z ≤ A + (2 * c - (1 - delta) * h) - b := by
    dsimp only [z, alpha, g0, B0]
    linarith
  have hsquare := mul_nonneg (sub_nonneg.mpr hcompare) (show
      0 ≤ A + (2 * c - (1 - delta) * h) - b + z by linarith)
  have hT : 2 * alpha ^ 2 + z ^ 2 - 2 * h ≤ 0 := by
    dsimp only [alpha]
    nlinarith [mul_nonneg hb hk]
  have hL : 0 < L := by
    dsimp only [L, alpha, B0]
    nlinarith only [hc, hdemand, mul_nonneg hb hk]
  let zL := 2 / 3 - alpha + (2 * B0 - (9 / 11) * h)
  let Bmin := Benchmark.mixedTangent (117 / 100) ((23 / 100) / 2)
  let zmin := 2 / 3 - alpha + (2 * Bmin - (9 / 11) * (23 / 100))
  have hLguards := rectangle_guards hh
    (by norm_num : (2 / 11 : ℝ) ∈ Icc (2 / 11 : ℝ) (226 / 589))
  have hmin := rectangle_guards
    (by norm_num : (23 / 100 : ℝ) ∈ Icc (23 / 100 : ℝ) (467 / 2000))
    (by norm_num : (2 / 11 : ℝ) ∈ Icc (2 / 11 : ℝ) (226 / 589))
  have hzL : 0 < zL := by dsimp only [zL, B0]; linarith [hLguards.2.1]
  have hzmin : 0 < zmin := by dsimp only [zmin, Bmin]; linarith [hmin.2.1]
  have hzLupper : zL ≤ 5 / 6 := by
    dsimp only [zL, B0]
    linarith [hLguards.2.2.2.2]
  have hzminupper : zmin ≤ 5 / 6 := by
    dsimp only [zmin, Bmin]
    linarith [hmin.2.2.2.2]
  have hzorder : zL ≤ z := by
    have hp := mul_nonneg (sub_nonneg.mpr hdelta.1) (show 0 ≤ h by linarith [hh.1])
    dsimp only [zL, z, g0]
    nlinarith only [hp]
  have hsquares : zL ^ 2 ≤ z ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hzorder) (show 0 ≤ z + zL by linarith)]
  have hcoefficient : 0 < (zL + zmin) * (217 / 351 - 9 / 11) - 2 + 7 * (217 / 351) := by
    linarith only [hzLupper, hzminupper]
  have hdifference :
      (2 * alpha ^ 2 + zL ^ 2 - 2 * h - 7 * L) -
        (2 * alpha ^ 2 + zmin ^ 2 - 2 * (23 / 100) -
          7 * (alpha * (1 - alpha) - 2 * Bmin)) =
      (h - 23 / 100) *
        ((zL + zmin) * (217 / 351 - 9 / 11) - 2 + 7 * (217 / 351)) := by
    dsimp only [zL, zmin, L, B0, Bmin]
    rw [tangent_eq, tangent_eq]
    ring
  have hbase : 0 < 2 * alpha ^ 2 + zmin ^ 2 - 2 * (23 / 100) -
      7 * (alpha * (1 - alpha) - 2 * Bmin) := by
    have hid : 2 * alpha ^ 2 + zmin ^ 2 - 2 * (23 / 100) -
        7 * (alpha * (1 - alpha) - 2 * Bmin) =
        10 * (alpha - 11534488387 / 27303490500) ^ 2 +
          67716218641374307 / 24849353116119675000 := by
      dsimp only [zmin, Bmin]
      rw [tangent_eq]
      ring
    rw [hid]
    positivity
  have hdiff := mul_nonneg (sub_nonneg.mpr hh.1) hcoefficient.le
  linarith only [hdifference, hdiff, hbase, hsquares, hT, hL]

/-- The large-partner unsaturated quota makes the hole too small for
the actual covariance inequality, with all original signs retained. -/
theorem unsaturated_large_b_false {A b k h delta c : ℝ}
    (hh : h ∈ Icc (23 / 100 : ℝ) (467 / 2000))
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (226 / 589))
    (hA : 1 / 3 < A)
    (hbg : 2 * c - (1 - delta) * h < b) (hk : 0 < k)
    (hc : Benchmark.mixedTangent (117 / 100) (h / 2) < c)
    (hbody : (A + b) ^ 2 ≤ h)
    (hdemand : 2 * c ≤ (A + b) * (1 - A - b) - b * k)
    (hcov : (A + b + k - h) ^ 2 <
      2 * (2 * c - (1 - delta) * h + 1 - delta) * k * (A + k)) : False := by
  have hguards := rectangle_guards hh hdelta
  have hc0 : (123 / 1000 : ℝ) < c := hguards.1.trans hc
  have hgamma : (57 / 1000 : ℝ) < 2 * c - (1 - delta) * h := by
    linarith only [hguards.2.1, hc]
  have hb : 0 < b := by linarith
  have hcap := alpha_lt_radius hh.2 hA hb.le hbody
  have halpha : A + b < (1 / 2 : ℝ) := by linarith
  have hlow : (109 / 250 : ℝ) < A + b := by
    by_contra hn
    have hp := mul_nonneg (show 0 ≤ 109 / 250 - (A + b) by linarith)
      (show 0 ≤ 1 - 109 / 250 - (A + b) by linarith)
    nlinarith [mul_pos hb hk]
  have hbk : b * k < (1 / 250 : ℝ) := by
    nlinarith only [hdemand, hc0, sq_nonneg (A + b - 1 / 2)]
  have hsmall : k < (4 / 57 : ℝ) := by
    have hp := mul_pos hk (show 0 < b - 57 / 1000 by linarith)
    nlinarith only [hp, hbk]
  have hnu : 2 * c - (1 - delta) * h + 1 - delta ≤ (22 / 25 : ℝ) := by
    have hp := mul_nonneg (sub_nonneg.mpr hdelta.1) (show 0 ≤ 1 - h by linarith [hh.2])
    nlinarith [hh.1, hdemand, mul_pos hb hk, sq_nonneg (A + b - 1 / 2)]
  have hleft : (81 / 400 + k) ^ 2 < (A + b + k - h) ^ 2 := by
    have hp := mul_pos (show 0 < A + b - h - 81 / 400 by linarith [hh.2])
      (show 0 < A + b - h + 81 / 400 + 2 * k by linarith [hh.2])
    nlinarith only [hp]
  have hright : 2 * (2 * c - (1 - delta) * h + 1 - delta) * k * (A + k) ≤
      (44 / 25 : ℝ) * k * (1 / 2 + k) := by
    have hp := mul_nonneg (sub_nonneg.mpr hnu)
      (show 0 ≤ k * (A + k) by positivity)
    have hq := mul_nonneg (show 0 ≤ (44 / 25 : ℝ) * k by positivity)
      (show 0 ≤ 1 / 2 - A by linarith)
    nlinarith only [hp, hq]
  have hsq : k ^ 2 ≤ (4 / 57 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ 4 / 57 - k by linarith)
      (show 0 ≤ 4 / 57 + k by positivity)]
  nlinarith only [hleft.trans (hcov.trans_le hright), hsq, hsmall]

private theorem cubic_positive {k K C : ℝ}
    (hk : 0 ≤ k) (hK : k ≤ K) (ha : 4 / 3 - C ≤ -3 * K)
    (hb : 2 * (7789 / 66000 : ℝ) - C / 3 < 0)
    (hend : 0 < (K + 7789 / 66000) ^ 2 - (C - K) * K * (K + 1 / 3)) :
    0 < (k + 7789 / 66000) ^ 2 - (C - k) * k * (k + 1 / 3) := by
  have hK0 : 0 ≤ K := hk.trans hK
  have hsq : k ^ 2 ≤ K ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hK) (add_nonneg hK0 hk)]
  have hcross : k * K ≤ K ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hK) hK0]
  have hp := mul_nonneg (show 0 ≤ -(4 / 3 - C) - 3 * K by linarith)
    (add_nonneg hk hK0)
  have hq := mul_nonneg hK0 hk
  have hbracket : 0 < -(k ^ 2 + k * K + K ^ 2) -
      (4 / 3 - C) * (k + K) - (2 * (7789 / 66000 : ℝ) - C / 3) := by
    nlinarith only [hsq, hcross, hp, hq, hb]
  have hid :
      ((k + 7789 / 66000) ^ 2 - (C - k) * k * (k + 1 / 3)) -
        ((K + 7789 / 66000) ^ 2 - (C - K) * K * (K + 1 / 3)) =
      (K - k) * (-(k ^ 2 + k * K + K ^ 2) -
        (4 / 3 - C) * (k + K) - (2 * (7789 / 66000 : ℝ) - C / 3)) := by ring
  have hp := mul_nonneg (sub_nonneg.mpr hK) hbracket.le
  linarith only [hid, hp, hend]

private theorem covariance_forces_cubic {A b k h nu C : ℝ}
    (hA : (1 / 3 : ℝ) < A) (hb : (1 / 55 : ℝ) < b) (hk : 0 < k)
    (hh : h ≤ (467 / 2000 : ℝ)) (hnu : 2 * nu < C - k)
    (hcov : (A + b + k - h) ^ 2 < 2 * nu * k * (A + k)) :
    (k + 7789 / 66000) ^ 2 < (C - k) * k * (k + 1 / 3) := by
  let r := A + k
  let r0 := k + 1 / 3
  let d := (1 / 55 : ℝ) - 467 / 2000
  have hr : 0 < r := by dsimp only [r]; linarith
  have hr0 : 0 < r0 := by dsimp only [r0]; linarith
  have hrr : r0 < r := by dsimp only [r, r0]; linarith
  have hrd : 0 < r + d := by dsimp only [r, d]; linarith
  have hleft : (r + d) ^ 2 < (A + b + k - h) ^ 2 := by
    have hp := mul_pos (show 0 < A + b + k - h - (r + d) by
      dsimp only [r, d]; linarith) (show 0 < A + b + k - h + (r + d) by
      dsimp only [r, d]; linarith)
    nlinarith only [hp]
  have hupper : (r + d) ^ 2 < (C - k) * k * r := by
    have hp := mul_pos (sub_pos.mpr hnu) (mul_pos hk hr)
    dsimp only [r] at hp ⊢
    nlinarith only [hleft, hcov, hp]
  have hd : d ^ 2 < r * r0 := by
    have hp := mul_pos (show 0 < r - 1 / 3 by dsimp only [r]; linarith) hr0
    have hq := mul_pos hk (show 0 < (1 / 3 : ℝ) by norm_num)
    dsimp only [d, r0] at hp hq ⊢
    nlinarith only [hp, hq]
  have hmon := mul_nonneg (sub_nonneg.mpr hrr.le) (sub_nonneg.mpr hd.le)
  have hratio : (r0 + d) ^ 2 * r ≤ (r + d) ^ 2 * r0 := by
    nlinarith only [hmon]
  have hmul := mul_lt_mul_of_pos_right hupper hr0
  have hfinal : (r0 + d) ^ 2 < (C - k) * k * r0 := by
    apply (mul_lt_mul_iff_left₀ hr).mp
    nlinarith only [hratio, hmul]
  convert hfinal using 1
  dsimp only [r0, d]
  ring

/-- The same signed whole-hole bill and saturated physical quota exclude
all three closed own-slope sectors on the correlated corner rectangle. -/
theorem saturated_false {A b k h delta c : ℝ}
    (hh : h ∈ Icc (23 / 100 : ℝ) (467 / 2000))
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (226 / 589))
    (hA : 1 / 3 < A) (hb : 0 < b) (hk : 0 < k) (hAk : k < A)
    (hc : Benchmark.mixedTangent (117 / 100) (h / 2) < c)
    (hbody : (A + b) ^ 2 ≤ h)
    (htrace : b ≤ 2 * c - (1 - delta) * h →
      2 * (A + b) ^ 2 + (A + (2 * c - (1 - delta) * h) - b) ^ 2 + 4 * b * k ≤
        2 * h)
    (hDelta : 0 < delta - 2 * (2 * c - (1 - delta) * h))
    (hV : 0 < 1 - 2 * h - A + k)
    (hcost : 2 * c ≤ A - A ^ 2 + 2 * b - 4 * A * b - 2 * b ^ 2 - b * k)
    (hbill : k + 2 * (2 * c - h) +
      ((A - k) * k / (1 - 2 * h - A + k)) *
        (delta - 2 * (2 * c - (1 - delta) * h)) < delta * (1 - 2 * h - A))
    (hcov : (A + b + k - h) ^ 2 <
      2 * (2 * c - (1 - delta) * h + 1 - delta) * k * (A + k)) : False := by
  let B0 := Benchmark.mixedTangent (117 / 100) (h / 2)
  let gamma := 2 * c - (1 - delta) * h
  let nu := gamma + 1 - delta
  let kappa := 2 * B0 - h
  let g0 := 2 * B0 - (1 - delta) * h
  let K0 := 2 * c - h
  let V0 := 1 - 2 * h - A
  let Hk := (A - k) * k / (V0 + k)
  let Delta := delta - 2 * gamma
  let Delta0 := delta - 2 * g0
  have hguards := rectangle_guards hh hdelta
  have hd : 0 < delta := by linarith only [hdelta.1]
  have hc0 : (123 / 1000 : ℝ) < c := hguards.1.trans hc
  have hgamma : (57 / 1000 : ℝ) < gamma := by
    dsimp only [gamma]
    linarith only [hguards.2.1, hc]
  have hkgap : kappa < K0 := by dsimp only [kappa, K0, B0]; linarith only [hc]
  have hcap := alpha_lt_radius hh.2 hA hb.le hbody
  have hV0 : 0 < V0 := by dsimp only [V0]; linarith only [hh.2, hcap, hb]
  have hHpos : 0 < Hk := div_pos (mul_pos (sub_pos.mpr hAk) hk) hV
  have hHone : Hk < 1 := by
    apply (div_lt_one hV).mpr
    have hp := mul_pos hk (show 0 < 1 - A + k by linarith)
    dsimp only [V0] at hV0
    nlinarith only [hp, hV0]
  have hpay : k + 2 * K0 + Hk * Delta < delta * V0 := hbill
  have hbasic : k + 2 * K0 < delta * V0 := by
    have hp : 0 < Hk * Delta := mul_pos hHpos hDelta
    linarith only [hpay, hp]
  have hpay0 : k + 2 * kappa + Hk * Delta0 < delta * V0 := by
    have hid : (2 * K0 + Hk * Delta) - (2 * kappa + Hk * Delta0) =
        2 * (K0 - kappa) * (1 - Hk) := by
      dsimp only [K0, kappa, Delta, Delta0, gamma, g0]
      ring
    have hp := mul_pos (sub_pos.mpr hkgap) (sub_pos.mpr hHone)
    nlinarith only [hid, hp, hpay]
  have hU : k < delta * (2 / 3 - 2 * h) - 2 * kappa := by
    have hp := mul_pos hd (show 0 < A - 1 / 3 by linarith)
    dsimp only [V0] at hbasic
    linarith only [hbasic, hp, hkgap]
  have hUmax : k < (4449466 / 94321149 : ℝ) := by
    have hp := mul_nonneg (sub_nonneg.mpr hdelta.2)
      (show 0 ≤ 2 / 3 - 2 * h by linarith [hh.2])
    dsimp only [kappa, B0] at hU
    rw [tangent_eq] at hU
    nlinarith only [hU, hp, hh.1]
  have hbmin : (1 / 55 : ℝ) < b := by
    by_contra hn
    have hbsmall : b ≤ (1 / 55 : ℝ) := le_of_not_gt hn
    have ht := htrace (show b ≤ gamma by linarith only [hbsmall, hgamma])
    have hterm : A ^ 2 ≤ (A + gamma - b) ^ 2 := by
      have hp := mul_nonneg (show 0 ≤ A by linarith)
        (show 0 ≤ gamma - b by linarith)
      nlinarith only [hp, sq_nonneg (gamma - b)]
    have hmass : A ^ 2 ≤ (A + b) ^ 2 := by
      nlinarith only [mul_pos (show 0 < A by linarith only [hA]) hb, sq_nonneg b]
    have hsmall : A < (79 / 200 : ℝ) := by
      change 2 * (A + b) ^ 2 + (A + gamma - b) ^ 2 + 4 * b * k ≤ 2 * h at ht
      nlinarith only [hh.2, mul_pos hb hk, ht, hterm, hmass, hA]
    have hp := mul_nonneg (show 0 ≤ 79 / 200 - A by linarith)
      (show 0 ≤ 1 - 79 / 200 - A - 4 * b by linarith)
    have hq := mul_nonneg (show 0 ≤ 1 / 55 - b by linarith)
      (show 0 ≤ 2 - 4 * (79 / 200) - 2 * (1 / 55) - 2 * b by linarith)
    have hcmin := hc
    rw [tangent_eq] at hcmin
    nlinarith only [hcmin, hh.1, hcost, hp, hq, mul_pos hb hk]
  have hnu : 2 * nu < 2 - 4 * delta / 3 - k := by
    have hp := mul_pos hd (show 0 < A - 1 / 3 by linarith)
    dsimp only [K0, V0] at hbasic
    dsimp only [nu, gamma]
    nlinarith only [hbasic, hp]
  by_cases hlow : delta ≤ (3 / 10 : ℝ)
  · have hsmall : k < (1 / 32 : ℝ) := by
      have hp := mul_nonneg (sub_nonneg.mpr hlow)
        (show 0 ≤ 2 / 3 - 2 * h by linarith [hh.2])
      dsimp only [kappa, B0] at hU
      rw [tangent_eq] at hU
      nlinarith only [hU, hp, hh.1, hh.2]
    have hnu' : 2 * nu < 58 / 33 - k := by linarith only [hnu, hdelta.1]
    have hforced := covariance_forces_cubic hA hbmin hk hh.2 hnu' hcov
    have hpositive := cubic_positive hk.le hsmall.le
      (by norm_num : 4 / 3 - (58 / 33 : ℝ) ≤ -3 * (1 / 32))
      (by norm_num : 2 * (7789 / 66000 : ℝ) - (58 / 33) / 3 < 0)
      (by norm_num : 0 < ((1 / 32 : ℝ) + 7789 / 66000) ^ 2 -
        (58 / 33 - 1 / 32) * (1 / 32) * (1 / 32 + 1 / 3))
    linarith only [hforced, hpositive]
  · by_cases hmiddle : delta ≤ (1 / 3 : ℝ)
    · have hsmall : k < (3 / 80 : ℝ) := by
        have hp := mul_nonneg (sub_nonneg.mpr hmiddle)
          (show 0 ≤ 2 / 3 - 2 * h by linarith [hh.2])
        dsimp only [kappa, B0] at hU
        rw [tangent_eq] at hU
        nlinarith only [hU, hp, hh.1, hh.2]
      have hnu' : 2 * nu < 8 / 5 - k := by linarith
      have hforced := covariance_forces_cubic hA hbmin hk hh.2 hnu' hcov
      have hpositive := cubic_positive hk.le hsmall.le
        (by norm_num : 4 / 3 - (8 / 5 : ℝ) ≤ -3 * (3 / 80))
        (by norm_num : 2 * (7789 / 66000 : ℝ) - (8 / 5) / 3 < 0)
        (by norm_num : 0 < ((3 / 80 : ℝ) + 7789 / 66000) ^ 2 -
          (8 / 5 - 3 / 80) * (3 / 80) * (3 / 80 + 1 / 3))
      linarith only [hforced, hpositive]
    · have hdelta' : (1 / 3 : ℝ) < delta := lt_of_not_ge hmiddle
      have hDelta0 : (7 / 50 : ℝ) < Delta0 := by
        have hll := mul_nonneg (sub_nonneg.mpr hdelta'.le) (sub_nonneg.mpr hh.1)
        have hlu := mul_nonneg (sub_nonneg.mpr hdelta'.le) (sub_nonneg.mpr hh.2)
        have hul := mul_nonneg (sub_nonneg.mpr hdelta.2) (sub_nonneg.mpr hh.1)
        have huu := mul_nonneg (sub_nonneg.mpr hdelta.2) (sub_nonneg.mpr hh.2)
        dsimp only [Delta0, g0, B0]
        rw [tangent_eq]
        nlinarith only [hll, hlu, hul, huu, hh.1, hh.2, hdelta.2, hdelta']
      have hsmall : k < (1 / 24 : ℝ) := by
        by_contra hn
        have hkl : (1 / 24 : ℝ) ≤ k := le_of_not_gt hn
        have hAk' : (17 / 60 : ℝ) < A - k := by linarith
        have hVk : V0 + k < (77 / 300 : ℝ) := by
          dsimp only [V0]
          linarith [hh.1]
        have hp := mul_pos (mul_pos (show 0 < A - k - 17 / 60 by linarith) hk)
          (show 0 < Delta0 by linarith)
        have hq := mul_nonneg (mul_nonneg (sub_nonneg.mpr hkl)
          (show 0 ≤ (17 / 60 : ℝ) by norm_num)) (show 0 ≤ Delta0 by linarith)
        have hr := mul_pos (show 0 < Delta0 - 7 / 50 by linarith)
          (show 0 < (17 / 60 : ℝ) * (1 / 24) by norm_num)
        have hnum : (17 / 2640 : ℝ) * (V0 + k) < (A - k) * k * Delta0 := by
          nlinarith only [hp, hq, hr, hVk]
        have hH : (17 / 2640 : ℝ) < Hk * Delta0 := by
          dsimp only [Hk]
          rw [div_mul_eq_mul_div]
          exact (lt_div_iff₀ hV).mpr hnum
        have hbudget : Hk * Delta0 < (4449466 / 94321149 : ℝ) - k := by
          have hp := mul_nonneg (sub_nonneg.mpr hdelta.2)
            (show 0 ≤ 2 / 3 - 2 * h by linarith [hh.2])
          have hq := mul_pos hd (show 0 < A - 1 / 3 by linarith)
          dsimp only [V0, kappa, B0] at hpay0
          rw [tangent_eq] at hpay0
          nlinarith only [hpay0, hp, hq, hh.1]
        linarith only [hH, hbudget, hkl]
      have hnu' : 2 * nu < 14 / 9 - k := by linarith
      have hforced := covariance_forces_cubic hA hbmin hk hh.2 hnu' hcov
      have hpositive := cubic_positive hk.le hsmall.le
        (by norm_num : 4 / 3 - (14 / 9 : ℝ) ≤ -3 * (1 / 24))
        (by norm_num : 2 * (7789 / 66000 : ℝ) - (14 / 9) / 3 < 0)
        (by norm_num : 0 < ((1 / 24 : ℝ) + 7789 / 66000) ^ 2 -
          (14 / 9 - 1 / 24) * (1 / 24) * (1 / 24 + 1 / 3))
      linarith only [hforced, hpositive]

end Erdos1017.CornerPrivateScalar
