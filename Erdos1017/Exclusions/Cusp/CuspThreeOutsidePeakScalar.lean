module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Scalar exit for the third-cusp outside peak

The high-slope third-cusp reverse cap and the forward cubic contradict each
other for the same normalized peak, multiplier one included
(`outside_contradiction`).
-/

@[expose] public section

namespace Erdos1017.CuspThreeOutsidePeakScalar

/-- The high-slope third-cusp reverse cap and forward cubic contradict one
another for the same original normalized peak, including multiplier one. -/
theorem outside_contradiction {delta R : ℝ} (hdelta : 0 < delta)
    (hdeltaCap : delta ≤ 1 / 3) (hR : 0 < R)
    (hRcap : R < 6 * delta / (3 - delta))
    (hforward : delta < (2 / 3 + delta) * R ^ 2 - (5 / 8) * R ^ 3) : False := by
  let M := 6 * delta / (3 - delta)
  have hden : 0 < 3 - delta := by linarith only [hdeltaCap]
  have hden0 : 3 - delta ≠ 0 := hden.ne'
  have hM : 0 < M := div_pos (mul_pos (by norm_num) hdelta) hden
  have hRM : 0 ≤ M - R := by dsimp [M]; linarith only [hRcap]
  have hdeltaSq : delta ^ 2 ≤ 1 / 9 := by nlinarith only [hdelta, hdeltaCap]
  have hderivative : 19 / 12 ≤ 4 - (79 / 12) * delta - 2 * delta ^ 2 := by
    nlinarith only [hdeltaCap, hdeltaSq]
  have hslope : 0 < 2 / 3 + delta - (15 / 16) * M := by
    have heq : (2 / 3 + delta - (15 / 16) * M) * (3 - delta) =
        (4 - (79 / 12) * delta - 2 * delta ^ 2) / 2 := by
      dsimp [M]
      field_simp
      ring
    apply (mul_pos_iff_of_pos_right hden).mp
    rw [heq]
    linarith only [hderivative]
  have hmonotone : (2 / 3 + delta) * R ^ 2 - (5 / 8) * R ^ 3 ≤
      (2 / 3 + delta) * M ^ 2 - (5 / 8) * M ^ 3 := by
    have hfirst := mul_nonneg hRM (mul_nonneg hslope.le (by linarith : (0 : ℝ) ≤ M + R))
    have hsecond := mul_nonneg (sq_nonneg (M - R)) (by linarith : (0 : ℝ) ≤ M + 2 * R)
    nlinarith only [hfirst, hsecond]
  have hpoly : 99 * delta - 60 * delta ^ 2 - 35 * delta ^ 3 - 27 < 0 := by
    have hslope : 0 ≤ 676 / 9 - (215 / 3) * delta - 35 * delta ^ 2 := by
      nlinarith only [hdeltaCap, hdeltaSq]
    have hpaid := mul_nonneg (by linarith only [hdeltaCap] : (0 : ℝ) ≤ 1 / 3 - delta) hslope
    nlinarith only [hpaid]
  have hendpoint : (2 / 3 + delta) * M ^ 2 - (5 / 8) * M ^ 3 < delta := by
    have heq : ((2 / 3 + delta) * M ^ 2 - (5 / 8) * M ^ 3 - delta) *
        (3 - delta) ^ 3 = delta * (99 * delta - 60 * delta ^ 2 - 35 * delta ^ 3 - 27) := by
      dsimp [M]
      field_simp
      ring
    have hscaled : ((2 / 3 + delta) * M ^ 2 - (5 / 8) * M ^ 3 - delta) *
        (3 - delta) ^ 3 < 0 := by
      rw [heq]
      exact mul_neg_of_pos_of_neg hdelta hpoly
    have hneg : (2 / 3 + delta) * M ^ 2 - (5 / 8) * M ^ 3 - delta < 0 := by
      by_contra hn
      exact not_le_of_gt hscaled (mul_nonneg (le_of_not_gt hn) (pow_pos hden 3).le)
    linarith only [hneg]
  linarith only [hforward, hmonotone, hendpoint]

end Erdos1017.CuspThreeOutsidePeakScalar
