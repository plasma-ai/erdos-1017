module

public import Erdos1017.Benchmark.BenchmarkPhiBounds

/-!
# Monotonicity of the head-count ratio

The head-count ratio decreases with the own multiplier whenever the
benchmark value strictly exceeds the missing density.
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- The head-count ratio `r(1 - ell)/(2(b - ell·e))` does not increase with
`ell`: for `r ≥ 0`, `0 ≤ e < b` and `L ≤ ell < 1`, its value at `ell` is at
most its value at `L`. -/
theorem headRatio_antitone {r e b L ell : ℝ} (hr : 0 ≤ r) (he : 0 ≤ e)
    (hb : e < b) (hL : L ≤ ell) (hell : ell < 1) :
    r * (1 - ell) / (2 * (b - ell * e)) ≤
      r * (1 - L) / (2 * (b - L * e)) := by
  have hL1 : L < 1 := hL.trans_lt hell
  have hden : 0 < 2 * (b - ell * e) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hell.le) he]
  have hdenL : 0 < 2 * (b - L * e) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL1.le) he]
  apply (div_le_div_iff₀ hden hdenL).mpr
  have hid : r * (1 - L) * (2 * (b - ell * e)) -
      r * (1 - ell) * (2 * (b - L * e)) = 2 * r * (ell - L) * (b - e) := by ring
  have hnonneg : 0 ≤ r * (1 - L) * (2 * (b - ell * e)) -
      r * (1 - ell) * (2 * (b - L * e)) := by
    rw [hid]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (sub_nonneg.mpr hL))
      (sub_nonneg.mpr hb.le)
  linarith

/-- For `r ≥ 0`, `0 ≤ e < b` and `L ≤ ell < 1`, a bound `C` on the head-count
ratio `r(1 - L)/(2(b - Le))` also bounds `r(1 - ell)/(2(b - ell·e))`. -/
theorem headRatio_le_of_slope {r e b L ell C : ℝ} (hr : 0 ≤ r) (he : 0 ≤ e)
    (hb : e < b) (hL : L ≤ ell) (hell : ell < 1)
    (hbound : r * (1 - L) / (2 * (b - L * e)) ≤ C) :
    r * (1 - ell) / (2 * (b - ell * e)) ≤ C :=
  (headRatio_antitone hr he hb hL hell).trans hbound

end Erdos1017.Benchmark
