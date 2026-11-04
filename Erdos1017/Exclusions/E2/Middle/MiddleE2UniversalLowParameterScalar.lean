module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates

/-!
# Low-parameter scalar bounds for the universal middle case

From `7/50` onward the stronger selector gives a fixed one-fifth cap, the
middle-cell square budget gives the same cap on closed missing mass, and with
ratio at most one third and closed missing mass at most one fifth the first
shared deficit polynomial is negative.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.MiddleE2UniversalLowParameter

open LowerE2Scalar

private theorem selector_numerator_pos {q : ℝ}
    (hq : q ∈ Icc (7 / 50 : ℝ) (1 / 5)) :
    0 < -196 + 1372 * q + 1227 * q ^ 2 + 424 * q ^ 3 - 235 * q ^ 4 := by
  have hq0 : 0 ≤ q := by linarith only [hq.1]
  have h2 : (7 / 50 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) hq.1 2
  have h3 : (7 / 50 : ℝ) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq.1 3
  have h4 : q ^ 4 ≤ (1 / 5 : ℝ) ^ 4 := pow_le_pow_left₀ hq0 hq.2 4
  norm_num at h2 h3 h4
  linarith only [hq.1, h2, h3, h4]

/-- A fixed cap of one fifth is available from the stronger selector
throughout the range starting at 7/50. -/
theorem selector_margin {q A : ℝ} (hq : q ∈ Icc (7 / 50 : ℝ) (1 / 5)) :
    (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 <
      gapFloor q + (multiplier q - 2 / 3) * (1 / 5) ^ 2 := by
  have hq0 : 0 ≤ q := by linarith only [hq.1]
  have hR := denominator_pos hq0
  have hq2 : q + 2 ≠ 0 := by linarith only [hq.1]
  have hq26 : q + 26 ≠ 0 := by linarith only [hq.1]
  have hid : (gapFloor q + (multiplier q - 2 / 3) * (1 / 5) ^ 2 -
      (2 + 5 * q) / (2 * (q + 26))) *
        (150 * denominator q * (q + 2) * (q + 26)) =
      -196 + 1372 * q + 1227 * q ^ 2 + 424 * q ^ 3 - 235 * q ^ 4 := by
    unfold gapFloor multiplier
    field_simp
    unfold denominator
    ring
  have hpoly := selector_numerator_pos hq
  rw [← hid] at hpoly
  have hden : 0 < 150 * denominator q * (q + 2) * (q + 26) := by positivity
  have hmargin := sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hpoly)
  have hquad : ((2 + 5 * q) / (2 * (q + 26)) -
      (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6) *
        (6 * (q + 26) * (q + 2)) = ((q + 26) * A - 4 * (q + 2)) ^ 2 := by
    unfold multiplier
    field_simp
    ring
  have hsquare := sq_nonneg ((q + 26) * A - 4 * (q + 2))
  rw [← hquad] at hsquare
  have hquadDen : 0 < 6 * (q + 26) * (q + 2) := by positivity
  have hbound := sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hquadDen).mp hsquare)
  exact hbound.trans_lt hmargin

/-- The actual middle-cell square budget gives the one-fifth cap. -/
theorem closed_missing_lt_fifth {q A gamma t : ℝ}
    (hq : q ∈ Icc (7 / 50 : ℝ) (1 / 5)) (hgamma : gapFloor q < gamma)
    (hbudget : gamma + (multiplier q - 2 / 3) * t ^ 2 ≤
      (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6) : t < 1 / 5 := by
  have hmargin := selector_margin (A := A) hq
  have hcoef : 0 < multiplier q - 2 / 3 := by
    unfold multiplier
    rw [sub_pos, lt_div_iff₀ (by linarith only [hq.1])]
    linarith only [hq.2]
  have hscaled : (multiplier q - 2 / 3) * t ^ 2 <
      (multiplier q - 2 / 3) * (1 / 5) ^ 2 := by
    linarith only [hmargin, hgamma, hbudget]
  have hsquare := (mul_lt_mul_iff_right₀ hcoef).mp hscaled
  nlinarith only [hsquare]

/-- With ratio at most one third and closed missing mass at most one
fifth, the first shared deficit polynomial is negative on the whole domain. -/
theorem first_polynomial_neg {x C p : ℝ}
    (hx : 0 ≤ x) (hC : 0 ≤ C) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 3) :
    let N := 2 / 15 + x
    let w := N + C
    C * (p ^ 2 - w ^ 2) - (w ^ 2 - x * p) * (p + N - C) < 0 := by
  let N := 2 / 15 + x
  let w := N + C
  have hN : 2 / 15 ≤ N := by dsimp only [N]; linarith only [hx]
  have hN0 : 0 < N := by linarith only [hN]
  have hxp := mul_le_mul_of_nonneg_left hp hx
  have hbase : 0 < N ^ 2 - x * p := by
    dsimp only [N]
    nlinarith only [hxp, sq_nonneg (x - 1 / 30)]
  have hpSquare := mul_nonneg hp0 (sub_nonneg.mpr hp)
  have hmin := mul_nonneg hp0
    (show 0 ≤ x + 2 * N - 4 / 15 by dsimp only [N]; linarith only [hx])
  have hpScaled := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 1 / 15)
  have hNSquare : (2 / 15 : ℝ) ^ 2 ≤ N ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hN 2
  have hcoefficient : p ^ 2 - x * p - 2 * N * p - 2 * N ^ 2 < 0 := by
    nlinarith only [hpSquare, hmin, hpScaled, hNSquare]
  have hpn : 0 < p + N := by linarith only [hp0, hN0]
  have hfirst := mul_pos hpn hbase
  have hsecond := mul_nonpos_of_nonneg_of_nonpos hC hcoefficient.le
  have hthird := mul_nonneg (sq_nonneg C) hpn.le
  change C * (p ^ 2 - w ^ 2) - (w ^ 2 - x * p) * (p + N - C) < 0
  have hid : C * (p ^ 2 - w ^ 2) - (w ^ 2 - x * p) * (p + N - C) =
      -(p + N) * (N ^ 2 - x * p) +
        C * (p ^ 2 - x * p - 2 * N * p - 2 * N ^ 2) - C ^ 2 * (p + N) := by
    dsimp only [w]
    ring
  rw [hid]
  linarith only [hfirst, hsecond, hthird]

end Erdos1017.MiddleE2UniversalLowParameter
