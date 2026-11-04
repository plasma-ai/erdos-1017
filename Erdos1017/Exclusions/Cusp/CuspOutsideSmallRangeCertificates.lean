module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Sign certificates for the small-count outside quadratics

Scalar facts for reciprocal counts six, seven and eight: the cell quadratics are
negative beyond their squared caps, and the count-seven and count-eight
envelopes are uniformly negative from seven fourths and five thirds onward.
-/

@[expose] public section

namespace Erdos1017.CuspOutsideSmallRange

/-- The normalized count-six, cell-three quadratic is strictly negative
on the entire real line. -/
theorem six_cell_three_neg (x : ℝ) :
    (-107 * x ^ 2 + 336 * x - 264) / 84 < 0 := by
  have hid : 107 * (107 * x ^ 2 - 336 * x + 264) = (107 * x - 168) ^ 2 + 24 := by
    ring
  have hpositive : 0 < 107 * x ^ 2 - 336 * x + 264 := by
    nlinarith [sq_nonneg (107 * x - 168)]
  exact div_neg_of_neg_of_pos (by linarith) (by norm_num)

/-- The count-six, cell-four quadratic is negative beyond the squared cap,
with both signs of the real variable included. -/
theorem six_cell_four_neg {x : ℝ} (hx : 11 / 5 ≤ x ^ 2) :
    (-479 * x ^ 2 + 1260 * x - 816) / 420 < 0 := by
  have hid : (479 * x ^ 2 + 816) ^ 2 - (1260 * x) ^ 2 =
      85801 / 25 + (1018342 / 5) * (x ^ 2 - 11 / 5) +
        229441 * (x ^ 2 - 11 / 5) ^ 2 := by ring
  have hgap : 0 < (479 * x ^ 2 + 816) ^ 2 - (1260 * x) ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - 11 / 5)]
  have hpositive : 0 < 479 * x ^ 2 + 816 := by nlinarith [sq_nonneg x]
  have hlinear : 1260 * x < 479 * x ^ 2 + 816 := by
    by_contra hnot
    have hle := le_of_not_gt hnot
    have hproduct := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ 1260 * x + (479 * x ^ 2 + 816) by linarith)
    nlinarith
  exact div_neg_of_neg_of_pos (by linarith) (by norm_num)

/-- The count-seven, cell-four quadratic is negative beyond the squared cap,
with both signs of the real variable included. -/
theorem seven_cell_four_neg {x : ℝ} (hx : 51 / 20 ≤ x ^ 2) :
    (-331 * x ^ 2 + 980 * x - 721) / 280 < 0 := by
  have hid : (331 * x ^ 2 + 721) ^ 2 - (980 * x) ^ 2 =
      144601 / 400 + (756631 / 10) * (x ^ 2 - 51 / 20) +
        109561 * (x ^ 2 - 51 / 20) ^ 2 := by ring
  have hgap : 0 < (331 * x ^ 2 + 721) ^ 2 - (980 * x) ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - 51 / 20)]
  have hpositive : 0 < 331 * x ^ 2 + 721 := by nlinarith [sq_nonneg x]
  have hlinear : 980 * x < 331 * x ^ 2 + 721 := by
    by_contra hnot
    have hle := le_of_not_gt hnot
    have hproduct := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ 980 * x + (331 * x ^ 2 + 721) by linarith)
    nlinarith
  exact div_neg_of_neg_of_pos (by linarith) (by norm_num)

/-- The count-seven envelope is uniformly negative from seven fourths onward,
for every real parameter below its source cap. -/
theorem seven_envelope_bound {D x : ℝ} (hD : D ≤ 15 / 8) (hx : 7 / 4 ≤ x) :
    D * (x ^ 2 - 1) + 1 - (15 / 16) * x ^ 3 ≤ -161 / 1024 := by
  have hparameter := mul_le_mul_of_nonneg_right hD
    (show 0 ≤ x ^ 2 - 1 by nlinarith)
  have hshift : 0 ≤ x - 7 / 4 := sub_nonneg.mpr hx
  have hcube := mul_nonneg (sq_nonneg (x - 7 / 4)) hshift
  have hid : (15 / 8) * (x ^ 2 - 1) + 1 - (15 / 16) * x ^ 3 =
      -161 / 1024 - (525 / 256) * (x - 7 / 4) -
        (195 / 64) * (x - 7 / 4) ^ 2 - (15 / 16) * (x - 7 / 4) ^ 3 := by ring
  nlinarith [sq_nonneg (x - 7 / 4)]

/-- The count-eight envelope is uniformly negative from five thirds onward,
for every real parameter below its source cap. -/
theorem eight_envelope_bound {D x : ℝ} (hD : D ≤ 17 / 9) (hx : 5 / 3 ≤ x) :
    D * (x ^ 2 - 1) + 1 - (19 / 20) * x ^ 3 ≤ -13 / 324 := by
  have hparameter := mul_le_mul_of_nonneg_right hD
    (show 0 ≤ x ^ 2 - 1 by nlinarith)
  have hshift : 0 ≤ x - 5 / 3 := sub_nonneg.mpr hx
  have hcube := mul_nonneg (sq_nonneg (x - 5 / 3)) hshift
  have hid : (17 / 9) * (x ^ 2 - 1) + 1 - (19 / 20) * x ^ 3 =
      -13 / 324 - (175 / 108) * (x - 5 / 3) -
        (103 / 36) * (x - 5 / 3) ^ 2 - (19 / 20) * (x - 5 / 3) ^ 3 := by ring
  nlinarith [sq_nonneg (x - 5 / 3)]

end Erdos1017.CuspOutsideSmallRange
