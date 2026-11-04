module

public import Erdos1017.Exclusions.E2.Lower.LowerE2PeakScalar

/-!
# Small saturated ratio versus one deficit row

A single integrated original deficit row is incompatible with a small saturated
ratio, by a scalar identity that spends no second missing-pair budget
(`false_of_small_ratio_square`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.UniversalDeficit

/-- A single integrated old deficit row is incompatible with a small
saturated ratio. This scalar identity spends no second missing-pair budget. -/
theorem false_of_small_ratio_square {A b u y : ℝ}
    (hA : 0 < A) (hb : b < A) (hAy : A ≤ y) (hy : y < 8 / 25) (hu : 0 ≤ u)
    (hsquare : (1 - A - b - y) ^ 2 ≤ (y - A) * (y - u)) : False := by
  have hfirst := mul_pos (hA.trans_le hAy)
    (show (0 : ℝ) < 8 - 25 * y by linarith only [hy])
  have hlast := mul_pos (sub_pos.mpr hb)
    (show (0 : ℝ) < 2 - 3 * A - 2 * y - b by linarith only [hb, hAy, hy])
  have huE := mul_nonneg hu (sub_nonneg.mpr hAy)
  nlinarith only [hsquare, sq_nonneg (y - A + (4 - 13 * y) / 8), hfirst, hlast, huE]

end Erdos1017.UniversalDeficit
