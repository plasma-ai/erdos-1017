module

public import Erdos1017.Exclusions.Cusp.CuspOutsideSmallCaps
public import Erdos1017.Exclusions.Cusp.CuspOutsideHoleCertificates

/-!
# Outside-peak contradictions for counts six to eight

For reciprocal counts six, seven and eight, the raw normalized outside-peak
budgets contradict the split-value gap, with the base and inventory caps derived
from the same original multiplier.
-/

@[expose] public section

namespace Erdos1017.CuspOutsideSmallExclusion

private theorem budget_estimates {U lam b k ell x t W Z : ℝ}
    (hlam : 1 < lam) (hU : lam < U) (hU2 : U < 2)
    (hell : ell ∈ Set.Ico lam U) (hW : 0 ≤ W)
    (hb0 : 0 ≤ b - 1) (hk0 : 0 ≤ k)
    (hbid : (b - 1) * (2 - lam) = U - 1)
    (hkid : k * (U - lam) * (2 - lam) = (U - 1) * lam)
    (hH : x ^ 2 = t ^ 2 + Z)
    (hreserve : U - ell < (2 - ell) * Z - ell * W)
    (hvariance : (ell - 1) * Z < (U - ell) * (t ^ 2 - 1)) :
    0 < Z ∧ b + k * W < x ^ 2 ∧ (U - 1) * Z < (U - ell) * (x ^ 2 - 1) := by
  have hA : 0 < U - 1 := by linarith
  have hd : 0 < U - ell := sub_pos.mpr hell.2
  have he : 0 < 2 - ell := by linarith [hell.2]
  have hell0 : 0 ≤ ell := by linarith [hell.1]
  have hZ : 0 < Z := by
    have hproduct := mul_nonneg hell0 hW
    have hpos : 0 < (2 - ell) * Z := by linarith
    exact pos_of_mul_pos_right hpos he.le
  have hvar : (U - 1) * Z < (U - ell) * (x ^ 2 - 1) := by
    rw [hH]
    nlinarith only [hvariance]
  have hdelta : U - ell ≤ U - lam := by linarith [hell.1]
  have heta : 2 - ell ≤ 2 - lam := by linarith [hell.1]
  have hproduct := mul_le_mul hdelta heta he.le (sub_nonneg.mpr hU.le)
  have hk : k * (U - ell) * (2 - ell) ≤ (U - 1) * ell := by
    calc
      k * (U - ell) * (2 - ell) = k * ((U - ell) * (2 - ell)) := by ring
      _ ≤ k * ((U - lam) * (2 - lam)) := mul_le_mul_of_nonneg_left hproduct hk0
      _ = (U - 1) * lam := by nlinarith only [hkid]
      _ ≤ (U - 1) * ell := mul_le_mul_of_nonneg_left hell.1 hA.le
  have hb : (b - 1) * (2 - ell) ≤ U - 1 := by
    calc
      (b - 1) * (2 - ell) ≤ (b - 1) * (2 - lam) :=
        mul_le_mul_of_nonneg_left heta hb0
      _ = U - 1 := hbid
  have hr := mul_lt_mul_of_pos_left hreserve hA
  have hz := mul_lt_mul_of_pos_left hvar he
  have hc : (U - 1) * ell * W <
      (U - ell) * (2 - ell) * (x ^ 2 - 1) - (U - ell) * (U - 1) := by
    nlinarith only [hr, hz]
  have hkw := mul_le_mul_of_nonneg_right hk hW
  have hbd := mul_le_mul_of_nonneg_left hb hd.le
  have hnegative : (U - ell) * (2 - ell) * (b + k * W - x ^ 2) < 0 := by
    nlinarith only [hc, hkw, hbd]
  refine ⟨hZ, ?_, hvar⟩
  by_contra hnot
  have hnonnegative :=
    mul_nonneg (mul_pos hd he).le (sub_nonneg.mpr (le_of_not_gt hnot))
  exact (not_lt_of_ge hnonnegative) hnegative

/-- The count-six outside-peak raw normalized budgets contradict the actual
split-value gap, with no supplied base or inventory-box bounds. -/
theorem outside_six_contradiction {ell x p t W Z : ℝ}
    (hell : ell ∈ Set.Ico (29 / 21 : ℝ) (5 / 3)) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hgap : 0 < 36 * Benchmark.splitValue (x / 6) - 5 / 6 - ell * (x ^ 2 - 1) / 2)
    (hH : x ^ 2 = t ^ 2 + Z) (hp : p ^ 2 ≤ W)
    (hinventory : 1 ≤ W + 2 * p * t - 2 * p ^ 2 + Z)
    (hreserve : 5 / 3 - ell < (2 - ell) * Z - ell * W)
    (hvariance : (ell - 1) * Z < (5 / 3 - ell) * (t ^ 2 - 1)) : False := by
  have hW0 : 0 ≤ W := (sq_nonneg p).trans hp
  obtain ⟨hZ0, hlower, hvar⟩ := budget_estimates (b := (27 / 13 : ℝ)) (k := (203 / 39 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hell hW0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hH hreserve hvariance
  have hbase : (27 / 13 : ℝ) ≤ x ^ 2 := by nlinarith only [hlower, hW0]
  have hcap := (CuspOutsideSmallCaps.outside_six_cap hx0 hbase hx2 hell.1 hgap).2
  have hWcap : W < 24 / 1015 := by nlinarith only [hlower, hcap]
  have hd : 0 < 5 / 3 - ell := sub_pos.mpr hell.2
  have hsmall := mul_lt_mul_of_pos_left
    (show x ^ 2 - 1 < (11 / 5 : ℝ) - 1 by linarith) hd
  have hbound := mul_le_mul_of_nonneg_right
    (show 5 / 3 - ell ≤ (2 / 7 : ℝ) by linarith [hell.1])
    (by norm_num : (0 : ℝ) ≤ 11 / 5 - 1)
  have hZcap : Z ∈ Set.Ioo (0 : ℝ) (18 / 35) :=
    ⟨hZ0, by nlinarith only [hvar, hsmall, hbound]⟩
  apply CuspOutsideHole.outside_six_contradiction hinventory hp ?_ hWcap.le hZcap.2.le
  rw [← hH]
  exact hcap.le

/-- The count-seven outside-peak raw normalized budgets pay their own base
and both inventory caps before the closed-box contradiction. -/
theorem outside_seven_contradiction {ell x p t W Z : ℝ}
    (hell : ell ∈ Set.Ico (41 / 28 : ℝ) (12 / 7)) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hgap : 0 < 49 * Benchmark.splitValue (x / 7) - 6 / 7 - ell * (x ^ 2 - 1) / 2)
    (hH : x ^ 2 = t ^ 2 + Z) (hp : p ^ 2 ≤ W)
    (hinventory : 1 ≤ W + 2 * p * t - 2 * p ^ 2 + Z)
    (hreserve : 12 / 7 - ell < (2 - ell) * Z - ell * W)
    (hvariance : (ell - 1) * Z < (12 / 7 - ell) * (t ^ 2 - 1)) : False := by
  have hW0 : 0 ≤ W := (sq_nonneg p).trans hp
  obtain ⟨hZ0, hlower, hvar⟩ := budget_estimates (b := (7 / 3 : ℝ)) (k := (164 / 21 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hell hW0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hH hreserve hvariance
  have hbase : (7 / 3 : ℝ) ≤ x ^ 2 := by nlinarith only [hlower, hW0]
  have hcap := (CuspOutsideSmallCaps.outside_seven_cap hx0 hbase hx2 hell.1 hgap).2
  have hWcap : W < 91 / 3280 := by nlinarith only [hlower, hcap]
  have hd : 0 < 12 / 7 - ell := sub_pos.mpr hell.2
  have hsmall := mul_lt_mul_of_pos_left
    (show x ^ 2 - 1 < (51 / 20 : ℝ) - 1 by linarith) hd
  have hbound := mul_le_mul_of_nonneg_right
    (show 12 / 7 - ell ≤ (1 / 4 : ℝ) by linarith [hell.1])
    (by norm_num : (0 : ℝ) ≤ 51 / 20 - 1)
  have hZcap : Z ∈ Set.Ioo (0 : ℝ) (217 / 400) :=
    ⟨hZ0, by nlinarith only [hvar, hsmall, hbound]⟩
  apply CuspOutsideHole.outside_seven_contradiction hinventory hp ?_ hWcap.le hZcap.2.le
  rw [← hH]
  exact hcap.le

/-- The count-eight outside-peak raw budgets derive the base, squared cap
and both inventory caps internally from the same original multiplier. -/
theorem outside_eight_contradiction {ell x p t W Z : ℝ}
    (hell : ell ∈ Set.Ico (55 / 36 : ℝ) (7 / 4)) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hgap : 0 < 64 * Benchmark.splitValue (x / 8) - 7 / 8 - ell * (x ^ 2 - 1) / 2)
    (hH : x ^ 2 = t ^ 2 + Z) (hp : p ^ 2 ≤ W)
    (hinventory : 1 ≤ W + 2 * p * t - 2 * p ^ 2 + Z)
    (hreserve : 7 / 4 - ell < (2 - ell) * Z - ell * W)
    (hvariance : (ell - 1) * Z < (7 / 4 - ell) * (t ^ 2 - 1)) : False := by
  have hW0 : 0 ≤ W := (sq_nonneg p).trans hp
  obtain ⟨hZ0, hlower, hvar⟩ := budget_estimates (b := (44 / 17 : ℝ)) (k := (1485 / 136 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hell hW0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hH hreserve hvariance
  have hcap := CuspOutsideSmallCaps.outside_eight_cap hx0 hx2 hell.1 hgap
  have hWcap : W < 232 / 13365 := by nlinarith only [hlower, hcap]
  have hd : 0 < 7 / 4 - ell := sub_pos.mpr hell.2
  have hsmall := mul_lt_mul_of_pos_left
    (show x ^ 2 - 1 < (25 / 9 : ℝ) - 1 by linarith) hd
  have hbound := mul_le_mul_of_nonneg_right
    (show 7 / 4 - ell ≤ (2 / 9 : ℝ) by linarith [hell.1])
    (by norm_num : (0 : ℝ) ≤ 25 / 9 - 1)
  have hZcap : Z ∈ Set.Ioo (0 : ℝ) (128 / 243) :=
    ⟨hZ0, by nlinarith only [hvar, hsmall, hbound]⟩
  apply CuspOutsideHole.outside_eight_contradiction hinventory hp ?_ hWcap.le hZcap.2.le
  rw [← hH]
  exact hcap.le

end Erdos1017.CuspOutsideSmallExclusion
