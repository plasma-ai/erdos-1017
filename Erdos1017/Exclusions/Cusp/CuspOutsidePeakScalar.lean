module

public import Erdos1017.Exclusions.Cusp.CuspOutsideLargeSplitGap
public import Erdos1017.Exclusions.Cusp.CuspOutsideSmallExclusion

/-!
# Scalar outside-peak exit for counts at least six

One scalar contradiction covers every cusp index at least six, keeping all
normalized inventory variables and deriving the cell, box and squared-base
bounds; the raw reserve and variance budgets give the squared baseline.
-/

@[expose] public section

namespace Erdos1017.CuspOutsidePeakScalar

/-- The raw reserve and variance budgets give the large-count squared baseline,
without discarding the original nonnegative inventory `W`. -/
theorem squared_base_of_raw_budgets {m ell x t W Z : ℝ} (hm : 9 ≤ m)
    (hell : ell ∈ Set.Ico (2 - 2 / m - 2 / (m + 1)) (2 - 2 / m))
    (hW : 0 ≤ W) (hH : x ^ 2 = t ^ 2 + Z)
    (hreserve : 2 - 2 / m - ell < (2 - ell) * Z - ell * W)
    (hvariance : (ell - 1) * Z < (2 - 2 / m - ell) * (t ^ 2 - 1)) :
    m * (m + 3) / (2 * (2 * m + 1)) < x ^ 2 := by
  let U := 2 - 2 / m
  let B := m * (m + 3) / (2 * (2 * m + 1))
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m + 1 := by linarith
  have hm2 : 0 < 2 * (2 * m + 1) := by linarith
  have hquot : 2 / m < 1 := (div_lt_iff₀ hm0).mpr (by linarith)
  have hquot1 : 2 / (m + 1) < 1 := (div_lt_iff₀ hm1).mpr (by linarith)
  have hU : 1 < U := by dsimp [U]; linarith
  have hU2 : U < 2 := by dsimp [U]; linarith [div_pos (by norm_num : (0 : ℝ) < 2) hm0]
  have hell0 : 0 ≤ ell := by linarith [hell.1]
  have hd : 0 < U - ell := sub_pos.mpr hell.2
  have he : 0 < 2 - ell := by linarith [hell.2]
  have hB : 0 ≤ B - 1 := by
    have hB1 : 1 ≤ B := by
      apply (le_div_iff₀ hm2).mpr
      nlinarith
    linarith
  have hidentity : (B - 1) * (2 - (2 - 2 / m - 2 / (m + 1))) = U - 1 := by
    dsimp [B, U]
    field_simp
    ring
  have hb : (B - 1) * (2 - ell) ≤ U - 1 := by
    calc
      (B - 1) * (2 - ell) ≤
          (B - 1) * (2 - (2 - 2 / m - 2 / (m + 1))) :=
        mul_le_mul_of_nonneg_left (by linarith [hell.1]) hB
      _ = U - 1 := hidentity
  have hr : U - ell < (2 - ell) * Z := by
    dsimp [U]
    linarith [mul_nonneg hell0 hW]
  have hv : (U - 1) * Z < (U - ell) * (x ^ 2 - 1) := by
    rw [hH]
    dsimp [U]
    nlinarith only [hvariance]
  have hr' := mul_lt_mul_of_pos_left hr (show 0 < U - 1 by linarith)
  have hv' := mul_lt_mul_of_pos_left hv he
  have hc : (U - ell) * (U - 1) < (U - ell) * ((2 - ell) * (x ^ 2 - 1)) := by
    nlinarith only [hr', hv']
  have hc' := (mul_lt_mul_iff_right₀ hd).mp hc
  have hfinal : (2 - ell) * (B - 1) < (2 - ell) * (x ^ 2 - 1) := by
    nlinarith only [hb, hc']
  have := (mul_lt_mul_iff_right₀ he).mp hfinal
  dsimp [B] at this
  linarith

/-- One scalar exit for every integer count at least six. All normalized
inventory variables are retained; cell, box and squared-base bounds are derived. -/
theorem outside_contradiction {k : ℕ} {ell x p t W Z : ℝ} (hk : 6 ≤ k)
    (hell : ell ∈ Set.Ico (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1))
      (2 - 2 / (k : ℝ)))
    (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hgap : 0 < (k : ℝ) ^ 2 * Benchmark.splitValue (x / k) -
      (1 - 1 / (k : ℝ)) - ell * (x ^ 2 - 1) / 2)
    (hH : x ^ 2 = t ^ 2 + Z) (hp : p ^ 2 ≤ W)
    (hinventory : 1 ≤ W + 2 * p * t - 2 * p ^ 2 + Z)
    (hreserve : 2 - 2 / (k : ℝ) - ell < (2 - ell) * Z - ell * W)
    (hvariance : (ell - 1) * Z < (2 - 2 / (k : ℝ) - ell) * (t ^ 2 - 1)) :
    False := by
  by_cases hk9 : 9 ≤ k
  · have hm : (9 : ℝ) ≤ k := by exact_mod_cast hk9
    have hbase := squared_base_of_raw_budgets hm hell
      (le_trans (sq_nonneg p) hp) hH hreserve hvariance
    exact CuspOutsideLargeSplitGap.outside_large_contradiction hm hell.1 hx0 hx2
      hbase.le hgap
  · have hcases : k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases hcases with rfl | rfl | rfl
    · norm_num at hell hgap hreserve hvariance
      exact CuspOutsideSmallExclusion.outside_six_contradiction hell hx0 hx2 (by linarith) hH hp
        hinventory hreserve hvariance
    · norm_num at hell hgap hreserve hvariance
      exact CuspOutsideSmallExclusion.outside_seven_contradiction hell hx0 hx2 (by linarith) hH hp
        hinventory hreserve hvariance
    · norm_num at hell hgap hreserve hvariance
      exact CuspOutsideSmallExclusion.outside_eight_contradiction hell hx0 hx2 (by linarith) hH hp
        hinventory hreserve hvariance

end Erdos1017.CuspOutsidePeakScalar
