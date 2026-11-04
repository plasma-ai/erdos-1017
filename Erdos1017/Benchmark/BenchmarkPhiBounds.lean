module

public import Erdos1017.Benchmark.BenchmarkFamilyGuards

/-!
# Head-count bounds for the three benchmark branches

The scalar head-count bounds for the three possible benchmark branches on the
remaining multipartite density interval. Branch selection and right
differentiation are supplied by `BenchmarkHeadCountGuards`.
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- For `0 ≤ e < b` and `L < 1`, if `4(2(b - Le))² - 2e(1 - L)² > 0`, then the
head-count ratio satisfies `√(2e)(1 - L)/(2(b - Le)) < 2`. -/
private theorem phi_lt_two_of_gap {e b L : ℝ} (he : 0 ≤ e) (hb : e < b) (hL : L < 1)
    (hgap : 0 < 4 * (2 * (b - L * e)) ^ 2 - 2 * e * (1 - L) ^ 2) :
    Real.sqrt (2 * e) * (1 - L) / (2 * (b - L * e)) < 2 := by
  have hden : 0 < 2 * (b - L * e) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL.le) he]
  apply (div_lt_iff₀ hden).mpr
  have hr := Real.sqrt_nonneg (2 * e)
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) he)
  have hn : 0 ≤ Real.sqrt (2 * e) * (1 - L) := mul_nonneg hr (sub_nonneg.mpr hL.le)
  apply (sq_lt_sq₀ hn (by positivity : 0 ≤ 2 * (2 * (b - L * e)))).mp
  rw [mul_pow, hs]
  nlinarith

/-- For `2/3 < z < 4/5` with `twoHeadDensity z ≥ 0`, put `L = (4 - 3z)/(3z)`,
`e = twoHeadDensity z` and `b = twoHeadValue z`; then `1/2 < L < 1`, `e < b`,
and the head-count ratio satisfies `√(2e)(1 - L)/(2(b - Le)) < 2`. -/
theorem twoHead_phi_bounds {z : ℝ} (hz : z ∈ Set.Ioo (2 / 3 : ℝ) (4 / 5))
    (he : 0 ≤ twoHeadDensity z) :
    1 / 2 < (4 - 3 * z) / (3 * z) ∧ (4 - 3 * z) / (3 * z) < 1 ∧
      twoHeadDensity z < twoHeadValue z ∧
      Real.sqrt (2 * twoHeadDensity z) * (1 - (4 - 3 * z) / (3 * z)) /
        (2 * (twoHeadValue z - (4 - 3 * z) / (3 * z) * twoHeadDensity z)) < 2 := by
  have hz0 : 0 < z := by linarith [hz.1]
  have heta := twoHeadDenominator_pos hz.1.le
  have hLlo : 1 / 2 < (4 - 3 * z) / (3 * z) := by
    apply (lt_div_iff₀ (by positivity : 0 < 3 * z)).mpr
    linarith [hz.2]
  have hLhi : (4 - 3 * z) / (3 * z) < 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < 3 * z)).mpr
    linarith [hz.1]
  have hv : twoHeadDensity z < twoHeadValue z := by
    have hp : 0 < (3 * z - 2) ^ 2 * (1 - z) * (3 * z - 1) /
        (24 * twoHeadDenominator z ^ 2) := by
      have h1 : 0 < 3 * z - 2 := by linarith [hz.1]
      have h2 : 0 < 1 - z := by linarith [hz.2]
      have h3 : 0 < 3 * z - 1 := by linarith [hz.1]
      positivity
    unfold twoHeadValue
    linarith
  refine ⟨hLlo, hLhi, hv, phi_lt_two_of_gap he hv hLhi ?_⟩
  have hid :
      4 * (2 * (twoHeadValue z - (4 - 3 * z) / (3 * z) * twoHeadDensity z)) ^ 2 -
          2 * twoHeadDensity z * (1 - (4 - 3 * z) / (3 * z)) ^ 2 =
        (3 * z - 2) ^ 2 * (1 - z) * (5 * z - 3) / (18 * twoHeadDenominator z ^ 2) := by
    have hz' := hz0.ne'
    have heta' := heta.ne'
    unfold twoHeadValue twoHeadDensity
    field_simp
    unfold twoHeadDenominator
    ring
  rw [hid]
  have h1 : 0 < 3 * z - 2 := by linarith [hz.1]
  have h2 : 0 < 1 - z := by linarith [hz.2]
  have h3 : 0 < 5 * z - 3 := by linarith [hz.1]
  positivity

/-- For `σ_D < s ≤ σ₀` with `mixedDensity s ≥ 0`, put `L = (s + 1)/(3s)`,
`e = mixedDensity s` and `b = mixedValue s`; then `1/2 < L < 1`, `e < b`, and
the head-count ratio satisfies `√(2e)(1 - L)/(2(b - Le)) < 2`. -/
theorem mixed_phi_bounds {s : ℝ} (hs : sigmaD < s) (hshi : s ≤ sigmaZero)
    (he : 0 ≤ mixedDensity s) :
    1 / 2 < (s + 1) / (3 * s) ∧ (s + 1) / (3 * s) < 1 ∧
      mixedDensity s < mixedValue s ∧
      Real.sqrt (2 * mixedDensity s) * (1 - (s + 1) / (3 * s)) /
        (2 * (mixedValue s - (s + 1) / (3 * s) * mixedDensity s)) < 2 := by
  have hs1 : 1 < s := sigmaD_gt_one.trans hs
  have hs0 : 0 < s := by linarith
  have hs2 : s < 2 := hshi.trans_lt sigmaZero_bounds.2
  have hQ := mixedDenominator_pos hs0.le
  have hLlo : 1 / 2 < (s + 1) / (3 * s) := by
    apply (lt_div_iff₀ (by positivity : 0 < 3 * s)).mpr
    linarith
  have hLhi : (s + 1) / (3 * s) < 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < 3 * s)).mpr
    linarith
  have hpoly : 0 < mixedRootPolynomial s := by
    have hm := mixedRootPolynomial_strictMonoOn sigmaD_spec.1.1 hs1.le hs
    rwa [sigmaD_spec.2] at hm
  have hv : mixedDensity s < mixedValue s := by
    have hid : mixedValue s - mixedDensity s =
        s * mixedRootPolynomial s / (6 * mixedDenominator s ^ 2) := by
      unfold mixedValue mixedDensity mixedRootPolynomial
      ring
    rw [← sub_pos, hid]
    positivity
  refine ⟨hLlo, hLhi, hv, phi_lt_two_of_gap he hv hLhi ?_⟩
  have hid :
      4 * (2 * (mixedValue s - (s + 1) / (3 * s) * mixedDensity s)) ^ 2 -
          2 * mixedDensity s * (1 - (s + 1) / (3 * s)) ^ 2 =
        (s - 1) * (4 * s + 1) * (16 * s ^ 4 - 17 * s ^ 3 + 15 * s ^ 2 - 2 * s - 2) /
          (9 * s ^ 2 * mixedDenominator s ^ 2) := by
    have hs' := hs0.ne'
    have hQ' := hQ.ne'
    unfold mixedValue mixedDensity
    field_simp
    unfold mixedDenominator
    ring
  rw [hid]
  have hp : 0 < 16 * s ^ 4 - 17 * s ^ 3 + 15 * s ^ 2 - 2 * s - 2 := by
    have hid : 16 * s ^ 4 - 17 * s ^ 3 + 15 * s ^ 2 - 2 * s - 2 =
        16 * (s - 1) ^ 4 + 47 * (s - 1) ^ 3 + 60 * (s - 1) ^ 2 + 41 * (s - 1) + 10 := by ring
    rw [hid]
    have ht : 0 < s - 1 := sub_pos.mpr hs1
    positivity
  have ht : 0 < s - 1 := sub_pos.mpr hs1
  positivity

/-- For `2/5 < r < 9/20`, put `L = 1/r - 5/3`, `e = r²/2` and
`b = splitPolynomial 2 r`; then `1/2 < L < 1`, `e < b`, and the head-count
ratio satisfies `r(1 - L)/(2(b - Le)) < 2`. -/
theorem split_phi_bounds {r : ℝ} (hr : r ∈ Set.Ioo (2 / 5 : ℝ) (9 / 20)) :
    1 / 2 < 1 / r - 5 / 3 ∧ 1 / r - 5 / 3 < 1 ∧
      r ^ 2 / 2 < splitPolynomial 2 r ∧
      r * (1 - (1 / r - 5 / 3)) /
        (2 * (splitPolynomial 2 r - (1 / r - 5 / 3) * (r ^ 2 / 2))) < 2 := by
  have hr0 : 0 < r := by linarith [hr.1]
  have hLlo : 1 / 2 < 1 / r - 5 / 3 := by
    have h : 13 / 6 < 1 / r := (lt_div_iff₀ hr0).mpr (by linarith [hr.2])
    linarith
  have hLhi : 1 / r - 5 / 3 < 1 := by
    have h : 1 / r < 8 / 3 := (div_lt_iff₀ hr0).mpr (by linarith [hr.1])
    linarith
  have hv : r ^ 2 / 2 < splitPolynomial 2 r := by
    have hp := mul_pos (show 0 < 1 - 2 * r by linarith [hr.2])
      (show 0 < 4 * r - 1 by linarith [hr.1])
    norm_num [splitPolynomial]
    nlinarith
  refine ⟨hLlo, hLhi, hv, ?_⟩
  have hid : r * (1 - (1 / r - 5 / 3)) /
      (2 * (splitPolynomial 2 r - (1 / r - 5 / 3) * (r ^ 2 / 2))) =
        (8 * r - 3) / (3 * r - 1) := by
    have hr' := hr0.ne'
    have hd : 3 * r - 1 ≠ 0 := by linarith [hr.1]
    have hden : 2 * (splitPolynomial 2 r - (1 / r - 5 / 3) * (r ^ 2 / 2)) =
        (3 * r - 1) / 3 := by
      norm_num [splitPolynomial]
      field_simp
      ring
    rw [hden]
    field_simp
    ring
  rw [hid]
  apply (div_lt_iff₀ (by linarith [hr.1] : 0 < 3 * r - 1)).mpr
  linarith [hr.2]

end Erdos1017.Benchmark
