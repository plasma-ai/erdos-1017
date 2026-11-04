module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates

/-!
# Parameter guards on the upper `E₂` interval

Exact missing-mass guards hold on the closed upper-`E₂` scalar interval, the
family multiplier has exact open and closed bounds, the shifted-row floor is at
least its left endpoint value, and the stationary two-head value exceeds the
strict upper-`E₂` cost guard.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.UpperE2Parameter

open LowerE2Scalar

/-- Exact missing-mass guards on the entire closed upper-E2 scalar interval. -/
theorem missingMass_mem {q : ℝ} (hq : q ∈ Set.Icc (1 / 5 : ℝ) (213 / 1000)) :
    missingMass q ∈ Set.Ioc (23 / 100 : ℝ) (3509 / 14884) := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have h2 : q ^ 2 ≤ (213 / 1000 : ℝ) ^ 2 := pow_le_pow_left₀ hq0 hq.2 2
  have h3 : (1 / 5 : ℝ) ^ 3 ≤ q ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hq.1 3
  have h3' : q ^ 3 ≤ (213 / 1000 : ℝ) ^ 3 := pow_le_pow_left₀ hq0 hq.2 3
  have h4 : (1 / 5 : ℝ) ^ 4 ≤ q ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hq.1 4
  constructor
  · have hid : (missingMass q - 23 / 100) * (800 * denominator q ^ 2) =
        216 - 576 * q - 2484 * q ^ 2 + 3024 * q ^ 3 + 1116 * q ^ 4 := by
      unfold missingMass
      field_simp
      simp only [denominator]
      ring
    have hpoly : 0 < 216 - 576 * q - 2484 * q ^ 2 + 3024 * q ^ 3 + 1116 * q ^ 4 := by
      norm_num at h2 h3 h4
      linarith [hq.2]
    rw [← hid] at hpoly
    exact sub_pos.mp ((mul_pos_iff_of_pos_right (by positivity)).mp hpoly)
  · have hid : (3509 / 14884 - missingMass q) * (29768 * denominator q ^ 2) =
        (5 * q - 1) * (7866 + 15498 * q - 23679 * q ^ 2 - 8271 * q ^ 3) := by
      unfold missingMass
      field_simp
      simp only [denominator]
      ring
    have hpoly : 0 ≤ 7866 + 15498 * q - 23679 * q ^ 2 - 8271 * q ^ 3 := by
      norm_num at h2 h3'
      linarith
    have hprod := mul_nonneg (show 0 ≤ 5 * q - 1 by linarith [hq.1]) hpoly
    rw [← hid] at hprod
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (by positivity)).mp hprod)

/-- The literal family multiplier has these exact open and closed bounds. -/
theorem multiplier_mem {q : ℝ} (hq : q ∈ Set.Icc (1 / 5 : ℝ) (213 / 1000)) :
    multiplier q ∈ Set.Ioc (4 / 5 : ℝ) (9 / 11) := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hden : 0 < 2 + q := by linarith
  unfold multiplier
  constructor
  · apply (lt_div_iff₀ hden).mpr
    linarith [hq.2]
  · apply (div_le_iff₀ hden).mpr
    linarith [hq.1]

/-- The upper-E2 shifted-row floor is at least its left endpoint value. -/
theorem gapFloor_ge {q : ℝ} (hq : q ∈ Set.Icc (1 / 5 : ℝ) (213 / 1000)) :
    (7 / 122 : ℝ) ≤ gapFloor q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have hid : (gapFloor q - 7 / 122) * (122 * denominator q) =
      (5 * q - 1) * (23 * q + 7) := by
    unfold gapFloor
    field_simp
    simp only [denominator]
    ring
  have hprod := mul_nonneg (show 0 ≤ 5 * q - 1 by linarith [hq.1])
    (show 0 ≤ 23 * q + 7 by linarith)
  rw [← hid] at hprod
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (by positivity)).mp hprod)

/-- The ratio uses the same literal floor and multiplier at the same parameter. -/
theorem gapFloor_div_multiplier_ge {q : ℝ}
    (hq : q ∈ Set.Icc (1 / 5 : ℝ) (213 / 1000)) :
    (77 / 1098 : ℝ) ≤ gapFloor q / multiplier q := by
  have hell := multiplier_mem hq
  have hfloor := gapFloor_ge hq
  apply (le_div_iff₀ (show 0 < multiplier q by linarith [hell.1])).mpr
  linarith [hell.2]

/-- A correlated affine floor retains the actual family multiplier. -/
theorem gapFloor_ge_correlated {q : ℝ}
    (hq : q ∈ Set.Icc (1 / 5 : ℝ) (213 / 1000)) :
    16477 / 67100 - (23 / 100) * multiplier q ≤ gapFloor q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have hq2 : 2 + q ≠ 0 := by linarith
  have h2 : (1 / 5 : ℝ) ^ 2 ≤ q ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hq.1 2
  have hid : (gapFloor q + (23 / 100) * multiplier q - 16477 / 67100) *
      (67100 * denominator q * (q + 2)) =
      (5 * q - 1) * (2088 - 10134 * q + 7038 * q ^ 2) := by
    unfold gapFloor multiplier
    field_simp
    simp only [denominator]
    ring
  have hpoly : 0 ≤ 2088 - 10134 * q + 7038 * q ^ 2 := by
    norm_num at h2
    linarith [hq.2]
  have hprod := mul_nonneg (show 0 ≤ 5 * q - 1 by linarith [hq.1]) hpoly
  rw [← hid] at hprod
  have hnonneg := (mul_nonneg_iff_of_pos_right (by positivity)).mp hprod
  linarith

/-- The actual stationary two-head value exceeds the strict upper-E2 cost guard. -/
theorem twoHeadValue_gt {q : ℝ} (hq : q ∈ Set.Icc (1 / 5 : ℝ) (213 / 1000)) :
    (123 / 1000 : ℝ) < Benchmark.twoHeadValue ((q + 2) / 3) := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have hq2 : 2 + q ≠ 0 := by linarith
  have h2 : q ^ 2 ≤ (213 / 1000 : ℝ) ^ 2 := pow_le_pow_left₀ hq0 hq.2 2
  have h3 : (1 / 5 : ℝ) ^ 3 ≤ q ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hq.1 3
  have h4 : q ^ 4 ≤ (213 / 1000 : ℝ) ^ 4 := pow_le_pow_left₀ hq0 hq.2 4
  have hvalue : Benchmark.twoHeadValue ((q + 2) / 3) =
      (gapFloor q + multiplier q * missingMass q) / 2 := by
    linarith [gapFloor_eq_twoHeadValue hq0]
  have hid : (Benchmark.twoHeadValue ((q + 2) / 3) - 123 / 1000) *
      (16000 * denominator q ^ 2) =
      2032 - 7552 * q - 13368 * q ^ 2 + 28448 * q ^ 3 - 6968 * q ^ 4 := by
    rw [hvalue]
    unfold gapFloor multiplier missingMass
    field_simp
    simp only [denominator]
    ring
  have hpoly : 0 < 2032 - 7552 * q - 13368 * q ^ 2 + 28448 * q ^ 3 - 6968 * q ^ 4 := by
    norm_num at h2 h3 h4
    linarith [hq.2]
  rw [← hid] at hpoly
  exact sub_pos.mp ((mul_pos_iff_of_pos_right (by positivity)).mp hpoly)

end Erdos1017.UpperE2Parameter
