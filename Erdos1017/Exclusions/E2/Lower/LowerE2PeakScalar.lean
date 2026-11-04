module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates

/-!
# Scalar facts for the lower `E₂` peak

The lower `E₂` pair floor stays above `2/49`, the threshold needed by square
majority; square majority with a missing cross block contradicts the `33/5`
pair-floor bound on the closed lower `E₂` range; and the saturated-score deficit
equals the gap times a correlated ratio, including the zero parameter.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.LowerE2Scalar

/-- The actual lower-E2 pair floor stays above the rational threshold
needed by original strict square majority. -/
theorem pairFloor_gt_two_fortyNine {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    (2 / 49 : ℝ) < pairFloor q := by
  have hR := denominator_pos hq.1
  have h2 : q ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ hq.1 hq.2 2
  have h4 : q ^ 4 ≤ (1 / 10 : ℝ) ^ 4 := pow_le_pow_left₀ hq.1 hq.2 4
  have h3 : 0 ≤ q ^ 3 := pow_nonneg hq.1 3
  have hRb : denominator q ≤ 171 / 100 := by
    unfold denominator
    nlinarith [hq.2]
  have hR2 : (denominator q) ^ 2 ≤ (171 / 100 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hR.le hRb 2
  apply (lt_div_iff₀ (by positivity : 0 < 16 * (denominator q) ^ 2)).mpr
  unfold pairNumerator
  nlinarith [hq.2]

/-- Original square majority and a missing cross block give a strict
contradiction to this bound throughout the entire closed lower-E2 range. -/
theorem missingMass_lt_thirtyThree_fifths_pairFloor {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    missingMass q < (33 / 5 : ℝ) * pairFloor q := by
  have hR := denominator_pos hq.1
  have hid : ((33 / 5 : ℝ) * pairFloor q - missingMass q) *
      (80 * (denominator q) ^ 2) =
      92 - 728 * q - 1977 * q ^ 2 + 1288 * q ^ 3 - 295 * q ^ 4 := by
    unfold pairFloor pairNumerator missingMass
    field_simp
    ring
  have hpositive : 0 < 92 - 728 * q - 1977 * q ^ 2 + 1288 * q ^ 3 - 295 * q ^ 4 := by
    by_cases hsmall : q ≤ 9 / 100
    · have h2 : q ^ 2 ≤ (9 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ hq.1 hsmall 2
      have h4 : q ^ 4 ≤ (9 / 100 : ℝ) ^ 4 := pow_le_pow_left₀ hq.1 hsmall 4
      have h3 : 0 ≤ q ^ 3 := pow_nonneg hq.1 3
      nlinarith
    · have h2 : q ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ hq.1 hq.2 2
      have h4 : q ^ 4 ≤ (1 / 10 : ℝ) ^ 4 := pow_le_pow_left₀ hq.1 hq.2 4
      have h3 : (9 / 100 : ℝ) ^ 3 ≤ q ^ 3 :=
        pow_le_pow_left₀ (by norm_num) (le_of_not_ge hsmall) 3
      nlinarith [hq.2]
  rw [← hid] at hpositive
  exact sub_pos.mp ((mul_pos_iff_of_pos_right (by positivity)).mp hpositive)

/-- The same family's saturated-score deficit has this exact correlated
ratio, including the zero parameter before any division by its slope gap. -/
theorem deficit_eq_gap_mul_ratio {q : ℝ} (hq : 0 ≤ q) :
    1 - multiplier q - 2 * gapFloor q =
      (1 - multiplier q) * (9 * q / (2 * denominator q)) := by
  have hR := ne_of_gt (denominator_pos hq)
  have hq2 : 2 + q ≠ 0 := by linarith
  unfold multiplier gapFloor
  field_simp
  unfold denominator
  ring

end Erdos1017.LowerE2Scalar
