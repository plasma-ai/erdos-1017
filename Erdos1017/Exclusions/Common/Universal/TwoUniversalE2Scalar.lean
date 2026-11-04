module

public import Erdos1017.Benchmark.BenchmarkE2Activity

/-!
# Scalar support inequality for two universal heads at `E₂`

This module defines the scalar width from the `E₂` cost and multiplier and the
correlated two-head support polynomial, and shows the polynomial is positive at
the `E₂` value throughout `0 < q ≤ 1/5`, with the benchmark gap supplying the
inequality.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.TwoUniversalE2Scalar

/-- The actual scalar width determined by the old E2 cost and multiplier. -/
def width (q c : ℝ) : ℝ :=
  2 * (2 * c - LowerE2Scalar.multiplier q * LowerE2Scalar.missingMass q) /
    (1 - LowerE2Scalar.multiplier q)

/-- The correlated two-universal-head support expression at the actual E2 parameter. -/
def supportPolynomial (q s v T : ℝ) : ℝ :=
  (1 - LowerE2Scalar.multiplier q) * (s - 2 * LowerE2Scalar.missingMass q) -
    2 * LowerE2Scalar.multiplier q * v ^ 2 + (2 * s - 1) * T - (1 - s) ^ 2 / 12 +
      (12 / 25) *
        max ((1 + LowerE2Scalar.multiplier q) * v - T - (1 - s) / 12) 0 ^ 2

private def referenceRemainder (q : ℝ) : ℝ := 9 * q / (2 * LowerE2Scalar.denominator q)

private def referenceDifference (q : ℝ) : ℝ :=
  3 * q * (q + 2) / (2 * LowerE2Scalar.denominator q)

private def squareExpression (ell h s v T : ℝ) : ℝ :=
  (1 - ell) * (s - 2 * h) - 2 * ell * v ^ 2 + (2 * s - 1) * T -
    (1 - s) ^ 2 / 12 + (12 / 25) * ((1 + ell) * v - T - (1 - s) / 12) ^ 2

private def circleWeight (ell : ℝ) : ℝ := 2 * ell - 9 * (1 + ell) ^ 2 / 20

private def truncatedExpression (ell h s v T : ℝ) : ℝ :=
  (1 - ell) * (s - 2 * h) - 2 * ell * v ^ 2 + (2 * s - 1) * T -
    (1 - s) ^ 2 / 12 + (12 / 25) * max ((1 + ell) * v - T - (1 - s) / 12) 0 ^ 2

private theorem reference_circle {q : ℝ} (hq : 0 ≤ q) :
    (1 - referenceRemainder q) ^ 2 + referenceDifference q ^ 2 =
      2 * LowerE2Scalar.missingMass q := by
  have hR := (LowerE2Scalar.denominator_pos hq).ne'
  unfold referenceRemainder referenceDifference LowerE2Scalar.missingMass
  field_simp [hR]
  simp only [LowerE2Scalar.denominator]
  ring

private theorem reference_difference {q : ℝ} (hq : 0 ≤ q) :
    (1 + LowerE2Scalar.multiplier q) * referenceDifference q =
      4 * referenceRemainder q / 3 := by
  have hR := (LowerE2Scalar.denominator_pos hq).ne'
  have hq2 : q + 2 ≠ 0 := by linarith
  unfold referenceRemainder referenceDifference LowerE2Scalar.multiplier
  field_simp [hR, hq2]
  ring

private theorem reference_width {q : ℝ} (hq : 0 ≤ q) :
    2 * LowerE2Scalar.gapFloor q =
      (1 - LowerE2Scalar.multiplier q) * (1 - referenceRemainder q) := by
  have hR := (LowerE2Scalar.denominator_pos hq).ne'
  have hq2 : q + 2 ≠ 0 := by linarith
  unfold referenceRemainder LowerE2Scalar.gapFloor LowerE2Scalar.multiplier
  field_simp [hR, hq2]
  simp only [LowerE2Scalar.denominator]
  ring

private theorem reference_zero {q : ℝ} (hq : 0 ≤ q) :
    squareExpression (LowerE2Scalar.multiplier q) (LowerE2Scalar.missingMass q)
      (1 - referenceRemainder q) (referenceDifference q) 0 = 0 := by
  have hR := (LowerE2Scalar.denominator_pos hq).ne'
  have hq2 : q + 2 ≠ 0 := by linarith
  unfold squareExpression referenceRemainder referenceDifference
    LowerE2Scalar.multiplier LowerE2Scalar.missingMass
  field_simp [hR, hq2]
  simp only [LowerE2Scalar.denominator]
  ring

private theorem squareExpression_sos (ell r v₀ h s v T : ℝ) (hm : 0 < 1 + ell)
    (hv₀ : (1 + ell) * v₀ = 4 * r / 3)
    (hh : (1 - r) ^ 2 + v₀ ^ 2 = 2 * h) :
    squareExpression ell h s v T - circleWeight ell * (2 * h - s ^ 2 - v ^ 2) =
      squareExpression ell h (1 - r) v₀ 0 +
        (4 * r / 15 + 2 * circleWeight ell * (1 - r)) * (s - (1 - r)) +
        (2 - 16 * r / 5) * T + ((1 - ell) * (s - (1 - r)) - T) +
        (3 / 100) * ((1 + ell) * (v₀ - v) - (4 / 3) * (s - (1 - r))) ^ 2 +
        (circleWeight ell - 2 / 15) * (s - (1 - r)) ^ 2 + (12 / 25) * T ^ 2 +
        (24 / 25) * (1 + ell) * T * (v₀ - v) + (48 / 25) * (s - (1 - r)) * T := by
  have hv : v₀ = 4 * r / (3 * (1 + ell)) := by
    apply (eq_div_iff (by positivity : 3 * (1 + ell) ≠ 0)).mpr
    nlinarith only [hv₀]
  have he : h = ((1 - r) ^ 2 + v₀ ^ 2) / 2 := by linarith only [hh]
  rw [he, hv]
  unfold squareExpression circleWeight
  field_simp [hm.ne']
  ring

private theorem circleWeight_lower {ell : ℝ} (hell : ell ∈ Icc (9 / 11 : ℝ) 1) :
    2 / 15 ≤ circleWeight ell := by
  have hp : 0 ≤ (ell - 9 / 11) * (2 - 9 * (ell + 31 / 11) / 20) :=
    mul_nonneg (sub_nonneg.mpr hell.1) (by linarith only [hell.2])
  unfold circleWeight
  nlinarith only [hp]

private theorem squareExpression_strict_lower (ell r v₀ h s v T : ℝ)
    (hell : ell ∈ Icc (9 / 11 : ℝ) 1) (hr : r ∈ Ioc (0 : ℝ) (1 / 2))
    (hv₀ : (1 + ell) * v₀ = 4 * r / 3)
    (hh : (1 - r) ^ 2 + v₀ ^ 2 = 2 * h)
    (hbase : squareExpression ell h (1 - r) v₀ 0 = 0)
    (hs : 1 - r < s) (hvv : v ≤ v₀) (hT : 0 ≤ T)
    (hupper : T ≤ (1 - ell) * (s - (1 - r))) :
    0 < squareExpression ell h s v T - circleWeight ell * (2 * h - s ^ 2 - v ^ 2) := by
  have hm : 0 < 1 + ell := by linarith only [hell.1]
  have hweight := circleWeight_lower hell
  have hweight0 : 0 ≤ circleWeight ell := by linarith only [hweight]
  have hweight' : 0 ≤ circleWeight ell - 2 / 15 := sub_nonneg.mpr hweight
  have hr' : 0 ≤ 1 - r := by linarith only [hr.2]
  have hs' : 0 ≤ s - (1 - r) := (sub_pos.mpr hs).le
  have hv' : 0 ≤ v₀ - v := sub_nonneg.mpr hvv
  have hfirst : 0 < (4 * r / 15 + 2 * circleWeight ell * (1 - r)) * (s - (1 - r)) := by
    apply mul_pos _ (sub_pos.mpr hs)
    have hprod : 0 ≤ 2 * circleWeight ell * (1 - r) := by positivity
    linarith only [hr.1, hprod]
  have hsecond : 0 ≤ (2 - 16 * r / 5) * T :=
    mul_nonneg (by linarith only [hr.2]) hT
  have hgap : 0 ≤ (1 - ell) * (s - (1 - r)) - T := sub_nonneg.mpr hupper
  have hsq : 0 ≤ (3 / 100 : ℝ) *
      ((1 + ell) * (v₀ - v) - (4 / 3) * (s - (1 - r))) ^ 2 := by positivity
  have hsq' : 0 ≤ (circleWeight ell - 2 / 15) * (s - (1 - r)) ^ 2 := by positivity
  have hT₂ : 0 ≤ (12 / 25 : ℝ) * T ^ 2 := by positivity
  have hcross : 0 ≤ (24 / 25 : ℝ) * (1 + ell) * T * (v₀ - v) := by positivity
  have hcross' : 0 ≤ (48 / 25 : ℝ) * (s - (1 - r)) * T := by positivity
  rw [squareExpression_sos ell r v₀ h s v T hm hv₀ hh, hbase]
  linarith only [hfirst, hsecond, hgap, hsq, hsq', hT₂, hcross, hcross']

private theorem truncatedExpression_pos (ell r v₀ h s v T : ℝ)
    (hell : ell ∈ Icc (9 / 11 : ℝ) 1) (hr : r ∈ Ioc (0 : ℝ) (1 / 2))
    (hv₀ : (1 + ell) * v₀ = 4 * r / 3)
    (hh : (1 - r) ^ 2 + v₀ ^ 2 = 2 * h)
    (hbase : squareExpression ell h (1 - r) v₀ 0 = 0)
    (hs : 1 - r < s) (hs1 : s < 1) (hv : 0 ≤ v)
    (hcircle : s ^ 2 + v ^ 2 ≤ 2 * h) (hT : 0 ≤ T)
    (hupper : T ≤ (1 - ell) * (s - (1 - r))) :
    0 < truncatedExpression ell h s v T := by
  have hm : 0 < 1 + ell := by linarith only [hell.1]
  have hweight := circleWeight_lower hell
  have hweight0 : 0 ≤ circleWeight ell := by linarith only [hweight]
  have hcircle' : 0 ≤ 2 * h - s ^ 2 - v ^ 2 := by linarith only [hcircle]
  have hslack : 0 ≤ circleWeight ell * (2 * h - s ^ 2 - v ^ 2) := by positivity
  have hvpos : 0 < v₀ := (mul_pos_iff_of_pos_left hm).mp (by linarith only [hv₀, hr.1])
  by_cases hactive : 0 ≤ (1 + ell) * v - T - (1 - s) / 12
  · have hvv : v ≤ v₀ := by
      have hsquare : (1 - r) ^ 2 ≤ s ^ 2 := by
        simpa only [pow_two] using
          mul_self_le_mul_self (by linarith only [hr.2] : 0 ≤ 1 - r) hs.le
      nlinarith only [hh, hcircle, hsquare, hv, hvpos]
    have hpos := squareExpression_strict_lower ell r v₀ h s v T hell hr hv₀ hh
      hbase hs hvv hT hupper
    have he : truncatedExpression ell h s v T = squareExpression ell h s v T := by
      unfold truncatedExpression squareExpression
      rw [max_eq_left hactive]
    rw [he]
    linarith only [hpos, hslack]
  · let v₁ := (T + (1 - s) / 12) / (1 + ell)
    have hv₁ : (1 + ell) * v₁ = T + (1 - s) / 12 := by
      dsimp only [v₁]
      exact mul_div_cancel₀ _ hm.ne'
    have hvv₁ : v ≤ v₁ := by
      apply (le_div_iff₀ hm).mpr
      nlinarith only [le_of_not_ge hactive]
    have hsmallT : T ≤ s - (1 - r) := by
      have hp := mul_le_mul_of_nonneg_right
        (show 1 - ell ≤ 1 by linarith only [hell.1]) (sub_pos.mpr hs).le
      linarith only [hupper, hp]
    have hv₁v : v₁ ≤ v₀ := by
      apply (div_le_iff₀ hm).mpr
      nlinarith only [hv₀, hsmallT, hs1, hr.1]
    have hpos := squareExpression_strict_lower ell r v₀ h s v₁ T hell hr hv₀ hh
      hbase hs hv₁v hT hupper
    have hzero : (1 + ell) * v₁ - T - (1 - s) / 12 = 0 := by
      linarith only [hv₁]
    have he : truncatedExpression ell h s v T -
        circleWeight ell * (2 * h - s ^ 2 - v ^ 2) =
      squareExpression ell h s v₁ T - circleWeight ell * (2 * h - s ^ 2 - v₁ ^ 2) +
        (9 / 20) * (1 + ell) ^ 2 * (v₁ ^ 2 - v ^ 2) := by
      unfold truncatedExpression squareExpression
      rw [max_eq_right (le_of_not_ge hactive), hzero]
      unfold circleWeight
      ring
    have hremaining : 0 ≤ (9 / 20 : ℝ) * (1 + ell) ^ 2 * (v₁ ^ 2 - v ^ 2) := by
      have hsq : v ^ 2 ≤ v₁ ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self hv hvv₁
      have hd : 0 ≤ v₁ ^ 2 - v ^ 2 := sub_nonneg.mpr hsq
      positivity
    linarith only [he, hpos, hslack, hremaining]

/-- The correlated support expression is positive for the actual
E2 value throughout `0 < q ≤ 1/5`. -/
theorem supportPolynomial_pos_of_twoHeadValue_lt {q c s v T : ℝ}
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hc : Benchmark.twoHeadValue ((q + 2) / 3) < c)
    (hs : width q c ≤ s) (hs1 : s < 1) (hv : 0 ≤ v)
    (hcircle : s ^ 2 + v ^ 2 ≤ 2 * LowerE2Scalar.missingMass q)
    (hT : T = (1 - LowerE2Scalar.multiplier q) * (s - width q c)) :
    0 < supportPolynomial q s v T := by
  have hR := LowerE2Scalar.denominator_pos hq.1.le
  have hq2 : 0 < 2 + q := by linarith only [hq.1]
  have hell : LowerE2Scalar.multiplier q ∈ Icc (9 / 11 : ℝ) 1 := by
    unfold LowerE2Scalar.multiplier
    constructor
    · apply (le_div_iff₀ hq2).mpr
      linarith only [hq.2]
    · apply (div_le_one hq2).mpr
      linarith only [hq.1]
  have hdelta : 0 < 1 - LowerE2Scalar.multiplier q := by
    unfold LowerE2Scalar.multiplier
    have he : (2 - q) / (2 + q) < 1 := (div_lt_one hq2).mpr (by linarith only [hq.1])
    linarith only [he]
  have hr : referenceRemainder q ∈ Ioc (0 : ℝ) (1 / 2) := by
    unfold referenceRemainder
    constructor
    · exact div_pos (by linarith only [hq.1]) (by positivity)
    · apply (div_le_iff₀ (by positivity : 0 < 2 * LowerE2Scalar.denominator q)).mpr
      unfold LowerE2Scalar.denominator
      nlinarith only [sq_nonneg (q - 1)]
  have hw : 1 - referenceRemainder q < width q c := by
    unfold width
    apply (lt_div_iff₀ hdelta).mpr
    have hreference := reference_width hq.1.le
    have hvalue := LowerE2Scalar.gapFloor_eq_twoHeadValue hq.1.le
    nlinarith only [hc, hreference, hvalue]
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact mul_nonneg hdelta.le (sub_nonneg.mpr hs)
  have hupper : T ≤ (1 - LowerE2Scalar.multiplier q) *
      (s - (1 - referenceRemainder q)) := by
    rw [hT]
    exact mul_le_mul_of_nonneg_left (by linarith only [hw]) hdelta.le
  change 0 < truncatedExpression (LowerE2Scalar.multiplier q)
    (LowerE2Scalar.missingMass q) s v T
  exact truncatedExpression_pos _ _ _ _ _ _ _ hell hr (reference_difference hq.1.le)
    (reference_circle hq.1.le) (reference_zero hq.1.le) (hw.trans_le hs) hs1 hv hcircle hT0 hupper

/-- The actual benchmark gap supplies the correlated support inequality;
the benchmark branch and stationary endpoint identity are derived internally. -/
theorem supportPolynomial_pos {q c s v T : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hc : benchmark ((1 - LowerE2Scalar.missingMass q) / 2) < c)
    (hs : width q c ≤ s) (hs1 : s < 1) (hv : 0 ≤ v)
    (hcircle : s ^ 2 + v ^ 2 ≤ 2 * LowerE2Scalar.missingMass q)
    (hT : T = (1 - LowerE2Scalar.multiplier q) * (s - width q c)) :
    0 < supportPolynomial q s v T := by
  rw [Benchmark.benchmark_e2_q hq] at hc
  exact supportPolynomial_pos_of_twoHeadValue_lt hq hc hs hs1 hv hcircle hT

end Erdos1017.TwoUniversalE2Scalar
