module

public import Erdos1017.Exclusions.Common.Flows.FullForwardSelectorEnvelope
public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates

/-!
# Quarter bound for the forward selector envelope

The forward selector envelope is at most one quarter, obtained as a convex
combination of two exact bounds, and the quarter-envelope margin in the upper
lower-`E₂` range has positive numerator from `q = 2/15` onwards.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.ForwardPeak

/-- Only two split cells are needed beyond the elementary small-mass bound. -/
theorem twice_split_sub_sq_le_quarter {A : ℝ} (hA : A ∈ Icc (0 : ℝ) (1 / 4)) :
    2 * Benchmark.splitValue A - A ^ 2 ≤ 1 / 32 := by
  by_cases hsmall : A ≤ 1 / 6
  · have hs := (Benchmark.splitValue_bounds ⟨hA.1, by linarith [hA.2]⟩).2
    have hsq : A ^ 2 ≤ (1 / 6 : ℝ) ^ 2 := by gcongr; exact hA.1
    nlinarith
  by_cases hmiddle : A ≤ 1 / 5
  · have hc := Benchmark.splitValue_on_cell 4 (r := A)
      (by constructor <;> norm_num <;> linarith)
    norm_num [Benchmark.splitPolynomial] at hc
    have hp := mul_nonneg (sub_nonneg.mpr hmiddle)
      (show 0 ≤ 24 - 52 * (A + 1 / 5) by linarith)
    nlinarith
  · have hc := Benchmark.splitValue_on_cell 3 (r := A)
      (by constructor <;> norm_num <;> linarith [hA.2])
    norm_num [Benchmark.splitPolynomial] at hc
    have hp := mul_nonneg (sub_nonneg.mpr hA.2)
      (show 0 ≤ 20 - 38 * (A + 1 / 4) by linarith [hA.2])
    nlinarith

/-- The quarter envelope follows by a convex combination of two exact bounds. -/
theorem selectorEnvelope_le_quarter {ell A : ℝ}
    (hell : ell ∈ Icc (0 : ℝ) 1) (hA : A ∈ Icc (0 : ℝ) (1 / 4)) :
    selectorEnvelope ell A ≤ (4 - 3 * ell) / 32 := by
  have hsq : A ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by gcongr; exact hA.1; exact hA.2
  have hfirst := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2 * (1 - ell) by linarith [hell.2])
  have hsecond := mul_le_mul_of_nonneg_left (twice_split_sub_sq_le_quarter hA) hell.1
  unfold selectorEnvelope
  nlinarith

end Erdos1017.ForwardPeak

namespace Erdos1017.LowerE2Scalar

/-- Exact clearing of the upper lower-E2 quarter-envelope margin. -/
theorem quarter_gap_identity {q : ℝ} (hq : 0 ≤ q) :
    (gapFloor q - (4 - 3 * multiplier q) / 32) *
      (32 * denominator q * (q + 2)) = 25 * q ^ 3 + 29 * q ^ 2 + 11 * q - 2 := by
  have hR := (denominator_pos hq).ne'
  have hq2 : q + 2 ≠ 0 := by linarith
  unfold gapFloor multiplier
  field_simp
  unfold denominator
  ring

/-- The exact numerator is positive from q=2/15 onwards. -/
theorem quarter_gap_pos {q : ℝ} (hq : 2 / 15 ≤ q) :
    (4 - 3 * multiplier q) / 32 < gapFloor q := by
  have hq0 : 0 ≤ q := by linarith
  have hpoly : 0 < 25 * q ^ 3 + 29 * q ^ 2 + 11 * q - 2 := by
    have h2 : (2 / 15 : ℝ) ^ 2 ≤ q ^ 2 := by gcongr
    have h3 : (2 / 15 : ℝ) ^ 3 ≤ q ^ 3 := by gcongr
    nlinarith
  rw [← quarter_gap_identity hq0] at hpoly
  have hden : 0 < 32 * denominator q * (q + 2) := by
    have hR := denominator_pos hq0
    have hq2 : 0 < q + 2 := by linarith
    positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hpoly)

end Erdos1017.LowerE2Scalar
