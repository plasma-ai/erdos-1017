module

public import Erdos1017.Exclusions.Cusp.BenchmarkSplitCubicEnvelopes
public import Erdos1017.Exclusions.Cusp.CuspOutsideSmallRangeCertificates

/-!
# Squared caps for the small-count outside gaps

For reciprocal counts six, seven and eight, the split-value gap and the coarse
normalized source range give the strict cell and squared cap, using the cubic
envelopes where needed.
-/

@[expose] public section

namespace Erdos1017.CuspOutsideSmallCaps

/-- The count-six actual split-value gap derives its remaining strict cell
and squared cap from the coarse normalized source range. -/
theorem outside_six_cap {ell x : ℝ} (hx0 : 0 ≤ x) (hbase : 27 / 13 ≤ x ^ 2)
    (hx2 : x < 2) (hell : 29 / 21 ≤ ell)
    (hgap : 0 < 36 * Benchmark.splitValue (x / 6) - 5 / 6 - ell * (x ^ 2 - 1) / 2) :
    x / 6 ∈ Set.Ioo (1 / 5 : ℝ) (1 / 4) ∧ x ^ 2 < 11 / 5 := by
  have hrlo : 1 / 5 < x / 6 := by
    by_contra hnot
    have hupper : x ≤ 6 / 5 := by linarith
    have hsq := mul_le_mul hupper hupper hx0 (by norm_num : (0 : ℝ) ≤ 6 / 5)
    nlinarith
  have hslope := mul_nonneg (sub_nonneg.mpr hell) (show 0 ≤ x ^ 2 - 1 by linarith)
  have hgapLower :
      0 < 36 * Benchmark.splitValue (x / 6) - 5 / 6 - (29 / 21) * (x ^ 2 - 1) / 2 := by
    nlinarith
  have hrhi : x / 6 < 1 / 4 := by
    by_contra hnot
    have hcell : Benchmark.splitValue (x / 6) = Benchmark.splitPolynomial 3 (x / 6) := by
      apply Benchmark.splitValue_on_cell 2
      norm_num
      constructor <;> linarith
    rw [hcell] at hgapLower
    norm_num [Benchmark.splitPolynomial] at hgapLower
    have hnegative := CuspOutsideSmallRange.six_cell_three_neg x
    nlinarith
  have hcell : Benchmark.splitValue (x / 6) = Benchmark.splitPolynomial 4 (x / 6) := by
    apply Benchmark.splitValue_on_cell 3
    norm_num
    constructor <;> linarith
  have hcap : x ^ 2 < 11 / 5 := by
    by_contra hnot
    have hnegative := CuspOutsideSmallRange.six_cell_four_neg (le_of_not_gt hnot)
    rw [hcell] at hgapLower
    norm_num [Benchmark.splitPolynomial] at hgapLower
    nlinarith
  exact ⟨⟨hrlo, hrhi⟩, hcap⟩

/-- The count-seven actual split-value gap supplies its own cubic envelope,
then derives the strict cell and squared cap. -/
theorem outside_seven_cap {ell x : ℝ} (hx0 : 0 ≤ x) (hbase : 7 / 3 ≤ x ^ 2)
    (hx2 : x < 2) (hell : 41 / 28 ≤ ell)
    (hgap : 0 < 49 * Benchmark.splitValue (x / 7) - 6 / 7 - ell * (x ^ 2 - 1) / 2) :
    x / 7 ∈ Set.Ioo (1 / 5 : ℝ) (1 / 4) ∧ x ^ 2 < 51 / 20 := by
  have hr : x / 7 ∈ Set.Icc (0 : ℝ) (1 / 3) := ⟨by linarith, by linarith⟩
  have hbound := Benchmark.splitValue_le_fifteen_sixteenths hr
  have hD : 7 * (1 - ell / 2) ≤ 15 / 8 := by linarith
  have henv : 0 < (7 * (1 - ell / 2)) * (x ^ 2 - 1) + 1 - (15 / 16) * x ^ 3 := by
    nlinarith
  have hxhi : x < 7 / 4 := by
    by_contra hnot
    have hnegative := CuspOutsideSmallRange.seven_envelope_bound hD (le_of_not_gt hnot)
    linarith
  have hrlo : 1 / 5 < x / 7 := by
    by_contra hnot
    have hupper : x ≤ 7 / 5 := by linarith
    have hsq := mul_le_mul hupper hupper hx0 (by norm_num : (0 : ℝ) ≤ 7 / 5)
    nlinarith
  have hrhi : x / 7 < 1 / 4 := by linarith
  have hslope := mul_nonneg (sub_nonneg.mpr hell) (show 0 ≤ x ^ 2 - 1 by linarith)
  have hgapLower :
      0 < 49 * Benchmark.splitValue (x / 7) - 6 / 7 - (41 / 28) * (x ^ 2 - 1) / 2 := by
    nlinarith
  have hcell : Benchmark.splitValue (x / 7) = Benchmark.splitPolynomial 4 (x / 7) := by
    apply Benchmark.splitValue_on_cell 3
    norm_num
    constructor <;> linarith
  have hcap : x ^ 2 < 51 / 20 := by
    by_contra hnot
    have hnegative := CuspOutsideSmallRange.seven_cell_four_neg (le_of_not_gt hnot)
    rw [hcell] at hgapLower
    norm_num [Benchmark.splitPolynomial] at hgapLower
    nlinarith
  exact ⟨⟨hrlo, hrhi⟩, hcap⟩

/-- The count-eight actual split-value gap and coarse source range imply
the squared cap through the derived nineteen-twentieths envelope. -/
theorem outside_eight_cap {ell x : ℝ} (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hell : 55 / 36 ≤ ell)
    (hgap : 0 < 64 * Benchmark.splitValue (x / 8) - 7 / 8 - ell * (x ^ 2 - 1) / 2) :
    x ^ 2 < 25 / 9 := by
  have hr : x / 8 ∈ Set.Icc (0 : ℝ) (1 / 4) := ⟨by linarith, by linarith⟩
  have hbound := Benchmark.splitValue_le_nineteen_twentieths hr
  have hD : 8 * (1 - ell / 2) ≤ 17 / 9 := by linarith
  have henv : 0 < (8 * (1 - ell / 2)) * (x ^ 2 - 1) + 1 - (19 / 20) * x ^ 3 := by
    nlinarith
  have hxhi : x < 5 / 3 := by
    by_contra hnot
    have hnegative := CuspOutsideSmallRange.eight_envelope_bound hD (le_of_not_gt hnot)
    linarith
  nlinarith

end Erdos1017.CuspOutsideSmallCaps
