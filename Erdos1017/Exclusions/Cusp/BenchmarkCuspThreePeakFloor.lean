module

public import Erdos1017.Exclusions.Cusp.BenchmarkSplitCubicEnvelopes

/-!
# Split collision floor below the third-cusp peak threshold

Below the third-cusp peak threshold, the split collision term is at most the
third-cusp value minus its square (`splitValue_theta_le_one_twentySeventh`).
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- Below the third-cusp peak threshold, the exact split collision term
cannot exceed the original third-cusp value after subtracting its square. -/
theorem splitValue_theta_le_one_twentySeventh {A : ℝ}
    (hA : A ∈ Set.Icc (0 : ℝ) (11 / 39)) :
    2 * splitValue A - A ^ 2 ≤ 1 / 27 := by
  rcases le_total A (1 / 4) with hsmall | hlarge
  · have hcurve := splitValue_le_nineteen_twentieths ⟨hA.1, hsmall⟩
    have hAsq : A ^ 2 ≤ A / 4 := by nlinarith only [hA.1, hsmall]
    have hcoef : 0 ≤ 21 / 160 + (21 / 40) * A - (19 / 10) * A ^ 2 := by
      nlinarith only [hAsq, hA.1]
    have hpaid := mul_nonneg (by linarith only [hsmall] : (0 : ℝ) ≤ 1 / 4 - A) hcoef
    nlinarith only [hcurve, hpaid]
  · have hcell : A ∈ Set.Icc (1 / (((2 : ℕ) : ℝ) + 2)) (1 / (((2 : ℕ) : ℝ) + 1)) :=
      ⟨by linarith only [hlarge], by linarith only [hA.2]⟩
    rw [splitValue_on_cell 2 hcell]
    norm_num [splitPolynomial]
    have hpaid := mul_nonneg (by linarith only [hA.2] : (0 : ℝ) ≤ 11 / 39 - A)
      (by linarith only [hA.2] : (0 : ℝ) ≤ 1 / 3 - A)
    nlinarith only [hpaid]

end Erdos1017.Benchmark
