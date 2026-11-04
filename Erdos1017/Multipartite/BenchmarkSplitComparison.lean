module

public import Erdos1017.Benchmark.BenchmarkDenseHeadCountGuards
public import Erdos1017.Multipartite.BenchmarkLowDensityGuards
public import Erdos1017.Multipartite.TwoHead.TwoHeadFamilyBoundary

/-!
# Benchmark versus the split comparator

The explicit benchmark dominates its split comparator throughout the
density interval needed by the two-head family upper bound.
-/

@[expose] public section

namespace Erdos1017.Benchmark

theorem splitValue_le_benchmark {d : ℝ} (hd : d ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    splitValue (Real.sqrt (1 - 2 * d)) ≤ benchmark d := by
  by_cases hhalf : d = 1 / 2
  · subst d
    norm_num [splitValue]
  have hdhalf : d < 1 / 2 := lt_of_le_of_ne hd.2 hhalf
  have hr0 := Real.sqrt_nonneg (1 - 2 * d)
  have hrsq := Real.sq_sqrt (show 0 ≤ 1 - 2 * d by linarith)
  by_cases hlow : d ≤ 3 / 8
  · have hr : Real.sqrt (1 - 2 * d) ∈ Set.Icc (1 / 2 : ℝ) 1 := by
      constructor <;> nlinarith [hd.1]
    have hsplit := splitValue_on_cell 0 (r := Real.sqrt (1 - 2 * d)) (by
      norm_num only [Nat.cast_zero, zero_add, one_div_one]
      exact hr)
    have hbound : splitValue (Real.sqrt (1 - 2 * d)) ≤ 1 / 2 - d := by
      rw [hsplit]
      norm_num [splitPolynomial]
      nlinarith [sq_nonneg (Real.sqrt (1 - 2 * d) - 1 / 2)]
    exact hbound.trans (benchmark_ge_missing_of_low ⟨hd.1, hlow⟩)
  · have hdlo : 3 / 8 < d := lt_of_not_ge hlow
    have hquarter : 1 / 4 < d := by linarith
    have hepos : 0 < 1 / 2 - d := by linarith
    have hsqrt : Real.sqrt (2 * (1 / 2 - d)) = Real.sqrt (1 - 2 * d) := by
      congr 1
      ring
    have hmax : mixedCurve (1 / 2 - d) ≤ benchmark d := by
      simp only [benchmark, not_le.mpr hquarter, ite_false, hdhalf, ite_true]
      exact le_max_left _ _
    by_cases he : 1 / 2 - d ≤ epsilonStar
    · have heq : mixedCurve (1 / 2 - d) = splitValue (Real.sqrt (1 - 2 * d)) := by
        simp only [mixedCurve, he, ite_true, hsqrt]
      rwa [heq] at hmax
    · have heS : epsilonStar < 1 / 2 - d := lt_of_not_ge he
      have heD : 1 / 2 - d ≤ epsilonD := by linarith [eighth_lt_epsilonD]
      have hr : Real.sqrt (2 * (1 / 2 - d)) ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) := by
        rw [hsqrt]
        constructor <;> nlinarith [two_twenty_fifths_lt_epsilonStar]
      have hsplit := split_lt_mixedCurve ⟨heS, heD⟩ hr
      rw [hsqrt] at hsplit
      exact hsplit.le.trans hmax

theorem benchmark_ge_missing {d : ℝ} (hd : d ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    1 / 2 - d ≤ benchmark d := by
  by_cases hlow : d ≤ 3 / 8
  · exact benchmark_ge_missing_of_low ⟨hd.1, hlow⟩
  have hdhi : 3 / 8 < d := lt_of_not_ge hlow
  have hr0 := Real.sqrt_nonneg (1 - 2 * d)
  have hrsq := Real.sq_sqrt (show 0 ≤ 1 - 2 * d by linarith [hd.2])
  have hrhi : Real.sqrt (1 - 2 * d) ≤ 1 / 2 := by nlinarith
  have hlower := TwoHeadFamilyBoundary.splitValue_lower_bound
    (show Real.sqrt (1 - 2 * d) ∈ Set.Icc (0 : ℝ) 1 from ⟨hr0, by linarith⟩)
  have hgap := mul_nonneg (sq_nonneg (Real.sqrt (1 - 2 * d)))
    (show 0 ≤ 1 / 2 - Real.sqrt (1 - 2 * d) by linarith)
  have hbase : 1 / 2 - d ≤ splitValue (Real.sqrt (1 - 2 * d)) := by nlinarith
  exact hbase.trans (splitValue_le_benchmark hd)

theorem twoHeadCurve_le_benchmark {d : ℝ} (hd : d ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    twoHeadCurve (1 / 2 - d) ≤ benchmark d := by
  by_cases hhalf : d = 1 / 2
  · subst d
    norm_num
  by_cases hquarter : d = 1 / 4
  · subst d
    norm_num [benchmark]
  have hdhalf : d < 1 / 2 := lt_of_le_of_ne hd.2 hhalf
  have hdquarter : 1 / 4 < d := lt_of_le_of_ne hd.1 (Ne.symm hquarter)
  simp only [benchmark, not_le.mpr hdquarter, ite_false, hdhalf, ite_true]
  exact le_max_right _ _

end Erdos1017.Benchmark
