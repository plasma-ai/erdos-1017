module

public import Erdos1017.Benchmark.BenchmarkFamilyGuards

/-!
# Low-density guards for the benchmark

The two-head value is at least the density, and above the low-window
missing-density endpoint the two-head curve uses its rational inverse branch and
lies above the baseline; low-density lower bounds for the benchmark
(`benchmark_ge_missing_of_low`, `benchmark_ge_third_of_low`) are included.
-/

@[expose] public section

namespace Erdos1017.Benchmark

theorem twoHeadValue_ge_density {z : ℝ} (hz : z ∈ Set.Icc (2 / 3 : ℝ) (4 / 5)) :
    twoHeadDensity z ≤ twoHeadValue z := by
  have hgap : 0 ≤ (3 * z - 2) ^ 2 * (1 - z) * (3 * z - 1) /
      (24 * twoHeadDenominator z ^ 2) :=
    div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith [hz.2]))
      (by linarith [hz.1])) (by positivity)
  unfold twoHeadValue
  linarith

/-- Above the low-window missing-density endpoint the actual two-head
curve uses its rational inverse branch and lies above the baseline. -/
theorem twoHeadCurve_ge_epsilon_of_eighth_le {ε : ℝ}
    (hε : ε ∈ Set.Icc (1 / 8 : ℝ) (1 / 4)) : ε ≤ twoHeadCurve ε := by
  have hεC : epsilonC < ε := by linarith [epsilonC_lt_nine_eightieths, hε.1]
  obtain ⟨hz, heq⟩ := twoHeadInverse_spec ⟨hεC.le, hε.2⟩
  have hε0 : ε ≠ 0 := by linarith [hε.1]
  simp only [twoHeadCurve, hε0, ite_false, not_le.mpr hεC]
  exact heq.symm.le.trans (twoHeadValue_ge_density ⟨hz.1, hz.2.trans (le_of_lt zC_lt_four_fifths)⟩)

theorem benchmark_ge_missing_of_low {d : ℝ} (hd : d ∈ Set.Icc (1 / 4 : ℝ) (3 / 8)) :
    1 / 2 - d ≤ benchmark d := by
  by_cases hquarter : d ≤ 1 / 4
  · rw [benchmark_of_le_quarter hquarter]
    linarith [hd.1]
  have hhalf : d < 1 / 2 := by linarith [hd.2]
  have hε : 1 / 2 - d ∈ Set.Icc (1 / 8 : ℝ) (1 / 4) := by constructor <;> linarith [hd.1, hd.2]
  simp only [benchmark, hquarter, ite_false, hhalf, ite_true]
  exact (twoHeadCurve_ge_epsilon_of_eighth_le hε).trans (le_max_right _ _)

theorem benchmark_ge_third_of_low {d : ℝ} (hd : d ∈ Set.Icc (1 / 4 : ℝ) (3 / 8)) :
    d / 3 ≤ benchmark d := by
  have h : d / 3 ≤ 1 / 2 - d := by linarith [hd.2]
  exact h.trans (benchmark_ge_missing_of_low hd)

end Erdos1017.Benchmark
