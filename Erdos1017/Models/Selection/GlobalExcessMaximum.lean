module

public import Erdos1017.Benchmark.BenchmarkContinuity
public import Erdos1017.LowerBound.WeightedGraphBenchmarkLower
public import Mathlib.Topology.Order.Compact

/-!
# Positive global maximum of the excess

Failure of the benchmark upper bound gives a positive global maximum of the
excess strictly between the established endpoint regions, and since the lower
bound is already proved, any failure of equality produces the same maximizer.
-/

@[expose] public section

noncomputable section

namespace Erdos1017

open FractionalGraph

/-- Failure of the benchmark upper bound gives an actual positive global
maximum of the excess, strictly between the established endpoint regions. -/
theorem exists_positive_global_excess
    (hfailure : ∃ d ∈ Set.Icc (0 : ℝ) (1 / 2), benchmark d < densityLimit d) :
    ∃ d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2),
      0 < densityLimit d - benchmark d ∧
      ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
        densityLimit x - benchmark x ≤ densityLimit d - benchmark d := by
  obtain ⟨x, hx, hgap⟩ := hfailure
  have hcontinuous : ContinuousOn (fun d => densityLimit d - benchmark d)
      (Set.Icc (0 : ℝ) (1 / 2)) :=
    densityLimit_continuous.continuousOn.sub benchmark_continuousOn
  obtain ⟨d, hd, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨x, hx⟩ hcontinuous
  have hpositive : 0 < densityLimit d - benchmark d :=
    (sub_pos.mpr hgap).trans_le (hmax hx)
  have hquarter : (1 / 4 : ℝ) < d := by
    by_contra h
    have hdq : d ≤ 1 / 4 := le_of_not_gt h
    rw [densityLimit_eq_self d ⟨hd.1, hdq⟩, benchmark_of_le_quarter hdq] at hpositive
    linarith
  have hhalf : d < (1 / 2 : ℝ) := by
    by_contra h
    have heq : d = 1 / 2 := le_antisymm hd.2 (le_of_not_gt h)
    rw [heq, densityLimit_half, benchmark_half] at hpositive
    linarith
  exact ⟨d, ⟨hquarter, hhalf⟩, hpositive, fun x hx => hmax hx⟩

/-- The lower bound has already been proved, so any failure of equality
produces the same positive global maximizer used by the reduction. -/
theorem exists_positive_global_excess_of_ne
    (hfailure : ∃ d ∈ Set.Icc (0 : ℝ) (1 / 2), densityLimit d ≠ benchmark d) :
    ∃ d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2),
      0 < densityLimit d - benchmark d ∧
      ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
        densityLimit x - benchmark x ≤ densityLimit d - benchmark d := by
  apply exists_positive_global_excess
  obtain ⟨d, hd, hne⟩ := hfailure
  exact ⟨d, hd, lt_of_le_of_ne (WeightedGraph.benchmark_le_densityLimit d hd) hne.symm⟩

end Erdos1017
