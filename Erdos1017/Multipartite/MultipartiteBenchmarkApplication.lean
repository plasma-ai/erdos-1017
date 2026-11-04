module

public import Erdos1017.Multipartite.MultipartiteWindowComparison
public import Erdos1017.Multipartite.MultipartiteTrivialBound
public import Erdos1017.Multipartite.MultipartiteDenseComparison
public import Erdos1017.Multipartite.MultipartiteLowDensityComparison
public import Erdos1017.Multipartite.BenchmarkLowDensityGuards

/-!
# Applying the benchmark to normalized profiles

The normalized edge density is expressed through the two compact moments, and
the structural, collision and low-density arguments cover all normalized
multipartite profile densities, leaving only the one-head family bound as a
premise.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteProfiles

open scoped BigOperators

/-- Actual normalized edge density in terms of the two compact moments. -/
theorem density_eq_normalized_edge_mass {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    density x = (x.1 + (x.1 ^ 2 - ∑' i, (x.2 i) ^ 2) / 2) / (1 + x.1) ^ 2 := by
  have hM : 0 < 1 + x.1 := by linarith [hx.1.1.1]
  unfold density missingDensity
  field_simp
  ring

/-- The genuine fixed-moment one-head/edge-mass comparison gives the
actual low-density profile bound once its remaining restricted-family
optimization is supplied. -/
theorem normalizedValue_le_benchmark_of_low_of_oneHead_bound
    {L : ℝ} {x : Profile} (hx : x ∈ space L)
    (hd : density x ∈ Set.Icc (1 / 4 : ℝ) (3 / 8))
    (hone : oneHeadValue x.1 (∑' i, (x.2 i) ^ 2) / (1 + x.1) ^ 2 ≤ benchmark (density x)) :
    normalizedValue x ≤ benchmark (density x) := by
  have hM : 0 < (1 + x.1) ^ 2 := by have := hx.1.1.1; positivity
  have hthird := Benchmark.benchmark_ge_third_of_low hd
  conv_lhs at hthird => rw [density_eq_normalized_edge_mass hx]
  have hthird' : ((x.1 + (x.1 ^ 2 - ∑' i, (x.2 i) ^ 2) / 2) / 3) / (1 + x.1) ^ 2 ≤
      benchmark (density x) := by
    convert hthird using 1
    ring
  apply (div_le_iff₀ hM).mpr
  exact (limitValue_le_max_oneHead hx).trans (max_le ((div_le_iff₀ hM).mp hone)
    ((div_le_iff₀ hM).mp hthird'))

/-- All actual normalized multipartite profile densities are covered by the
completed structural, collision and low-density arguments. The sole
remaining premise is the actual one-secondary-head family optimization. -/
theorem normalizedValue_le_benchmark_of_oneHead_family_bound
    (hfamily : ∀ L x, x ∈ space L → density x ∈ Set.Icc (1 / 4 : ℝ) (1 / 2) →
      oneHeadValue x.1 (∑' i, (x.2 i) ^ 2) / (1 + x.1) ^ 2 ≤ benchmark (density x))
    {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    normalizedValue x ≤ benchmark (density x) := by
  have hhalf : density x ≤ 1 / 2 := (density_mem_Icc hx).2
  by_cases hquarter : density x ≤ 1 / 4
  · exact normalizedValue_le_benchmark_of_le_quarter hx hquarter
  have hquarter' : 1 / 4 ≤ density x := (lt_of_not_ge hquarter).le
  by_cases hlow : density x ≤ 3 / 8
  · exact normalizedValue_le_benchmark_of_low_of_oneHead_bound hx ⟨hquarter', hlow⟩
      (hfamily L x hx ⟨hquarter', hhalf⟩)
  by_cases hdense : 153 / 338 ≤ density x
  · exact normalizedValue_le_benchmark_of_dense hx hdense
  apply normalizedValue_le_benchmark_on_comparison_window ?_ ?_ ?_ hx
    ⟨(lt_of_not_ge hlow).le, (lt_of_not_ge hdense).le⟩
  · intro R y hy hdy
    apply normalizedValue_le_benchmark_of_low_of_oneHead_bound hy
      (by rw [hdy]; norm_num)
    exact hfamily R y hy ⟨by rw [hdy]; norm_num, (density_mem_Icc hy).2⟩
  · intro R y hy hdy
    exact normalizedValue_le_benchmark_of_dense hy (by rw [hdy])
  · intro y hy hzero
    have hone := hfamily comparisonCutoff y hy.1
      ⟨by linarith [hy.2.1], (density_mem_Icc hy.1).2⟩
    change limitValue y / (1 + y.1) ^ 2 ≤ benchmark (density y)
    rw [limitValue_eq_oneHeadValue_of_second_zero hy.1 hzero]
    exact hone

end Erdos1017.MultipartiteProfiles
