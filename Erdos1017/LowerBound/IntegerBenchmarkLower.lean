module

public import Erdos1017.LowerBound.WeightedGraphBenchmarkLower

/-!
# Benchmark lower bound for the integer problem

The fractional maximum is bounded by the integer extremal function, so the
integer problem satisfies the benchmark lower bound uniformly in its edge count
(`benchmark_uniform_integer_lower`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017

open scoped Topology
open Filter
open FractionalGraph

/-- The fractional maximum is bounded by the original integer extremal function. -/
theorem fractional_extremal_le_f (n k : ℕ) (hk : k ≤ n.choose 2) :
    extremal n k ≤ (f n k : ℝ) := by
  obtain ⟨G, hG, hvG⟩ := extremal_attained n k hk
  have hcp : cliquePartitionNumber G ≤ f n k :=
    (f_le_iff_cliquePartitionNumber n k (f n k)).mp le_rfl G hG
  rw [← hvG]
  exact (value_le_cliquePartitionNumber G).trans (by exact_mod_cast hcp)

theorem normalized_edge_count_mem_density_interval (n k : ℕ) (hk : k ≤ n.choose 2) :
    (k : ℝ) / (n : ℝ) ^ 2 ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  refine ⟨div_nonneg (Nat.cast_nonneg _) (sq_nonneg _), ?_⟩
  by_cases hn : n = 0
  · simp [hn]
  · have hden : 0 < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast (Nat.pos_of_ne_zero hn)) _
    have hcard : (k : ℝ) ≤ (n.choose 2 : ℝ) := by exact_mod_cast hk
    have hbound : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
      simpa using (Nat.choose_le_pow_div 2 n : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / (2 : ℕ).factorial)
    rw [div_le_iff₀ hden]
    linarith

/-- The original integer problem satisfies the benchmark lower bound uniformly in its edge count. -/
theorem benchmark_uniform_integer_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, k ≤ n.choose 2 →
      benchmark ((k : ℝ) / (n : ℝ) ^ 2) - ε < (f n k : ℝ) / (n : ℝ) ^ 2 := by
  obtain ⟨N, hN⟩ := extremal_uniform_convergence ε hε
  refine ⟨N, ?_⟩
  intro n hn k hk
  have herr := (abs_lt.mp (hN n hn k hk)).1
  have hbench := WeightedGraph.benchmark_le_densityLimit _
    (normalized_edge_count_mem_density_interval n k hk)
  have hfrac := div_le_div_of_nonneg_right (fractional_extremal_le_f n k hk) (sq_nonneg (n : ℝ))
  linarith

end Erdos1017
