module

public import Erdos1017.IntegerTransfer.SameGraphIntegerTransfer
public import Erdos1017.LowerBound.IntegerBenchmarkLower
public import Erdos1017.Target

/-!
# Integer transfer and the uniform asymptotic formula

The same-graph transfer bounds the integer extremum by the fractional extremum
up to `ε n²`, uniformly in the edge count
(`exists_integer_extremal_upper_transfer`), and `finalUniformAsymptotic` derives
`UniformAsymptotic` from the fractional upper bound
`densityLimit d ≤ benchmark d` on `[0, 1/2]`. It is used in
`FullBenchmarkUpper`.
-/

@[expose] public section

noncomputable section

namespace Erdos1017

open FractionalGraph

/-- The actual same-graph transfer bounds the original integer extremum by the
fractional extremum uniformly in the prescribed edge count. -/
theorem exists_integer_extremal_upper_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ,
      (f n k : ℝ) ≤ extremal n k + ε * (n : ℝ) ^ 2 := by
  obtain ⟨n₀, hn₀, htransfer⟩ := exists_same_graph_integer_upper_transfer ε hε
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn k
  let B := extremal n k + ε * (n : ℝ) ^ 2
  have hB : 0 ≤ B := add_nonneg (extremal_nonneg n k) (mul_nonneg hε.le (sq_nonneg _))
  have hfloor : f n k ≤ ⌊B⌋₊ := by
    apply (f_le_iff_cliquePartitionNumber n k ⌊B⌋₊).mpr
    intro G hG
    apply Nat.le_floor
    have hvalue : value G ≤ extremal n k := by simpa only [hG] using value_le_extremal G
    dsimp only [B]
    linarith only [htransfer n hn G, hvalue]
  exact (show (f n k : ℝ) ≤ (⌊B⌋₊ : ℝ) by exact_mod_cast hfloor).trans (Nat.floor_le hB)

/-- The original uniform target follows from the sharp scalar fractional
upper comparison. The same-graph integer transfer and lower inequality used
here are unconditional; only the displayed scalar comparison is assumed. -/
theorem finalUniformAsymptotic
    (hupper : ∀ d : ℝ, d ∈ Set.Icc (0 : ℝ) (1 / 2) → densityLimit d ≤ benchmark d) :
    UniformAsymptotic := by
  intro ε hε
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨N₁, hN₁, htransfer⟩ := exists_integer_extremal_upper_transfer (ε / 3) hthird
  obtain ⟨N₂, hfrac⟩ := extremal_uniform_convergence (ε / 3) hthird
  obtain ⟨N₃, hlower⟩ := benchmark_uniform_integer_lower ε hε
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro n hn k hk
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₃ : N₃ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : 0 < n := hN₁.trans_le hn₁
  have hden : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hnpos)
  have hnorm := div_le_div_of_nonneg_right (htransfer n hn₁ k) hden.le
  simp only [add_div, mul_div_cancel_right₀ _ hden.ne'] at hnorm
  have hlimit := (abs_lt.mp (hfrac n hn₂ k hk)).2
  have hsharp := hupper _ (normalized_edge_count_mem_density_interval n k hk)
  have hlow := hlower n hn₃ k hk
  apply abs_lt.mpr
  constructor <;> linarith only [hnorm, hlimit, hsharp, hlow, hε]

end Erdos1017
