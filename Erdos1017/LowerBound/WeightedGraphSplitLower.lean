module

public import Erdos1017.LowerBound.WeightedGraphSplitDual
public import Erdos1017.Benchmark

/-!
# Split lower bound in the limit

With equal tail weights, the split lower bound is realized by finite heads and
increasingly fine independent tail parts (`split_limit_lower`), so the split
value and split curve lie below the density limit.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

open scoped BigOperators Topology
open Filter FractionalGraph

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteDensity_top (w : ι → ℝ) :
    finiteDensity (⊤ : SimpleGraph ι) w = ((∑ i, w i) ^ 2 - ∑ i, w i ^ 2) / 2 := by
  classical
  unfold finiteDensity finiteObjective
  simp only [SimpleGraph.top_adj, ite_not, ite_mul, zero_mul, one_mul]
  rw [offDiagonal_sum]

def equalTailWeights (a u : ℝ) (N : ℕ) : Option (Fin (N + 1)) → ℝ
  | none => a
  | some _ => u / ((N + 1 : ℕ) : ℝ)

theorem equalTailWeights_tail_sum (a u : ℝ) (N : ℕ) :
    (∑ i, equalTailWeights a u N (some i)) = u := by
  simp only [equalTailWeights, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem equalTailWeights_tail_square_sum (a u : ℝ) (N : ℕ) :
    (∑ i, equalTailWeights a u N (some i) ^ 2) = u ^ 2 / ((N + 1 : ℕ) : ℝ) := by
  simp only [equalTailWeights, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem split_equal_tail_lower (j : ℕ) (hj : 0 < j) (a u : ℝ)
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hsum : a + u = 1) (N : ℕ) :
    2 / ((j : ℝ) + 1) * a * u + (-2 / ((j : ℝ) * ((j : ℝ) + 1))) *
      (u ^ 2 - u ^ 2 / ((N + 1 : ℕ) : ℝ)) / 2 ≤
      densityLimit ((1 - a ^ 2 - u ^ 2 / ((N + 1 : ℕ) : ℝ)) / 2) := by
  have hw (i : Option (Fin (N + 1))) : 0 ≤ equalTailWeights a u N i := by
    cases i
    · exact ha
    · exact div_nonneg hu (Nat.cast_nonneg _)
  have htotal : (∑ i, equalTailWeights a u N i) = 1 := by
    rw [Fintype.sum_option, equalTailWeights_tail_sum]
    exact hsum
  have h := split_finite_lower j hj (equalTailWeights a u N) hw htotal
  rw [equalTailWeights_tail_sum, equalTailWeights_tail_square_sum, finiteDensity_top,
    htotal, Fintype.sum_option, equalTailWeights_tail_square_sum] at h
  simpa only [equalTailWeights, one_pow, sub_add_eq_sub_sub] using h

/-- The split lower bound is realized by finite heads and increasingly fine independent tail parts. -/
theorem split_limit_lower (j : ℕ) (hj : 0 < j) (a u : ℝ)
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hsum : a + u = 1) :
    2 / ((j : ℝ) + 1) * a * u + (-2 / ((j : ℝ) * ((j : ℝ) + 1))) * u ^ 2 / 2 ≤
      densityLimit ((1 - a ^ 2) / 2) := by
  have hvanish : Tendsto (fun N : ℕ => u ^ 2 / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (u ^ 2)
  have hconst : Tendsto (fun _ : ℕ => u ^ 2) atTop (𝓝 (u ^ 2)) := tendsto_const_nhds
  have hleft := (((hconst.sub hvanish).const_mul (-2 / ((j : ℝ) * ((j : ℝ) + 1)))).div_const 2).const_add
    (2 / ((j : ℝ) + 1) * a * u)
  have hc : Tendsto (fun _ : ℕ => 1 - a ^ 2) atTop (𝓝 (1 - a ^ 2)) := tendsto_const_nhds
  have hright := densityLimit_continuous.continuousAt.tendsto.comp ((hc.sub hvanish).div_const 2)
  simpa only [sub_zero] using le_of_tendsto_of_tendsto' hleft hright
    (fun N => split_equal_tail_lower j hj a u ha hu hsum N)

theorem splitValue_le_densityLimit (a : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1) :
    Benchmark.splitValue a ≤ densityLimit ((1 - a ^ 2) / 2) := by
  have hj : 0 < Benchmark.splitIndex a := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  have h := split_limit_lower (Benchmark.splitIndex a) hj a (1 - a) ha.le
    (sub_nonneg.mpr ha₁) (by ring)
  have hj' : (0 : ℝ) < Benchmark.splitIndex a := by exact_mod_cast hj
  have heq : Benchmark.splitValue a =
      2 / ((Benchmark.splitIndex a : ℝ) + 1) * a * (1 - a) +
        (-2 / ((Benchmark.splitIndex a : ℝ) * ((Benchmark.splitIndex a : ℝ) + 1))) *
          (1 - a) ^ 2 / 2 := by
    simp only [Benchmark.splitValue, ite_eq_right ha.ne']
    field_simp
    ring
  rwa [heq]

theorem split_curve_le_densityLimit (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Benchmark.splitValue (Real.sqrt (2 * ε)) ≤ densityLimit (1 / 2 - ε) := by
  by_cases hz : ε = 0
  · subst ε
    simpa [Benchmark.splitValue] using densityLimit_nonneg (1 / 2)
  · have hpos : 0 < ε := lt_of_le_of_ne hε.1 (Ne.symm hz)
    have ha : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.mpr (by positivity)
    have hsquare := Real.sq_sqrt (show 0 ≤ 2 * ε by positivity)
    have ha₁ : Real.sqrt (2 * ε) ≤ 1 := by nlinarith [hε.2]
    have h := splitValue_le_densityLimit (Real.sqrt (2 * ε)) ha ha₁
    have heq : (1 - Real.sqrt (2 * ε) ^ 2) / 2 = 1 / 2 - ε := by rw [hsquare]; ring
    rwa [heq] at h

end Erdos1017.WeightedGraph
