module

public import Erdos1017.LowerBound.WeightedGraphRealization

/-!
# Passing finite weighted duals to the graph limit

Integer multiplicities approximate every nonnegative probability vector, and
with continuity of objective and density this shows that every feasible signed
dual of a finite weighted base is bounded by the graph limit
(`objective_le_densityLimit`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

open scoped BigOperators Topology
open Filter FractionalGraph

variable {r : ℕ}

theorem continuous_objective (y : Fin r → Fin r → ℝ) : Continuous (fun w => objective w y) := by
  unfold objective
  fun_prop

theorem continuous_density (G : SimpleGraph (Fin r)) : Continuous (density G) :=
  continuous_objective (adjacencyMatrix G)

/-- Integer multiplicities approximate every nonnegative probability vector. -/
def approximation (w : Fin r → ℝ) (q : ℕ) (i : Fin r) : ℕ := ⌊w i * (q : ℝ) ^ 2⌋₊

def approximationWeights (w : Fin r → ℝ) (q : ℕ) (i : Fin r) : ℝ :=
  (approximation w q i : ℝ) / ((∑ j, approximation w q j : ℕ) : ℝ)

theorem tendsto_approximation_total (w : Fin r → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    Tendsto (fun q : ℕ => ((∑ i, approximation w q i : ℕ) : ℝ) / (q : ℝ) ^ 2)
      atTop (𝓝 1) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ => tendsto_floor_density (w i) (hw i))
  simpa only [← Finset.sum_div, ← Nat.cast_sum, hsum, approximation] using h

theorem approximation_total_eventually_pos (w : Fin r → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) : ∀ᶠ q : ℕ in atTop, 0 < ∑ i, approximation w q i := by
  filter_upwards [(tendsto_approximation_total w hw hsum).eventually
    (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with q hq
  by_contra h
  have hz : (∑ i, approximation w q i) = 0 := by omega
  simp [hz] at hq

theorem tendsto_approximationWeights (w : Fin r → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) : Tendsto (approximationWeights w) atTop (𝓝 w) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have h := (tendsto_floor_density (w i) (hw i)).div
    (tendsto_approximation_total w hw hsum) (by norm_num : (1 : ℝ) ≠ 0)
  apply Tendsto.congr' (show _ =ᶠ[atTop] _ from ?_) (by simpa only [div_one] using h)
  filter_upwards [eventually_gt_atTop 0] with q hq
  have hq' : (q : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt hq))
  exact div_div_div_cancel_right₀ hq' _ _

/-- Every feasible signed dual of every finite weighted base is bounded by the actual graph limit. -/
theorem objective_le_densityLimit (G : SimpleGraph (Fin r)) (w : Fin r → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (y : Fin r → Fin r → ℝ) (hy : DualFeasible G y) :
    objective w y ≤ densityLimit (density G w) := by
  have hweights := tendsto_approximationWeights w hw hsum
  have hobj := (continuous_objective y).continuousAt.tendsto.comp hweights
  have hden := (continuous_density G).continuousAt.tendsto.comp hweights
  have hF := densityLimit_continuous.continuousAt.tendsto.comp hden
  apply le_of_tendsto_of_tendsto hobj hF
  filter_upwards [approximation_total_eventually_pos w hw hsum] with q hq
  exact realization_objective_le_densityLimit G (approximation w q) hq y hy

end Erdos1017.WeightedGraph
