module

public import Erdos1017.LowerBound.WeightedGraphDual
public import Erdos1017.LowerBound.FractionalLimitEndpoints

/-!
# Finite insertion repair for nearly complete graphs

The fractional partition repair bounds a feasible signed dual on a nearly
complete graph by one plus three per missing unordered edge, and filling every
missing pair at charge `-3` restores the full clique inequality.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

variable {n : ℕ}

/-- The actual fractional partition repair bounds a feasible signed dual on
a nearly complete graph by one plus three per missing unordered edge. -/
theorem dual_charge_le_one_add_three_missing (G : SimpleGraph (Fin n)) (hn : 2 ≤ n)
    (y : Fin n → Fin n → ℝ) (hy : DualFeasible G y) :
    objective (fun _ => 1) y ≤ 1 + 3 *
      ((FractionalGraph.finiteEdges (⊤ : SimpleGraph (Fin n)) \
        FractionalGraph.finiteEdges G).card : ℝ) := by
  have hsub := FractionalGraph.finiteEdges_mono (show G ≤ ⊤ from le_top)
  have h := FractionalGraph.value_le_edit_cost (⊤ : SimpleGraph (Fin n)) G
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub] at h
  simp only [Finset.card_empty, Nat.cast_zero, add_zero] at h
  linarith [dual_objective_le_value G y hy, FractionalGraph.value_top_le_one n hn]

/-- Filling every missing pair at charge `-3` restores the full clique
inequality. This is the finite numerical insertion repair. -/
theorem dual_charge_minus_three_missing_le_one (G : SimpleGraph (Fin n)) (hn : 2 ≤ n)
    (y : Fin n → Fin n → ℝ) (hy : DualFeasible G y) :
    objective (fun _ => 1) y - 3 *
      ((FractionalGraph.finiteEdges (⊤ : SimpleGraph (Fin n)) \
        FractionalGraph.finiteEdges G).card : ℝ) ≤ 1 := by
  linarith [dual_charge_le_one_add_three_missing G hn y hy]

end Erdos1017.WeightedGraph
