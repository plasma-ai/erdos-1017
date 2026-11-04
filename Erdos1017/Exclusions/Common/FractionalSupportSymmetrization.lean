module

public import Erdos1017.Exclusions.Common.FiniteSupportCloning
public import Erdos1017.Exclusions.Common.MultipartiteSupportBound

/-!
# Slope-one support bound for all finite graphs

Among graphs of the same order, a maximizer of value plus edge count with the
fewest neighborhood rows is complete multipartite, so every finite graph,
including the empty one, satisfies the sharp slope-one support bound
(`value_add_edge_count_le_all`).
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.FractionalGraph

variable {n : ℕ}

/-- Among actual graphs of the same order, an attained maximum of value
plus edge count with the fewest neighborhood rows is complete multipartite. -/
theorem exists_completeMultipartite_support_ge (G : SimpleGraph (Fin n)) :
    ∃ H : SimpleGraph (Fin n), H.IsCompleteMultipartite ∧
      value G + (G.edgeSet.ncard : ℝ) ≤ value H + (H.edgeSet.ncard : ℝ) := by
  classical
  let F := fun H : SimpleGraph (Fin n) => value H + (H.edgeSet.ncard : ℝ)
  obtain ⟨H, _, hmax⟩ := Finset.univ.exists_max_image F
    (Finset.univ_nonempty_iff.mpr ⟨G⟩)
  let M := Finset.univ.filter fun K : SimpleGraph (Fin n) => F K = F H
  have hHM : H ∈ M := by simp [M]
  obtain ⟨K, hKM, hmin⟩ := M.exists_min_image neighborhoodRowCount ⟨H, hHM⟩
  have hKeq : F K = F H := (Finset.mem_filter.mp hKM).2
  refine ⟨K, ?_, ?_⟩
  · by_contra hnot
    obtain ⟨y, hy, _, hopt⟩ := exists_bounded_dual K
    obtain ⟨L, hKL, hrows⟩ := exists_support_clone K y hy hopt hnot
    have hLeq : F L = F H := le_antisymm (hmax L (Finset.mem_univ _))
      (hKeq ▸ hKL)
    have hLM : L ∈ M := by
      simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hLeq
    exact (not_lt_of_ge (hmin L hLM)) hrows
  · change F G ≤ F K
    rw [hKeq]
    exact hmax G (Finset.mem_univ _)

/-- Every actual finite graph satisfies the sharp unrestricted slope-one
support bound, including the graph on no vertices. -/
theorem value_add_edge_count_le_all (G : SimpleGraph (Fin n)) :
    value G + (G.edgeSet.ncard : ℝ) ≤ 25 * (n : ℝ) ^ 2 / 48 := by
  by_cases hn : 0 < n
  · obtain ⟨H, hH, hGH⟩ := exists_completeMultipartite_support_ge G
    exact hGH.trans (FractionalMultipartite.value_add_edge_count_le H hn hH)
  · have hn0 : n = 0 := by omega
    subst n
    obtain ⟨y, _, _, hopt⟩ := exists_bounded_dual G
    have hvalue : value G = 0 := by simpa [WeightedGraph.objective] using hopt.symm
    have hcount := ordered_edge_count G
    have hedge : G.edgeSet.ncard = 0 := by simpa using hcount.symm
    simp only [hvalue, hedge, Nat.cast_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, zero_div, le_refl]

end Erdos1017.FractionalGraph
