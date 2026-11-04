module

public import Erdos1017.FractionalLimit.FractionalGraphDelete
public import Erdos1017.LowerBound.WeightedGraphDual

/-!
# Entry bounds for optimal fractional duals

Erasing an edge coefficient (`eraseEdge`) from a dual gives a feasible dual for
the graph without that edge and subtracts its single charge from the objective,
so every entry of an attained optimal finite dual lies in `[-3,1]`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.WeightedGraph

variable {n : ℕ}

def isSelectedEdge (u v i j : Fin n) : Prop :=
  (i = u ∧ j = v) ∨ (i = v ∧ j = u)

/-- Remove a symmetric edge coefficient from a dual matrix. -/
def eraseEdge (y : Fin n → Fin n → ℝ) (u v : Fin n) :
    Fin n → Fin n → ℝ := by
  classical
  exact fun i j => if isSelectedEdge u v i j then 0 else y i j

private theorem isSelectedEdge_swap (u v i j : Fin n) :
    isSelectedEdge u v i j ↔ isSelectedEdge u v j i := by
  simp only [isSelectedEdge]
  tauto

/-- Erasing an existing edge gives a feasible dual for the graph with that
edge deleted. -/
theorem dualFeasible_eraseEdge (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : DualFeasible G y) (u v : Fin n)
    (huv : G.Adj u v) :
    DualFeasible (G.deleteEdges {s(u, v)}) (eraseEdge y u v) := by
  classical
  have hnot_selected {i j : Fin n} (h : ¬isSelectedEdge u v i j)
      (hij : G.Adj i j) : (G.deleteEdges {s(u, v)}).Adj i j := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hij, ?_⟩
    intro heq
    exact h (by simpa [isSelectedEdge, Sym2.eq_iff] using heq)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    by_cases h : isSelectedEdge u v i j
    · have h' := (isSelectedEdge_swap u v i j).mp h
      simp [eraseEdge, h, h']
    · have h' := (isSelectedEdge_swap u v i j).mpr.mt h
      simp [eraseEdge, h, h', hy.1 i j]
  · intro i j hij
    by_cases h : isSelectedEdge u v i j
    · simp [eraseEdge, h]
    · have hG : ¬G.Adj i j := fun hadj => hij (hnot_selected h hadj)
      simp [eraseEdge, h, hy.2.1 i j hG]
  · intro S hS
    have hG : G.IsClique (S : Set (Fin n)) := by
      intro i hi j hj hij
      exact (SimpleGraph.deleteEdges_adj.mp (hS hi hj hij)).1
    have hno : ¬(u ∈ S ∧ v ∈ S) := by
      intro h
      have hadj := hS h.1 h.2 huv.ne
      exact (SimpleGraph.deleteEdges_adj.mp hadj).2 (Set.mem_singleton_iff.mpr rfl)
    have hsame : ∀ i ∈ S, ∀ j ∈ S, eraseEdge y u v i j = y i j := by
      intro i hi j hj
      have h : ¬isSelectedEdge u v i j := by
        intro h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hno ⟨hi, hj⟩
        · exact hno ⟨hj, hi⟩
      simp [eraseEdge, h]
    calc
      charge (eraseEdge y u v) S = charge y S := by
        rw [charge_eq_sum, charge_eq_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hsame i hi j hj
      _ ≤ 1 := hy.2.2 S hG

/-- Erasing an undirected edge subtracts its single charge from the
half-ordered-pair dual objective. -/
theorem objective_eraseEdge (y : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, y i j = y j i) (u v : Fin n) (huv : u ≠ v) :
    objective (fun _ => 1) (eraseEdge y u v) =
      objective (fun _ => 1) y - y u v := by
  classical
  have hterm (i j : Fin n) : eraseEdge y u v i j =
      y i j - (if i = u ∧ j = v then y u v else 0) -
        (if i = v ∧ j = u then y v u else 0) := by
    by_cases h₁ : i = u ∧ j = v
    · obtain ⟨rfl, rfl⟩ := h₁
      simp [eraseEdge, isSelectedEdge, huv, huv.symm]
    · by_cases h₂ : i = v ∧ j = u
      · obtain ⟨rfl, rfl⟩ := h₂
        simp [eraseEdge, isSelectedEdge, huv, huv.symm]
      · simp [eraseEdge, isSelectedEdge, h₁, h₂]
  have hmask₁ : (∑ i : Fin n, ∑ j : Fin n,
      if i = u ∧ j = v then y u v else 0) = y u v := by
    simp [ite_and]
  have hmask₂ : (∑ i : Fin n, ∑ j : Fin n,
      if i = v ∧ j = u then y v u else 0) = y v u := by
    simp [ite_and]
  simp only [objective, mul_one, hterm, Finset.sum_sub_distrib]
  rw [hmask₁, hmask₂, hsymm v u]
  ring

/-- A two-vertex clique bounds every present edge charge by one. -/
private theorem dualFeasible_entry_le_one (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : DualFeasible G y) (i j : Fin n) :
    y i j ≤ 1 := by
  by_cases hij : G.Adj i j
  · have hclique : G.IsClique (({i, j} : Finset (Fin n)) : Set (Fin n)) := by
      simpa using (SimpleGraph.isClique_pair).mpr (fun _ => hij)
    have h := hy.2.2 {i, j} hclique
    have hdiagᵢ : y i i = 0 := hy.2.1 i i (fun h => G.irrefl h)
    have hdiagⱼ : y j j = 0 := hy.2.1 j j (fun h => G.irrefl h)
    have hcharge : charge y {i, j} = y i j := by
      rw [charge_eq_sum]
      simp [Finset.sum_pair hij.ne, hdiagᵢ, hdiagⱼ, hy.1 j i]
    rwa [hcharge] at h
  · rw [hy.2.1 i j hij]
    norm_num

/-- Every entry of an attained optimal finite dual already lies in the
physical interval `[-3,1]`. The lower bound follows by erasing one edge and
using the actual cost-four fractional deletion theorem. -/
theorem optimal_dual_mem_Icc (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : DualFeasible G y)
    (hopt : objective (fun _ => 1) y = FractionalGraph.value G) (i j : Fin n) :
    y i j ∈ Set.Icc (-3 : ℝ) 1 := by
  constructor
  · by_cases hij : G.Adj i j
    · have hnew := dualFeasible_eraseEdge G y hy i j hij
      have hweak := dual_objective_le_value (G.deleteEdges {s(i, j)})
        (eraseEdge y i j) hnew
      have hdelete := FractionalGraph.value_delete_edge_le G i j hij
      rw [objective_eraseEdge y hy.1 i j hij.ne, hopt] at hweak
      linarith
    · rw [hy.2.1 i j hij]
      norm_num
  · exact dualFeasible_entry_le_one G y hy i j

end Erdos1017.WeightedGraph
