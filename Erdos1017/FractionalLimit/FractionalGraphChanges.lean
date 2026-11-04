module

public import Erdos1017.FractionalLimit.FractionalGraphDelete

/-!
# Fractional value under finite edge edits

This module iterates the one-edge deletion and insertion bounds over finite edge
sets, so that the fractional value changes by at most three units per changed
unordered edge (`abs_value_sub_le_edit_distance`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

variable {n : ℕ}

theorem value_add_edge_le_any (G : SimpleGraph (Fin n)) (u v : Fin n) :
    value (G ⊔ SimpleGraph.edge u v) ≤ value G + 1 := by
  by_cases huv : u = v
  · subst v
    simp
  · by_cases hadj : G.Adj u v
    · have hle : SimpleGraph.edge u v ≤ G := by
        intro a b hab
        obtain ⟨h | h, _⟩ := (SimpleGraph.edge_adj u v a b).mp hab
        · rcases h with ⟨rfl, rfl⟩
          exact hadj
        · rcases h with ⟨rfl, rfl⟩
          exact hadj.symm
      rw [sup_eq_left.mpr hle]
      linarith
    · exact value_add_edge_le G u v huv hadj

theorem delete_edge_eq_self_of_nonadjacent (G : SimpleGraph (Fin n)) (u v : Fin n)
    (hno : ¬G.Adj u v) : G.deleteEdges {s(u, v)} = G := by
  apply SimpleGraph.edgeSet_injective
  rw [SimpleGraph.edgeSet_deleteEdges]
  ext e
  constructor
  · intro he
    exact he.1
  · intro he
    refine ⟨he, ?_⟩
    intro heq
    have heq' : e = s(u, v) := Set.mem_singleton_iff.mp heq
    subst e
    exact hno ((SimpleGraph.mem_edgeSet G).mp he)

theorem value_delete_edge_le_any (G : SimpleGraph (Fin n)) (u v : Fin n) :
    value (G.deleteEdges {s(u, v)}) ≤ value G + 3 := by
  by_cases hadj : G.Adj u v
  · exact value_delete_edge_le G u v hadj
  · rw [delete_edge_eq_self_of_nonadjacent G u v hadj]
    linarith

/-- The one-edge construction iterates over any finite set of removed edges. -/
theorem value_delete_edges_le (G : SimpleGraph (Fin n)) (s : Finset (Sym2 (Fin n))) :
    value (G.deleteEdges s) ≤ value G + 3 * (s.card : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    have heq : G.deleteEdges (↑(insert e s) : Set (Sym2 (Fin n))) =
        (G.deleteEdges s).deleteEdges {e} := by
      rw [SimpleGraph.deleteEdges_deleteEdges]
      congr 1
      ext z
      simp
    rw [heq, Finset.card_insert_of_notMem he, Nat.cast_add, Nat.cast_one]
    induction e using Sym2.ind with
    | h u v =>
      have hstep := value_delete_edge_le_any (G.deleteEdges s) u v
      linarith

/-- The unit-edge addition construction iterates over every finite insertion set. -/
theorem value_add_edges_le (G : SimpleGraph (Fin n)) (s : Finset (Sym2 (Fin n))) :
    value (G ⊔ SimpleGraph.fromEdgeSet s) ≤ value G + (s.card : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    have heq : G ⊔ SimpleGraph.fromEdgeSet (↑(insert e s) : Set (Sym2 (Fin n))) =
        (G ⊔ SimpleGraph.fromEdgeSet s) ⊔ SimpleGraph.fromEdgeSet {e} := by
      rw [Finset.coe_insert, Set.insert_eq, SimpleGraph.fromEdgeSet_union]
      ac_rfl
    rw [heq, Finset.card_insert_of_notMem he, Nat.cast_add, Nat.cast_one]
    induction e using Sym2.ind with
    | h u v =>
      have hstep := value_add_edge_le_any (G ⊔ SimpleGraph.fromEdgeSet s) u v
      change value ((G ⊔ SimpleGraph.fromEdgeSet s) ⊔ SimpleGraph.edge u v) ≤ _
      linarith

def finiteEdges (G : SimpleGraph (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact G.edgeFinset

@[simp] theorem mem_finiteEdges (G : SimpleGraph (Fin n)) (u v : Fin n) :
    s(u, v) ∈ finiteEdges G ↔ G.Adj u v := by
  classical
  exact SimpleGraph.mem_edgeFinset

/-- Delete the unwanted edges, then add the missing edges. -/
theorem value_le_edit_cost (G H : SimpleGraph (Fin n)) :
    value H ≤ value G + 3 * ((finiteEdges G \ finiteEdges H).card : ℝ) +
      ((finiteEdges H \ finiteEdges G).card : ℝ) := by
  classical
  let removed := finiteEdges G \ finiteEdges H
  let added := finiteEdges H \ finiteEdges G
  have hgraph : G.deleteEdges removed ⊔ SimpleGraph.fromEdgeSet added = H := by
    ext u v
    simp only [SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
      SimpleGraph.fromEdgeSet_adj, Finset.mem_coe, Finset.mem_sdiff,
      mem_finiteEdges, removed, added]
    constructor
    · rintro (⟨huv, hnot⟩ | ⟨⟨huv, _⟩, _⟩)
      · by_contra hno
        exact hnot ⟨huv, hno⟩
      · exact huv
    · intro huv
      by_cases hG : G.Adj u v
      · exact Or.inl ⟨hG, fun h => h.2 huv⟩
      · exact Or.inr ⟨⟨huv, hG⟩, huv.ne⟩
  have hdel := value_delete_edges_le G removed
  have hadd := value_add_edges_le (G.deleteEdges removed) added
  rw [hgraph] at hadd
  linarith

/-- Each changed unordered edge costs at most three units of fractional partition mass. -/
theorem abs_value_sub_le_edit_distance (G H : SimpleGraph (Fin n)) :
    |value G - value H| ≤ 3 *
      (((finiteEdges G \ finiteEdges H).card : ℝ) +
        ((finiteEdges H \ finiteEdges G).card : ℝ)) := by
  have hGH := value_le_edit_cost G H
  have hHG := value_le_edit_cost H G
  have h₁ : 0 ≤ ((finiteEdges G \ finiteEdges H).card : ℝ) := Nat.cast_nonneg _
  have h₂ : 0 ≤ ((finiteEdges H \ finiteEdges G).card : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

end Erdos1017.FractionalGraph
