module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.CastCard
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Edge loss from removing vertices

Removing a set of vertices loses at most their number times the ambient vertex
count in edges, and the remaining graph is the mapped induced graph
(`induced_edge_loss`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.GraphEmbedding

open Finset

variable {A V : Type*} [Fintype A] [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- Mapping an induced graph back retains exactly those edges whose endpoints
belong to the embedded vertex set. -/
theorem map_comap_adj_iff (G : SimpleGraph V) (e : A ↪ V) (x y : V) :
    ((G.comap e).map e).Adj x y ↔ G.Adj x y ∧ x ∈ univ.map e ∧ y ∈ univ.map e := by
  classical
  constructor
  · rintro ⟨_, a, b, hab, rfl, rfl⟩
    exact ⟨hab, mem_map.mpr ⟨a, mem_univ _, rfl⟩, mem_map.mpr ⟨b, mem_univ _, rfl⟩⟩
  · rintro ⟨hxy, hx, hy⟩
    obtain ⟨a, _, rfl⟩ := mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := mem_map.mp hy
    exact ⟨hxy.ne, a, b, hxy, rfl, rfl⟩

/-- Removing vertices loses at most their number times the ambient vertex count
in edges. The remaining graph is the actual mapped induced graph. -/
theorem induced_edge_loss (G : SimpleGraph V) [DecidableRel G.Adj] (e : A ↪ V) :
    (G.edgeFinset.card : ℝ) - ((G.comap e).map e).edgeFinset.card ≤
      ((univ \ univ.map e).card : ℝ) * Fintype.card V := by
  classical
  let H := (G.comap e).map e
  let D := univ \ univ.map e
  have hsub : H ≤ G := SimpleGraph.map_comap_le e G
  have hmissing : (univ ×ˢ univ).filter (fun (x, y) => G.Adj x y ∧ ¬H.Adj x y) ⊆
      D ×ˢ univ ∪ univ ×ˢ D := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨_, hxy, hnot⟩ := mem_filter.mp hxy
    by_cases hx : x ∈ univ.map e
    · have hy : y ∉ univ.map e := fun hy => hnot ((map_comap_adj_iff G e x y).mpr ⟨hxy, hx, hy⟩)
      exact mem_union.mpr (Or.inr (mem_product.mpr
        ⟨mem_univ _, mem_sdiff.mpr ⟨mem_univ _, hy⟩⟩))
    · exact mem_union.mpr (Or.inl (mem_product.mpr
        ⟨mem_sdiff.mpr ⟨mem_univ _, hx⟩, mem_univ _⟩))
  have hcount :
      2 * ((G.edgeFinset.card : ℝ) - H.edgeFinset.card) ≤
        2 * (D.card : ℝ) * Fintype.card V := by
    calc
      _ = (((univ ×ˢ univ).filter fun (x, y) => G.Adj x y ∧ ¬H.Adj x y).card : ℝ) := by
        rw [univ_product_univ, mul_sub, filter_and_not, cast_card_sdiff]
        · norm_cast
          rw [SimpleGraph.two_mul_card_edgeFinset, SimpleGraph.two_mul_card_edgeFinset]
        · gcongr with xy _
          exact fun hxy => hsub hxy
      _ ≤ (D ×ˢ univ ∪ univ ×ˢ D).card := by exact_mod_cast card_le_card hmissing
      _ ≤ ((D ×ˢ univ).card : ℝ) + (univ ×ˢ D).card := by
        exact_mod_cast card_union_le (D ×ˢ univ) (univ ×ˢ D)
      _ = _ := by simp only [card_product, card_univ, Nat.cast_mul]; ring
  change (G.edgeFinset.card : ℝ) - H.edgeFinset.card ≤ (D.card : ℝ) * Fintype.card V
  linarith

end Erdos1017.GraphEmbedding
