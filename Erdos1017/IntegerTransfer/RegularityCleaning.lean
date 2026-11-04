module

public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.Linarith

/-!
# Cleaning a graph along a regular partition

The cleaned graph keeps the edges of every good pair and removes all other
edges, including those within a part, so each pair is empty or regular and dense
and each part is independent; a bounded equitable regular partition with fewer
than `ε n²` deleted edges exists (`exists_cleaning`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.RegularityCleaning

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The cleaned graph retains all original edges of each good pair and removes
all edges of every other pair, including edges within a part. -/
theorem reduced_adj_iff (P : Finpartition (univ : Finset V)) (ε d : ℝ)
    {s t : Finset V} (hs : s ∈ P.parts) (ht : t ∈ P.parts)
    {x y : V} (hx : x ∈ s) (hy : y ∈ t) :
    (G.regularityReduced P ε d).Adj x y ↔
      G.Adj x y ∧ s ≠ t ∧ G.IsUniform ε s t ∧ d ≤ G.edgeDensity s t := by
  constructor
  · rintro ⟨hxy, a, ha, b, hb, hxa, hyb, hab, hreg, hden⟩
    have has := P.eq_of_mem_parts ha hs hxa hx
    have hbt := P.eq_of_mem_parts hb ht hyb hy
    subst a
    subst b
    exact ⟨hxy, hab, hreg, hden⟩
  · rintro ⟨hxy, hst, hreg, hden⟩
    exact ⟨hxy, s, hs, t, ht, hx, hy, hst, hreg, hden⟩

/-- On a retained pair, every subpair has exactly its original edge set. -/
theorem reduced_interedges (P : Finpartition (univ : Finset V)) (ε d : ℝ)
    {s t : Finset V} (hs : s ∈ P.parts) (ht : t ∈ P.parts)
    (hst : s ≠ t) (hreg : G.IsUniform ε s t) (hden : d ≤ G.edgeDensity s t)
    {a b : Finset V} (ha : a ⊆ s) (hb : b ⊆ t) :
    (G.regularityReduced P ε d).interedges a b = G.interedges a b := by
  ext ⟨x, y⟩
  simp only [SimpleGraph.mem_interedges_iff]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, SimpleGraph.regularityReduced_le hxy⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, (reduced_adj_iff G P ε d hs ht (ha hx) (hb hy)).mpr
      ⟨hxy, hst, hreg, hden⟩⟩

/-- Every pair in the actual cleaned graph is either empty or regular and dense. -/
theorem reduced_pair (P : Finpartition (univ : Finset V)) (ε d : ℝ)
    {s t : Finset V} (hs : s ∈ P.parts) (ht : t ∈ P.parts) :
    (∀ x ∈ s, ∀ y ∈ t, ¬ (G.regularityReduced P ε d).Adj x y) ∨
      ((G.regularityReduced P ε d).IsUniform ε s t ∧
        d ≤ (G.regularityReduced P ε d).edgeDensity s t) := by
  by_cases hgood : s ≠ t ∧ G.IsUniform ε s t ∧ d ≤ G.edgeDensity s t
  · have heq : ∀ a ⊆ s, ∀ b ⊆ t,
        (G.regularityReduced P ε d).edgeDensity a b = G.edgeDensity a b := by
      intro a ha b hb
      simp only [SimpleGraph.edgeDensity_def,
        reduced_interedges G P ε d hs ht hgood.1 hgood.2.1 hgood.2.2 ha hb]
    refine Or.inr ⟨?_, ?_⟩
    · intro a ha b hb hca hcb
      rw [heq a ha b hb, heq s Subset.rfl t Subset.rfl]
      exact hgood.2.1 ha hb hca hcb
    · rw [heq s Subset.rfl t Subset.rfl]
      exact hgood.2.2
  · refine Or.inl ?_
    intro x hx y hy hxy
    exact hgood ((reduced_adj_iff G P ε d hs ht hx hy).mp hxy).2

/-- Each partition part is an independent set in the cleaned graph. -/
theorem reduced_independent (P : Finpartition (univ : Finset V)) (ε d : ℝ)
    {s : Finset V} (hs : s ∈ P.parts) :
    ∀ x ∈ s, ∀ y ∈ s, ¬ (G.regularityReduced P ε d).Adj x y := by
  intro x hx y hy hxy
  exact ((reduced_adj_iff G P ε d hs hs hx hy).mp hxy).2.1 rfl

/-- A bounded equitable regular partition and its actual cleaned subgraph.
Fewer than `ε n²` edges are deleted. The partition threshold is explicit. -/
theorem exists_cleaning [Nonempty V] (ε : ℝ) (l : ℕ)
    (hε : 0 < ε) (hl : 4 / ε ≤ (l : ℝ)) (hn : l ≤ Fintype.card V) :
    ∃ P : Finpartition (univ : Finset V),
      P.IsEquipartition ∧ l ≤ P.parts.card ∧
      P.parts.card ≤ SzemerediRegularity.bound (ε / 8) l ∧
      P.IsUniform G (ε / 8) ∧
      G.regularityReduced P (ε / 8) (ε / 4) ≤ G ∧
      (G.edgeFinset.card : ℝ) -
        (G.regularityReduced P (ε / 8) (ε / 4)).edgeFinset.card <
          ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨P, hPeq, hlP, hPbound, hPuniform⟩ :=
    szemeredi_regularity G (show 0 < ε / 8 by positivity) hn
  refine ⟨P, hPeq, hlP, hPbound, hPuniform, SimpleGraph.regularityReduced_le, ?_⟩
  have hparts : 4 / ε ≤ (P.parts.card : ℝ) := hl.trans (by exact_mod_cast hlP)
  have h := SimpleGraph.regularityReduced_edges_card_aux hε hPeq hPuniform hparts
  push_cast at h
  linarith

end Erdos1017.RegularityCleaning
