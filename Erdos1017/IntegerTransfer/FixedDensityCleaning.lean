/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
The removed-edge decomposition below adapts Mathlib's triangle-removal proof
to independent regularity and density parameters.
-/
module

public import Erdos1017.IntegerTransfer.RegularityCleaning
public import Erdos1017.IntegerTransfer.RegularPairSlicing

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.CastCard

/-!
# Regularity cleaning with a fixed density threshold

This module produces a bounded equitable partition and cleaned graph in which
the regularity error and the retained density threshold are chosen
independently, with removed edges accounted for by irregular, sparse and
internal pairs (`exists_fixed_density_cleaning`), and shows that trimming parts
preserves each dense regular pair at square-root regularity.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.RegularityCleaning

open Finset Fintype

variable {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A removed edge lies in an irregular pair, within a part, or in a sparse pair. -/
theorem unreduced_edges_subset (P : Finpartition (univ : Finset V)) (η d : ℝ) :
    (univ ×ˢ univ).filter (fun (x, y) =>
      G.Adj x y ∧ ¬(G.regularityReduced P η d).Adj x y) ⊆
      (P.nonUniforms G η).biUnion (fun (U, W) => U ×ˢ W) ∪ P.parts.biUnion offDiag ∪
        (P.sparsePairs G d).biUnion fun (U, W) => G.interedges U W := by
  rintro ⟨x, y⟩
  simp only [mem_filter, SimpleGraph.regularityReduced_adj, not_and, not_exists,
    not_le, mem_biUnion, mem_union, mem_product, Prod.exists, mem_offDiag, and_imp,
    or_assoc, and_assoc, P.mk_mem_nonUniforms, Finpartition.mk_mem_sparsePairs,
    SimpleGraph.mem_interedges_iff]
  intro hx hy h h'
  replace h' := h' h
  obtain ⟨U, hU, hx⟩ := P.exists_mem hx
  obtain ⟨W, hW, hy⟩ := P.exists_mem hy
  obtain rfl | hUW := eq_or_ne U W
  · exact Or.inr (Or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩)
  by_cases hreg : G.IsUniform η U W
  · exact Or.inr <| Or.inr ⟨U, W, hU, hW, hUW,
      h' _ hU _ hW hx hy hUW hreg, hx, hy, h⟩
  · exact Or.inl ⟨U, W, hU, hW, hUW, hreg, hx, hy⟩

/-- The regularity error and the retained density threshold can be chosen
independently. The three terms account for irregular, sparse and internal edges.
The edge decomposition is the one in Mathlib's triangle-removal proof. -/
theorem reduced_edge_loss [Nonempty V] (P : Finpartition (univ : Finset V))
    {η d τ : ℝ} (hη : 0 < η) (hd : 0 < d) (hτ : 0 < τ)
    (hP : P.IsEquipartition) (hPreg : P.IsUniform G η)
    (hparts : 4 / τ ≤ (P.parts.card : ℝ)) :
    (G.edgeFinset.card : ℝ) - (G.regularityReduced P η d).edgeFinset.card <
      (2 * η + 2 * d + τ / 4) * (Fintype.card V : ℝ) ^ 2 := by
  let A := (P.nonUniforms G η).biUnion fun (U, W) => U ×ˢ W
  let B := P.parts.biUnion offDiag
  let C := (P.sparsePairs G d).biUnion fun (U, W) => G.interedges U W
  have hcount :
      2 * ((G.edgeFinset.card : ℝ) - (G.regularityReduced P η d).edgeFinset.card) <
        (4 * η + τ / 2 + 4 * d) * (Fintype.card V : ℝ) ^ 2 := by
    calc
      _ = (((univ ×ˢ univ).filter fun (x, y) =>
          G.Adj x y ∧ ¬(G.regularityReduced P η d).Adj x y).card : ℝ) := by
        rw [univ_product_univ, mul_sub, filter_and_not, cast_card_sdiff]
        · norm_cast
          rw [SimpleGraph.two_mul_card_edgeFinset, SimpleGraph.two_mul_card_edgeFinset]
        · gcongr with xy _
          exact fun hxy => SimpleGraph.regularityReduced_le hxy
      _ ≤ (A ∪ B ∪ C).card := by
        gcongr
        exact unreduced_edges_subset G P η d
      _ ≤ (A ∪ B).card + C.card := by exact_mod_cast card_union_le (A ∪ B) C
      _ ≤ (A.card : ℝ) + B.card + C.card := by
        gcongr
        exact_mod_cast card_union_le A B
      _ < 4 * η * Fintype.card V ^ 2 + B.card + C.card := by
        gcongr
        exact hP.sum_nonUniforms_lt univ_nonempty hη hPreg
      _ ≤ 4 * η * Fintype.card V ^ 2 + τ / 2 * Fintype.card V ^ 2 +
          4 * d * Fintype.card V ^ 2 := by
        gcongr
        · exact hP.card_biUnion_offDiag_le hτ hparts
        · exact hP.card_interedges_sparsePairs_le (G := G) hd.le
      _ = _ := by ring
  nlinarith

/-- A bounded equitable partition and actual cleaned graph, with regularity
chosen before any lower bound on the eventual sampled edge densities. -/
theorem exists_fixed_density_cleaning [Nonempty V] (η d τ : ℝ) (l : ℕ)
    (hη : 0 < η) (hd : 0 < d) (hτ : 0 < τ)
    (hl : 4 / τ ≤ (l : ℝ)) (hn : l ≤ Fintype.card V) :
    ∃ P : Finpartition (univ : Finset V),
      P.IsEquipartition ∧ l ≤ P.parts.card ∧
      P.parts.card ≤ SzemerediRegularity.bound η l ∧ P.IsUniform G η ∧
      G.regularityReduced P η d ≤ G ∧
      (G.edgeFinset.card : ℝ) - (G.regularityReduced P η d).edgeFinset.card <
        (2 * η + 2 * d + τ / 4) * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨P, hPeq, hlP, hPbound, hPuniform⟩ := szemeredi_regularity G hη hn
  refine ⟨P, hPeq, hlP, hPbound, hPuniform, SimpleGraph.regularityReduced_le, ?_⟩
  exact reduced_edge_loss G P hη hd hτ hPeq hPuniform
    (hl.trans (by exact_mod_cast hlP))

/-- Trimming parts of the cleaned graph preserves each dense regular pair
at square-root regularity, losing at most the original regularity error in density. -/
theorem trimmed_reduced_pair (P : Finpartition (univ : Finset V)) {η d : ℝ}
    (hη : η ≤ 1 / 4) {s t s' t' : Finset V}
    (hs : s ∈ P.parts) (ht : t ∈ P.parts) (hs' : s' ⊆ s) (ht' : t' ⊆ t)
    (hscard : (s.card : ℝ) * Real.sqrt η ≤ s'.card)
    (htcard : (t.card : ℝ) * Real.sqrt η ≤ t'.card) :
    (∀ x ∈ s', ∀ y ∈ t', ¬(G.regularityReduced P η d).Adj x y) ∨
      ((G.regularityReduced P η d).IsUniform (Real.sqrt η) s' t' ∧
        d - η ≤ (G.regularityReduced P η d).edgeDensity s' t') := by
  obtain hempty | ⟨hreg, hden⟩ := reduced_pair G P η d hs ht
  · exact Or.inl (fun x hx y hy => hempty x (hs' hx) y (ht' hy))
  · obtain ⟨hreg', hclose⟩ := RegularPair.slice_sqrt
      (G.regularityReduced P η d) hreg hη hs' ht' hscard htcard
    exact Or.inr ⟨hreg', by have := (abs_sub_lt_iff.mp hclose).2; linarith⟩

end Erdos1017.RegularityCleaning
