module

public import Erdos1017.IntegerTransfer.CliquePackingCompletion

/-!
# Repairing an integer partition of a subgraph

An edge partition of a subgraph is a clique packing of the original graph, and
completing it adds at most one clique per missing edge, so fractional deletion
repair and integer edge completion share one edge-loss budget
(`cliquePartitionNumber_le_value_of_subgraph_rounding`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017

variable {n : ℕ}

/-- An edge partition of a subgraph is an actual clique packing in the original graph. -/
theorem partition_isPacking_of_le (G H : SimpleGraph (Fin n)) (hHG : H ≤ G)
    (P : Finset (Finset (Fin n))) (hP : H.IsCliqueEdgePartition P) : IsCliqueEdgePacking G P := by
  constructor
  · intro S hS
    exact ⟨(hP.1 S hS).1, ((hP.1 S hS).2).mono hHG⟩
  · intro u v huv S hS hu hv T hT hu' hv'
    have hadj := (hP.1 S hS).2 hu hv huv
    obtain ⟨U, _, huniq⟩ := hP.2 u v hadj
    exact (huniq S ⟨hS, hu, hv⟩).trans (huniq T ⟨hT, hu', hv'⟩).symm

/-- Completing a subgraph partition adds at most one clique per missing edge. -/
theorem cliquePartitionNumber_le_subgraph_add_edges (G H : SimpleGraph (Fin n)) (hHG : H ≤ G) :
    cliquePartitionNumber G ≤ cliquePartitionNumber H +
      (FractionalGraph.finiteEdges G \ FractionalGraph.finiteEdges H).card := by
  classical
  obtain ⟨P, hP, hcard⟩ := partition_card_le_cliquePartitionNumber H
  have hpacking := partition_isPacking_of_le G H hHG P hP
  have hres : (packingResidual G P).edgeFinset =
      FractionalGraph.finiteEdges G \ FractionalGraph.finiteEdges H := by
    ext e
    induction e using Sym2.ind with
    | h u v =>
      rw [Finset.mem_sdiff, FractionalGraph.mem_finiteEdges, FractionalGraph.mem_finiteEdges]
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, packingResidual_adj]
      constructor
      · rintro ⟨hG, hnot⟩
        refine ⟨hG, ?_⟩
        intro hH
        obtain ⟨S, hS, _⟩ := hP.2 u v hH
        exact hnot ⟨S, hS⟩
      · rintro ⟨hG, hnot⟩
        refine ⟨hG, ?_⟩
        rintro ⟨S, hS, hu, hv⟩
        exact hnot ((hP.1 S hS).2 hu hv hG.ne)
  have hcount : (packingResidual G P).edgeSet.ncard =
      (FractionalGraph.finiteEdges G \ FractionalGraph.finiteEdges H).card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, hres]
  have h := cliquePartitionNumber_le_packing_cost G P hpacking
  rw [hcount] at h
  exact h.trans (Nat.add_le_add_right hcard _)

/-- The same deleted-edge cardinality is the difference of the actual edge counts. -/
theorem subgraph_removed_edges_card (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H ≤ G) :
    ((FractionalGraph.finiteEdges G \ FractionalGraph.finiteEdges H).card : ℝ) =
      (G.edgeFinset.card : ℝ) - H.edgeFinset.card := by
  have hsub : FractionalGraph.finiteEdges H ⊆ FractionalGraph.finiteEdges G :=
    by
      intro e he
      induction e using Sym2.ind with
      | h u v => exact (FractionalGraph.mem_finiteEdges G u v).mpr (hHG ((FractionalGraph.mem_finiteEdges H u v).mp he))
  rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  have hG : FractionalGraph.finiteEdges G = G.edgeFinset := by
    ext e
    simp only [FractionalGraph.finiteEdges, SimpleGraph.mem_edgeFinset]
  have hH : FractionalGraph.finiteEdges H = H.edgeFinset := by
    ext e
    simp only [FractionalGraph.finiteEdges, SimpleGraph.mem_edgeFinset]
  rw [hG, hH]

/-- Fractional deletion repair and integer edge completion use one common
actual edge-loss budget. -/
theorem cliquePartitionNumber_le_value_of_subgraph_rounding
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H ≤ G) (E : ℝ)
    (hround : (cliquePartitionNumber H : ℝ) ≤ FractionalGraph.value H + E) :
    (cliquePartitionNumber G : ℝ) ≤ FractionalGraph.value G + E +
      4 * ((G.edgeFinset.card : ℝ) - H.edgeFinset.card) := by
  have hcost := FractionalGraph.value_le_edit_cost G H
  have hsub : FractionalGraph.finiteEdges H ⊆ FractionalGraph.finiteEdges G :=
    by
      intro e he
      induction e using Sym2.ind with
      | h u v => exact (FractionalGraph.mem_finiteEdges G u v).mpr (hHG ((FractionalGraph.mem_finiteEdges H u v).mp he))
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.card_empty, Nat.cast_zero, add_zero,
    subgraph_removed_edges_card G H hHG] at hcost
  have hrepair : (cliquePartitionNumber G : ℝ) ≤ cliquePartitionNumber H +
      ((FractionalGraph.finiteEdges G \ FractionalGraph.finiteEdges H).card : ℝ) := by
    exact_mod_cast cliquePartitionNumber_le_subgraph_add_edges G H hHG
  rw [subgraph_removed_edges_card G H hHG] at hrepair
  linarith only [hround, hcost, hrepair]

end Erdos1017
