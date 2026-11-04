module

public import Erdos1017.FractionalLimit.FractionalGraphChanges

/-!
# Completing a clique packing to a partition

This module defines clique edge packings and their residual graph of uncovered
edges, and shows that any partition of the residual completes the packing on the
same graph, so the clique partition number is at most the packing size plus the
uncovered edge count (`cliquePartitionNumber_le_packing_cost`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017

open scoped BigOperators

variable {n : ℕ}

/-- A family of actual cliques whose unordered edge sets are pairwise disjoint. -/
def IsCliqueEdgePacking (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n))) : Prop :=
  (∀ S ∈ P, 2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))) ∧
    ∀ u v, u ≠ v → ∀ S ∈ P, u ∈ S → v ∈ S →
      ∀ T ∈ P, u ∈ T → v ∈ T → S = T

/-- The graph of edges not yet covered by a clique packing. -/
def packingResidual (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n))) : SimpleGraph (Fin n) :=
  G.deleteEdges {e | ∃ S ∈ P, e.toFinset ⊆ S}

theorem packingResidual_adj (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n))) (u v : Fin n) :
    (packingResidual G P).Adj u v ↔ G.Adj u v ∧ ¬∃ S ∈ P, u ∈ S ∧ v ∈ S := by
  simp only [packingResidual, SimpleGraph.deleteEdges_adj, Set.mem_ofPred_eq,
    Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]

theorem packingResidual_le (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n))) :
    packingResidual G P ≤ G := G.deleteEdges_le _

/-- Any partition of the uncovered edges completes the packing on the same graph. -/
theorem packing_union_partition (G : SimpleGraph (Fin n)) (P Q : Finset (Finset (Fin n)))
    (hP : IsCliqueEdgePacking G P) (hQ : (packingResidual G P).IsCliqueEdgePartition Q) :
    G.IsCliqueEdgePartition (P ∪ Q) := by
  classical
  refine ⟨?_, ?_⟩
  · intro S hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact hP.1 S hS
    · exact ⟨(hQ.1 S hS).1, ((hQ.1 S hS).2).mono (packingResidual_le G P)⟩
  · intro u v huv
    by_cases hcovered : ∃ S ∈ P, u ∈ S ∧ v ∈ S
    · obtain ⟨S, hS, hu, hv⟩ := hcovered
      refine ⟨S, ⟨Finset.mem_union_left _ hS, hu, hv⟩, ?_⟩
      rintro T ⟨hT, hTu, hTv⟩
      rcases Finset.mem_union.mp hT with hT | hT
      · exact hP.2 u v huv.ne T hT hTu hTv S hS hu hv
      · have hres := (hQ.1 T hT).2 hTu hTv huv.ne
        exact ((packingResidual_adj G P u v).mp hres).2 ⟨S, hS, hu, hv⟩ |>.elim
    · have hres := (packingResidual_adj G P u v).mpr ⟨huv, hcovered⟩
      obtain ⟨S, ⟨hS, hu, hv⟩, hunique⟩ := hQ.2 u v hres
      refine ⟨S, ⟨Finset.mem_union_right _ hS, hu, hv⟩, ?_⟩
      rintro T ⟨hT, hTu, hTv⟩
      rcases Finset.mem_union.mp hT with hT | hT
      · exact (hcovered ⟨T, hT, hTu, hTv⟩).elim
      · exact hunique T ⟨hT, hTu, hTv⟩

/-- Uncovered edges can always be added individually, with their exact count as the extra cost. -/
theorem exists_partition_extending_packing (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n)))
    (hP : IsCliqueEdgePacking G P) :
    ∃ R : Finset (Finset (Fin n)), G.IsCliqueEdgePartition R ∧ P ⊆ R ∧
      R.card ≤ P.card + (packingResidual G P).edgeSet.ncard := by
  classical
  obtain ⟨Q, hQ, hcard⟩ := (packingResidual G P).exists_isCliqueEdgePartition_card_eq
  refine ⟨P ∪ Q, packing_union_partition G P Q hP hQ, Finset.subset_union_left, ?_⟩
  have hcount : Q.card = (packingResidual G P).edgeSet.ncard := by
    rw [hcard, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [← hcount]
  exact Finset.card_union_le _ _

theorem cliquePartitionNumber_le_packing_cost (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n)))
    (hP : IsCliqueEdgePacking G P) :
    cliquePartitionNumber G ≤ P.card + (packingResidual G P).edgeSet.ncard := by
  obtain ⟨R, hR, _, hcard⟩ := exists_partition_extending_packing G P hP
  exact (cliquePartitionNumber_le_iff G).mpr ⟨R, hR, hcard⟩

end Erdos1017
