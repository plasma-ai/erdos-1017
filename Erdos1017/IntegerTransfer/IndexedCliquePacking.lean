module

public import Erdos1017.IntegerTransfer.CliquePackingAccounting

/-!
# Indexed families of edge-disjoint cliques

An indexed family of edge-disjoint cliques has no repeated vertex set and forms
an ordinary clique packing, so each indexed clique contributes its exact edge
saving to the integer bound (`cliquePartitionNumber_le_indexed_savings`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017

open scoped BigOperators

variable {n : ℕ} {I : Type*} [Fintype I]

omit [Fintype I] in
/-- Indexed actual edge-disjoint cliques have no repeated vertex set. -/
theorem indexedCliques_injective (S : I → Finset (Fin n))
    (hsize : ∀ i, 2 ≤ (S i).card)
    (hedge : ∀ i j u v, u ≠ v → u ∈ S i → v ∈ S i → u ∈ S j → v ∈ S j → i = j) :
    Function.Injective S := by
  intro i j h
  obtain ⟨u, hu, v, hv, huv⟩ := (Finset.one_lt_card (s := S i)).mp (by have := hsize i; omega)
  exact hedge i j u v huv hu hv (h ▸ hu) (h ▸ hv)

/-- Indexed actual edge-disjoint cliques form an ordinary clique packing. -/
theorem indexedCliques_packing (G : SimpleGraph (Fin n)) (S : I → Finset (Fin n))
    (hsize : ∀ i, 2 ≤ (S i).card) (hclique : ∀ i, G.IsClique (S i : Set (Fin n)))
    (hedge : ∀ i j u v, u ≠ v → u ∈ S i → v ∈ S i → u ∈ S j → v ∈ S j → i = j) :
    IsCliqueEdgePacking G (Finset.univ.image S) := by
  classical
  constructor
  · intro U hU
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hU
    exact ⟨hsize i, hclique i⟩
  · intro u v huv U hU hu hv V hV hu' hv'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hV
    exact congrArg S (hedge i j u v huv hu hv hu' hv')

/-- Each indexed packed clique contributes its exact edge saving to the integer bound. -/
theorem cliquePartitionNumber_le_indexed_savings (G : SimpleGraph (Fin n))
    (S : I → Finset (Fin n)) (hsize : ∀ i, 2 ≤ (S i).card)
    (hclique : ∀ i, G.IsClique (S i : Set (Fin n)))
    (hedge : ∀ i j u v, u ≠ v → u ∈ S i → v ∈ S i → u ∈ S j → v ∈ S j → i = j) :
    (cliquePartitionNumber G : ℝ) ≤ (G.edgeSet.ncard : ℝ) -
      ∑ i, (((S i).card.choose 2 : ℝ) - 1) := by
  classical
  have h := cliquePartitionNumber_le_edge_savings G (Finset.univ.image S)
    (indexedCliques_packing G S hsize hclique hedge)
  rw [Finset.sum_image (indexedCliques_injective S hsize hedge).injOn] at h
  exact h

end Erdos1017
