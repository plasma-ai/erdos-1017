module

public import Erdos1017.IntegerTransfer.CoupledProfilePacking
public import Erdos1017.IntegerTransfer.AllocationResidualCost
public import Erdos1017.IntegerTransfer.MultipartiteGraphEdges

/-!
# Integer partition cost from coupled profile matchings

Coupled profile matchings complete to an integer clique partition, with the
unmatched allocated edges charged individually
(`cliquePartitionNumber_map_le_profile_cost`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators
open TransversalThinning TransversalClique

variable {ℓ C b n N : ℕ}

/-- Coupled profile matchings complete to an actual integer partition, with
the unmatched allocated edges charged individually. -/
theorem cliquePartitionNumber_map_le_profile_cost
    (G : SimpleGraph (Fin ℓ × Fin n)) [DecidableRel G.Adj]
    (hparts : ∀ i (a z : Fin n), ¬G.Adj (i, a) (i, z))
    (f : (Fin ℓ × Fin n) ↪ Fin N)
    (mass : Finset (Fin ℓ) → ℝ) (hmass : ∀ K, 0 ≤ mass K)
    (L : Finset (Finset (Fin ℓ) × Fin C))
    (hL : ∀ s ∈ L, 3 ≤ s.1.card ∧ s.1.card ≤ b)
    (X : Coordinate ℓ (Fin n) → AllocationLabel ℓ C)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (T : ∀ i : L, Finset (Fin (2 + ((layerRank L hL i).val + 1)) → Fin n))
    (hsub : ∀ i : L, T i ⊆ assignments (thinned
      (G.comap (MultipartiteCounting.partVertexEmbedding (layerEmbedding L hL i).toEmbedding))
      (fun v => CategoricalSampling.projection (some i.val) X
        (profileCoordinateEmbedding (layerEmbedding L hL i).toEmbedding v))))
    (hdisjoint : ∀ i : L, (T i : Set (Fin (2 + ((layerRank L hL i).val + 1)) → Fin n)).PairwiseDisjoint edges)
    (hmatching : ∀ i : L, (1 - ρ) * ((allocatedEdges G X (some i.val)).card : ℝ) /
      (2 + ((layerRank L hL i).val + 1)).choose 2 ≤ (T i).card)
    (horder : ∀ i : L, ((allocatedEdges G X (some i.val)).card : ℝ) ≤
      i.val.1.card.choose 2 * ((1 + ρ) * mass i.val.1 / C)) :
    (cliquePartitionNumber (G.map f) : ℝ) ≤
      ((residualAllocatedEdges G X (fun i : L => some i.val)).card : ℝ) +
        (1 + ρ * (b.choose 2 : ℝ)) * (1 + ρ) * ∑ i : L, mass i.val.1 / C := by
  classical
  let k (i : L) := 2 + ((layerRank L hL i).val + 1)
  have hk (i : L) : k i = i.val.1.card := by
    have := hL i.val i.property
    dsimp only [k, layerRank]
    omega
  have hinj : Function.Injective (fun i : L => (some i.val : AllocationLabel ℓ C)) := by
    intro i j h
    exact Subtype.ext (Option.some.inj h)
  have hpack := cliquePartitionNumber_le_embedded_matchings G (G.map f) f
    (fun _ _ h => SimpleGraph.map_adj_apply.mpr h) k (fun i => by dsimp only [k]; omega)
    (layerEmbedding L hL) X (fun i : L => some i.val) hinj T hsub hdisjoint
  have hedge : (G.map f).edgeSet.ncard = (TransversalClique.graphEdges G).card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, SimpleGraph.card_edgeFinset_map,
      graphEdges_card_eq_edgeFinset G hparts]
  rw [hedge] at hpack
  have hdecomp := allocatedEdges_card_decomposition G X (fun i : L => some i.val) hinj
  have hcost (i : L) :
      ((allocatedEdges G X (some i.val)).card : ℝ) - ((k i).choose 2 - 1 : ℝ) * (T i).card ≤
        (1 + ρ * (b.choose 2 : ℝ)) * (1 + ρ) * (mass i.val.1 / C) := by
    have hr : (1 : ℝ) ≤ (k i).choose 2 := by
      exact_mod_cast Nat.choose_pos (show 2 ≤ k i by dsimp only [k]; omega)
    have h := matching_cost_le (mass := mass i.val.1 / C) (Nat.cast_nonneg _) hr hρ (hmatching i)
      (by simpa only [hk i, mul_div_assoc] using horder i)
    have hchoose : ((k i).choose 2 : ℝ) ≤ b.choose 2 := by
      exact_mod_cast Nat.choose_le_choose 2 ((hk i).trans_le (hL i.val i.property).2)
    have hcoef : (1 + ρ * ((k i).choose 2 : ℝ)) ≤ 1 + ρ * (b.choose 2 : ℝ) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hchoose hρ) 1
    have hnonneg : 0 ≤ (1 + ρ) * (mass i.val.1 / C) :=
      mul_nonneg (by linarith) (div_nonneg (hmass _) (Nat.cast_nonneg C))
    calc
      _ ≤ (1 + ρ * ((k i).choose 2 : ℝ)) * (1 + ρ) * (mass i.val.1 / C) := h
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hnonneg
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset L)) => hcost i)
  simp only [Finset.sum_sub_distrib, mul_comm ((k _).choose 2 - 1 : ℝ), ← Finset.mul_sum] at hsum
  linarith only [hpack, hdecomp, hsum]

end Erdos1017.MultipartiteAllocation
