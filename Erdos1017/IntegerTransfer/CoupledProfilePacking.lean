module

public import Erdos1017.IntegerTransfer.CoupledCliqueMatching
public import Erdos1017.IntegerTransfer.AllocatedProfileEdgeTransport
public import Erdos1017.IntegerTransfer.EmbeddedCliquePacking

/-!
# Coupled matchings of selected profile layers

This module defines the rank and role embedding of a profile layer and proves
that the selected fractional profile layers can all be matched in one
categorical allocation outcome, with the same auxiliary cost control
(`exists_coupled_profile_matchings`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators
open TransversalThinning TransversalClique

/-- A profile layer's rank lies in the fixed range of clique sizes. -/
def layerRank {ℓ C b : ℕ} (L : Finset (Finset (Fin ℓ) × Fin C))
    (hL : ∀ s ∈ L, 3 ≤ s.1.card ∧ s.1.card ≤ b) (i : L) : Fin (b - 2) :=
  ⟨i.val.1.card - 3, by have := hL i.val i.property; omega⟩

/-- Increasing local roles for one selected profile layer. -/
def layerEmbedding {ℓ C b : ℕ} (L : Finset (Finset (Fin ℓ) × Fin C))
    (hL : ∀ s ∈ L, 3 ≤ s.1.card ∧ s.1.card ≤ b) (i : L) :
    Fin (2 + ((layerRank L hL i).val + 1)) ↪o Fin ℓ :=
  i.val.1.orderEmbOfFin (by have := hL i.val i.property; dsimp only [layerRank]; omega)

/-- Every local role of a layer belongs to its actual profile. -/
theorem layerEmbedding_mem {ℓ C b : ℕ} (L : Finset (Finset (Fin ℓ) × Fin C))
    (hL : ∀ s ∈ L, 3 ≤ s.1.card ∧ s.1.card ≤ b) (i : L)
    (j : Fin (2 + ((layerRank L hL i).val + 1))) : layerEmbedding L hL i j ∈ i.val.1 :=
  i.val.1.orderEmbOfFin_mem _ j

/-- Selected actual fractional profile layers can all be matched in one
categorical allocation outcome, with the same auxiliary cost control. -/
theorem exists_coupled_profile_matchings (b : ℕ) (hb : 3 ≤ b) (δ ρ : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (M : ℕ) (α₀ : ℝ), 0 < α₀ →
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ (ℓ C : ℕ), 0 < C → 1 ≤ (C : ℝ) * δ →
        ∀ (G : SimpleGraph (Fin ℓ × Fin n)) [DecidableRel G.Adj]
          (_hparts : ∀ i (a z : Fin n), ¬G.Adj (i, a) (i, z))
          (w : Finset (Fin ℓ × Fin n) → ℝ),
          (∀ S, 0 ≤ w S) →
          (∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × Fin n))) →
          (∀ v z, G.Adj v z → pairLoad w v z = 1) →
          ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
          (∀ i j : Fin ℓ, i < j → (∀ a z : Fin n, ¬G.Adj (i, a) (j, z)) ∨
            (G.IsUniform ε (MultipartiteCounting.part i) (MultipartiteCounting.part j) ∧
              δ ≤ G.edgeDensity (MultipartiteCounting.part i) (MultipartiteCounting.part j))) →
          ∀ (L : Finset (Finset (Fin ℓ) × Fin C))
            (hL : ∀ s ∈ L, 3 ≤ s.1.card ∧ s.1.card ≤ b), L.card ≤ M →
            (∀ s ∈ L, α₀ ≤ allocationDensity n C (typeMass w s.1)) →
            ∀ (Z : (Coordinate ℓ (Fin n) → AllocationLabel ℓ C) → ℝ), (∀ X, 0 ≤ Z X) →
              (∑ X, CategoricalSampling.weight (allocationProbability G (typeMass w) C) X * Z X) ≤
                1 - min ρ (1 / 2) →
            ∃ X : Coordinate ℓ (Fin n) → AllocationLabel ℓ C,
              0 < CategoricalSampling.weight (allocationProbability G (typeMass w) C) X ∧ Z X < 1 ∧
              ∃ T : ∀ i : L, Finset (Fin (2 + ((layerRank L hL i).val + 1)) → Fin n),
                (∀ i : L, T i ⊆ assignments (thinned
                  (G.comap (MultipartiteCounting.partVertexEmbedding (layerEmbedding L hL i).toEmbedding))
                  (fun v => CategoricalSampling.projection (some i.val) X
                    (profileCoordinateEmbedding (layerEmbedding L hL i).toEmbedding v)))) ∧
                (∀ i : L, (T i : Set (Fin (2 + ((layerRank L hL i).val + 1)) → Fin n)).PairwiseDisjoint edges) ∧
                (∀ i : L, (1 - ρ) * ((allocatedEdges G X (some i.val)).card : ℝ) /
                  (2 + ((layerRank L hL i).val + 1)).choose 2 ≤ (T i).card) ∧
                (∀ i : L, ((allocatedEdges G X (some i.val)).card : ℝ) ≤
                  i.val.1.card.choose 2 * ((1 + ρ) * typeMass w i.val.1 / C)) := by
  classical
  obtain ⟨ε₀, hε₀, hmaster⟩ := exists_coupled_clique_matchings (b - 2) (by omega) δ ρ hδ hρ
  refine ⟨ε₀, hε₀, ?_⟩
  intro M α₀ hα₀
  obtain ⟨n₀, hn₀, hsize⟩ := hmaster M α₀ hα₀
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn ℓ C hC hscale G _ hparts w hw hsupport hbalance ε hε hsmall hclean L hL hLM hfloor Z hZ hZmean
  let : NeZero n := ⟨by omega⟩
  let rank := layerRank L hL
  let φ := layerEmbedding L hL
  let H (i : L) := G.comap (MultipartiteCounting.partVertexEmbedding (φ i).toEmbedding)
  let α (i : L) := allocationDensity n C (typeMass w i.val.1)
  have hα (i : L) : α₀ ≤ α i := hfloor i.val i.property
  have hmass (i : L) : 0 < typeMass w i.val.1 := by
    have hpos : 0 < α i := hα₀.trans_le (hα i)
    have hden : 0 < (C : ℝ) * (n : ℝ) ^ 2 :=
      mul_pos (by exact_mod_cast hC) (sq_pos_of_pos (by exact_mod_cast (show 0 < n by omega)))
    exact (div_pos_iff_of_pos_right hden).mp hpos
  have hαδ (i : L) : α i ≤ δ := by
    have h := (allocationDensity_bounds G hparts w hw hsupport hbalance δ C hC hscale i.val.1
      (by have := (hL i.val i.property).1; omega) (hmass i)).2
    simpa only [α, Fintype.card_fin] using h
  have hregular (i : L) (j k : Fin (2 + ((rank i).val + 1))) (hjk : j < k) :
      (H i).IsUniform ε (MultipartiteCounting.part j) (MultipartiteCounting.part k) ∧
        δ ≤ pairDensity (H i) (j, k) := by
    have hlt := (φ i).strictMono hjk
    have hpos := typeMass_pair_positive G w hsupport i.val.1 (hmass i).ne'
      (φ i j) (φ i k) (layerEmbedding_mem L hL i j) (layerEmbedding_mem L hL i k) hlt.ne
    rcases hclean (φ i j) (φ i k) hlt with hempty | hreg
    · have hz : pairEdgeCount G (φ i j) (φ i k) = 0 := by
        apply Finset.card_eq_zero.mpr
        exact Finset.eq_empty_iff_forall_notMem.mpr (fun p hp => hempty p.1 p.2 (Finset.mem_filter.mp hp).2)
      omega
    · constructor
      · exact MultipartiteCounting.part_regular_embedding G (φ i).toEmbedding j k ε hreg.1
      · change δ ≤ ((G.comap (MultipartiteCounting.partVertexEmbedding (φ i).toEmbedding)).edgeDensity
          (MultipartiteCounting.part j) (MultipartiteCounting.part k) : ℝ)
        rw [MultipartiteCounting.part_density_embedding]
        exact hreg.2
  have hprob (i : L) (v : Coordinate (2 + ((rank i).val + 1)) (Fin n)) :
      allocationProbability G (typeMass w) C (profileCoordinateEmbedding (φ i).toEmbedding v) (some i.val) =
        partProbability (normalizedProbability (H i) (α i)) v := by
    simpa only [H, α, Fintype.card_fin, Prod.eta, partProbability, normalizedProbability, pairDensity] using allocationProbability_profile G (typeMass w) C hC
      i.val.1 i.val.2 (φ i).toEmbedding (layerEmbedding_mem L hL i)
      (fun j k hjk => typeMass_pair_positive G w hsupport _ (hmass i).ne' _ _
        (layerEmbedding_mem L hL i j) (layerEmbedding_mem L hL i k) ((φ i).injective.ne hjk)) v
  obtain ⟨X, hX, hZX, hT⟩ := hsize n hn L (by simpa only [Fintype.card_coe] using hLM) rank H ε hε hsmall
    (fun i j k h => (hregular i j k h).1) (fun i j k h => (hregular i j k h).2)
    (Coordinate ℓ (Fin n)) (AllocationLabel ℓ C) (allocationProbability G (typeMass w) C)
    (allocationProbability_nonneg G (typeMass w) (typeMass_nonneg w hw) C)
    (typeMass_allocationProbability_total G hparts w hsupport hbalance C hC)
    Z hZ hZmean (fun i => some i.val) (fun i => profileCoordinateEmbedding (φ i).toEmbedding) α hα hαδ hprob
  choose T hsub hdisjoint hmatching horder using hT
  have heq (i : L) :
      (graphEdges (thinned (H i) (fun v => CategoricalSampling.projection (some i.val) X
        (profileCoordinateEmbedding (φ i).toEmbedding v)))).card = (allocatedEdges G X (some i.val)).card := by
    have hmap := map_graphEdges_eq_allocated G i.val.1 i.val.2 (φ i)
      (fun j hj => by
        change j ∈ Set.range (φ i)
        rw [show Set.range (φ i) = i.val.1 from i.val.1.range_orderEmbOfFin (by have := hL i.val i.property; dsimp only [rank, layerRank]; omega)]
        exact hj) X
      (allocatedEdges_roles G hparts (typeMass w) (typeMass_nonneg w hw) X hX i.val.1 i.val.2)
    simpa only [Finset.card_map] using congrArg Finset.card hmap
  refine ⟨X, hX, hZX, T, hsub, hdisjoint, ?_, ?_⟩
  · intro i
    have h := hmatching i
    rw [heq i] at h
    exact h
  · intro i
    have h := graphEdges_card_le_of_role_control (H i)
      (fun v => CategoricalSampling.projection (some i.val) X (profileCoordinateEmbedding (φ i).toEmbedding v))
      (α i) ρ (by simpa only [Fintype.card_fin] using horder i)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hCp : (0 : ℝ) < C := by exact_mod_cast hC
    have hk : 2 + ((rank i).val + 1) = i.val.1.card := by have := hL i.val i.property; dsimp only [rank, layerRank]; omega
    rw [heq i, Fintype.card_fin, hk] at h
    convert h using 1
    dsimp only [α, allocationDensity]
    congr 1
    field_simp

end Erdos1017.MultipartiteAllocation
