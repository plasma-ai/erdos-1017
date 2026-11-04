module

public import Erdos1017.IntegerTransfer.TransversalHypergraphBounds
public import Erdos1017.IntegerTransfer.Nibble.HypergraphActiveTransport

/-!
# Matchings in the transversal clique hypergraph

Every vertex of the clique hypergraph is an inter-part graph edge, an edge
matching recovers a family of complete transversals with exact cardinality and
pairwise edge disjointness, and a matching exists from an aggregate
squared-error input without a maximum-degree estimate.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

open scoped BigOperators
open TransversalThinning

variable {k : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- The actual inter-part graph edges, each represented once. -/
def graphEdges (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj] : Finset (Coordinate k A) :=
  Finset.univ.filter (fun v => v.1.1 < v.2.1 ∧ G.Adj v.1 v.2)

/-- Every vertex of the clique hypergraph is an actual graph edge. -/
theorem hypergraph_supported (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (e : Finset (Coordinate k A)) (he : e ∈ hypergraph G) : e ⊆ graphEdges G := by
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp he
  intro v hv
  have hv := (mem_edges_iff X v).mp hv
  have hreal := (Finset.mem_filter.mp hX).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hv.1, ?_⟩
  have h := hreal (v.1.1, v.2.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.1⟩)
  simpa only [hv.2.1, hv.2.2] using h

/-- An actual edge matching recovers a family of actual complete transversals,
with exact cardinality and pairwise edge disjointness. -/
theorem assignments_of_matching (hk : 2 ≤ k)
    (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (M : Finset (Finset (Coordinate k A))) (hM : M ⊆ hypergraph G)
    (hdisj : (M : Set (Finset (Coordinate k A))).PairwiseDisjoint id) :
    ∃ T : Finset (Fin k → A), T ⊆ assignments G ∧
      (T : Set (Fin k → A)).PairwiseDisjoint edges ∧ T.card = M.card := by
  let T := (assignments G).filter (fun X => edges X ∈ M)
  have himage : T.image edges = M := by
    ext e
    simp only [T, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨X, ⟨_, hX⟩, rfl⟩
      exact hX
    · intro he
      obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp (hM he)
      exact ⟨X, ⟨hX, he⟩, rfl⟩
  refine ⟨T, Finset.filter_subset _ _, ?_, ?_⟩
  · intro X hX Y hY hXY
    exact hdisj (Finset.mem_filter.mp hX).2 (Finset.mem_filter.mp hY).2
      ((edges_injective hk).ne hXY)
  · rw [← himage, Finset.card_image_of_injective _ (edges_injective hk)]

/-- Matching for the actual clique hypergraph, with aggregate squared-error
input and no assumed maximum-degree estimate. All thresholds precede the graph. -/
theorem exists_matching_of_squared_error (k : ℕ) (hk : 3 ≤ k) (C₀ δ : ℝ)
    (hC₀ : 1 ≤ C₀) (hδ : 0 < δ) :
    ∃ η D₀ : ℝ, 0 < η ∧ 0 < D₀ ∧
      ∀ (n : ℕ), 0 < n →
        ∀ (G : SimpleGraph (Fin k × Fin n)) [DecidableRel G.Adj]
          (μ : Coordinate k (Fin n) → ℝ) (W : Finset (Coordinate k (Fin n))) (D : ℝ),
          D₀ ≤ D →
          (∀ v ∈ graphEdges G, μ v ≤ C₀ * D) →
          (n : ℝ) ^ (k - 3) ≤ η * D →
          (∀ v ∈ graphEdges G, v ∉ W →
            (1 - η) * D ≤ (HypergraphNibble.degree (hypergraph G) v : ℝ) ∧
              (HypergraphNibble.degree (hypergraph G) v : ℝ) ≤ (1 + η) * D) →
          ((W ∩ graphEdges G).card : ℝ) ≤ η * (graphEdges G).card →
          (∑ v ∈ graphEdges G, ((HypergraphNibble.degree (hypergraph G) v : ℝ) - μ v) ^ 2) ≤
            η * (graphEdges G).card * D ^ 2 →
          ∃ T : Finset (Fin k → Fin n), T ⊆ assignments G ∧
            (T : Set (Fin k → Fin n)).PairwiseDisjoint edges ∧
              (1 - δ) * (graphEdges G).card / k.choose 2 ≤ (T.card : ℝ) := by
  have hr : 2 ≤ k.choose 2 := (by decide : 2 ≤ Nat.choose 3 2).trans (Nat.choose_le_choose 2 hk)
  obtain ⟨η, D₀, hη, hD₀, hmatch⟩ :=
    HypergraphNibble.near_perfect_matching_of_squared_error (k.choose 2) C₀ δ hr hC₀ hδ
  refine ⟨η, D₀, hη, hD₀, ?_⟩
  intro n hn G _ μ W D hD hμ hcodegree hregular hW hsquare
  let : NeZero n := ⟨by omega⟩
  let U := graphEdges G
  let H := hypergraph G
  have hsupp : ∀ e ∈ H, e ⊆ U := hypergraph_supported G
  have hWcard : ((W.subtype (fun v => v ∈ U)).card : ℝ) ≤ η * Fintype.card U := by
    simpa only [Finset.card_subtype, Finset.filter_mem_eq_inter, Fintype.card_coe] using hW
  obtain ⟨M, hM, hdisj, hcard⟩ := hmatch U (HypergraphNibble.onVertices H U)
    (fun v => μ v) (W.subtype (fun v => v ∈ U)) D hD
    (by
      rintro e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      have hmap := Finset.subtype_map_of_mem (hsupp a ha)
      have h := congrArg Finset.card hmap
      simpa only [Finset.card_map, hypergraph_uniform G a ha] using h)
    (fun v => hμ v v.property)
    (by
      intro v w hvw
      rw [HypergraphNibble.codegree_onVertices H U hsupp]
      have hbound : (HypergraphNibble.codegree H v w : ℝ) ≤ (n : ℝ) ^ (k - 3) := by
        have h := codegree_le (by omega : 2 ≤ k) G v w (Subtype.val_injective.ne hvw)
        simp only [Fintype.card_fin] at h
        exact_mod_cast h
      exact hbound.trans hcodegree)
    (by
      intro v hv
      rw [HypergraphNibble.degree_onVertices H U hsupp]
      apply hregular v v.property
      simpa only [Finset.mem_subtype] using hv)
    hWcard
    (by
      simp only [HypergraphNibble.degree_onVertices H U hsupp, Fintype.card_coe]
      have hsum : (∑ v : U, ((HypergraphNibble.degree H v : ℝ) - μ v) ^ 2) =
          ∑ v ∈ U, ((HypergraphNibble.degree H v : ℝ) - μ v) ^ 2 :=
        Finset.sum_coe_sort U (fun v : Coordinate k (Fin n) => ((HypergraphNibble.degree H v : ℝ) - μ v) ^ 2)
      rw [hsum]
      exact hsquare)
  obtain ⟨P, hP, hPdisj, hPcard⟩ := HypergraphNibble.matching_onVertices H U hsupp M hM hdisj
  obtain ⟨T, hT, hTdisj, hTcard⟩ := assignments_of_matching (by omega) G P hP hPdisj
  refine ⟨T, hT, hTdisj, ?_⟩
  simpa only [Fintype.card_coe, hTcard, hPcard] using hcard

end Erdos1017.TransversalClique
