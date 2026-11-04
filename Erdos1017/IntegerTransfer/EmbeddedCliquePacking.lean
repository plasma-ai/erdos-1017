module

public import Erdos1017.IntegerTransfer.EmbeddedCliqueGeometry
public import Erdos1017.IntegerTransfer.FiniteCategoricalSampling
public import Erdos1017.IntegerTransfer.CliquePackingAccounting
public import Erdos1017.IntegerTransfer.IndexedCliquePacking

/-!
# Combining local matchings into an ambient clique packing

Local clique matchings in distinct allocation groups have disjoint ambient
edges, since mutually exclusive labels force disjoint physical edges, so they
combine into one packing and give an integer bound after any ambient embedding
(`cliquePartitionNumber_le_embedded_matchings`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

open scoped BigOperators
open TransversalThinning MultipartiteAllocation

variable {ℓ : ℕ} {A J : Type*} [Fintype A] [DecidableEq A] [DecidableEq J]

/-- Every actual embedded edge of a selected local clique has its group's label. -/
theorem embeddedEdges_selected (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    {k : ℕ} (φ : Fin k ↪o Fin ℓ) (X : Coordinate ℓ A → J) (label : J)
    (x : Fin k → A)
    (hx : x ∈ assignments (thinned (G.comap (MultipartiteCounting.partVertexEmbedding φ.toEmbedding))
      (fun v => CategoricalSampling.projection label X (profileCoordinateEmbedding φ.toEmbedding v))))
    (v : Coordinate ℓ A) (hv : v ∈ embeddedEdges φ x) : X v = label := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
  have h := (mem_edges_iff x w).mp hw
  have hreal := (Finset.mem_filter.mp hx).2
  have hadj := hreal (w.1.1, w.2.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩)
  have hsel := ((thinned_adj_iff _ _ h.1 _ _).mp hadj).2
  rw [h.2.1, h.2.2] at hsel
  simpa only [CategoricalSampling.projection, decide_eq_true_eq] using hsel

/-- Selected local cliques are actual ambient cliques. -/
theorem embeddedVertices_selected_isClique (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    {k : ℕ} (φ : Fin k ↪o Fin ℓ) (X : Coordinate ℓ A → J) (label : J)
    (x : Fin k → A)
    (hx : x ∈ assignments (thinned (G.comap (MultipartiteCounting.partVertexEmbedding φ.toEmbedding))
      (fun v => CategoricalSampling.projection label X (profileCoordinateEmbedding φ.toEmbedding v)))) :
    G.IsClique (embeddedVertices φ x : Set (Fin ℓ × A)) := by
  apply embeddedVertices_isClique G φ x
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro e he
  exact ((Finset.mem_filter.mp hx).2 e he).1

/-- Mutually exclusive allocation labels force disjoint physical clique edges. -/
theorem embeddedEdges_disjoint_of_label_ne (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    {k m : ℕ} (φ : Fin k ↪o Fin ℓ) (ψ : Fin m ↪o Fin ℓ)
    (X : Coordinate ℓ A → J) (a b : J) (hab : a ≠ b)
    (x : Fin k → A) (y : Fin m → A)
    (hx : x ∈ assignments (thinned (G.comap (MultipartiteCounting.partVertexEmbedding φ.toEmbedding))
      (fun v => CategoricalSampling.projection a X (profileCoordinateEmbedding φ.toEmbedding v))))
    (hy : y ∈ assignments (thinned (G.comap (MultipartiteCounting.partVertexEmbedding ψ.toEmbedding))
      (fun v => CategoricalSampling.projection b X (profileCoordinateEmbedding ψ.toEmbedding v)))) :
    Disjoint (embeddedEdges φ x) (embeddedEdges ψ y) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact hab ((embeddedEdges_selected G φ X a x hx v hv).symm.trans
    (embeddedEdges_selected G ψ X b y hy v hw))

omit [Fintype A] in
/-- Within one group the coordinate embedding preserves the local matching. -/
theorem embeddedEdges_disjoint {k : ℕ} (φ : Fin k ↪o Fin ℓ) (x y : Fin k → A)
    (hxy : Disjoint (edges x) (edges y)) :
    Disjoint (embeddedEdges φ x) (embeddedEdges φ y) := by
  exact (Finset.disjoint_map _).mpr hxy

omit [Fintype A] in
/-- A common pair of distinct ambient vertices supplies a common physical edge. -/
theorem embeddedEdges_common {k m : ℕ} (φ : Fin k ↪o Fin ℓ) (ψ : Fin m ↪o Fin ℓ)
    (x : Fin k → A) (y : Fin m → A) {v w : Fin ℓ × A} (hvw : v ≠ w)
    (hvx : v ∈ embeddedVertices φ x) (hwx : w ∈ embeddedVertices φ x)
    (hvy : v ∈ embeddedVertices ψ y) (hwy : w ∈ embeddedVertices ψ y) :
    ∃ c, c ∈ embeddedEdges φ x ∧ c ∈ embeddedEdges ψ y := by
  have hroles := embeddedVertices_role_ne φ x hvx hwx hvw
  rcases lt_or_gt_of_ne hroles with hlt | hlt
  · exact ⟨(v, w), (mem_embeddedEdges φ x _).mpr ⟨hlt, hvx, hwx⟩,
      (mem_embeddedEdges ψ y _).mpr ⟨hlt, hvy, hwy⟩⟩
  · exact ⟨(w, v), (mem_embeddedEdges φ x _).mpr ⟨hlt, hwx, hvx⟩,
      (mem_embeddedEdges ψ y _).mpr ⟨hlt, hwy, hvy⟩⟩

/-- Local matchings in distinct allocation groups combine into one physical packing. -/
theorem taggedEmbeddedEdges_disjoint {I : Type*}
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (k : I → ℕ) (φ : ∀ i, Fin (k i) ↪o Fin ℓ)
    (X : Coordinate ℓ A → J) (label : I → J) (hlabel : Function.Injective label)
    (T : ∀ i, Finset (Fin (k i) → A))
    (hT : ∀ i, T i ⊆ assignments (thinned (G.comap (MultipartiteCounting.partVertexEmbedding (φ i).toEmbedding))
      (fun v => CategoricalSampling.projection (label i) X (profileCoordinateEmbedding (φ i).toEmbedding v))))
    (hdisjoint : ∀ i, (T i : Set (Fin (k i) → A)).PairwiseDisjoint edges)
    (a b : (i : I) × T i) (hab : a ≠ b) :
    Disjoint (embeddedEdges (φ a.1) a.2.val) (embeddedEdges (φ b.1) b.2.val) := by
  classical
  rcases a with ⟨i, x, hx⟩
  rcases b with ⟨j, y, hy⟩
  by_cases hij : i = j
  · subst j
    apply embeddedEdges_disjoint
    apply hdisjoint i hx hy
    intro hxy
    subst y
    exact hab rfl
  · exact embeddedEdges_disjoint_of_label_ne G (φ i) (φ j) X (label i) (label j)
      (hlabel.ne hij) x y (hT i hx) (hT j hy)

/-- The combined local matchings give an actual integer bound after any ambient embedding. -/
theorem cliquePartitionNumber_le_embedded_matchings {I : Type*} [Fintype I] {n : ℕ}
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin n)) (f : (Fin ℓ × A) ↪ Fin n)
    (hf : ∀ v w, G.Adj v w → H.Adj (f v) (f w))
    (k : I → ℕ) (hk : ∀ i, 2 ≤ k i) (φ : ∀ i, Fin (k i) ↪o Fin ℓ)
    (X : Coordinate ℓ A → J) (label : I → J) (hlabel : Function.Injective label)
    (T : ∀ i, Finset (Fin (k i) → A))
    (hT : ∀ i, T i ⊆ assignments (thinned (G.comap (MultipartiteCounting.partVertexEmbedding (φ i).toEmbedding))
      (fun v => CategoricalSampling.projection (label i) X (profileCoordinateEmbedding (φ i).toEmbedding v))))
    (hdisjoint : ∀ i, (T i : Set (Fin (k i) → A)).PairwiseDisjoint edges) :
    (cliquePartitionNumber H : ℝ) ≤ (H.edgeSet.ncard : ℝ) -
      ∑ i, (T i).card * (((k i).choose 2 : ℝ) - 1) := by
  classical
  let S (a : (i : I) × T i) := (embeddedVertices (φ a.1) a.2.val).map f
  have hsize (a : (i : I) × T i) : 2 ≤ (S a).card := by
    simpa only [S, Finset.card_map, embeddedVertices_card] using hk a.1
  have hclique (a : (i : I) × T i) : H.IsClique (S a : Set (Fin n)) := by
    intro v hv w hw hvw
    obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hw
    apply hf
    exact embeddedVertices_selected_isClique G (φ a.1) X (label a.1) a.2.val (hT a.1 a.2.property)
      hv' hw' (fun h => hvw (congrArg f h))
  have hedge (a b : (i : I) × T i) (u v : Fin n) (huv : u ≠ v)
      (hua : u ∈ S a) (hva : v ∈ S a) (hub : u ∈ S b) (hvb : v ∈ S b) : a = b := by
    by_contra hab
    obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hua
    obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hva
    have hub' : u' ∈ embeddedVertices (φ b.1) b.2.val := by simpa only [S, Finset.mem_map, f.injective.eq_iff, exists_eq_right] using hub
    have hvb' : v' ∈ embeddedVertices (φ b.1) b.2.val := by simpa only [S, Finset.mem_map, f.injective.eq_iff, exists_eq_right] using hvb
    obtain ⟨c, hca, hcb⟩ := embeddedEdges_common (φ a.1) (φ b.1) a.2.val b.2.val
      (fun h => huv (congrArg f h)) hu' hv' hub' hvb'
    exact Finset.disjoint_left.mp (taggedEmbeddedEdges_disjoint G k φ X label hlabel T hT hdisjoint a b hab) hca hcb
  have h := cliquePartitionNumber_le_indexed_savings H S hsize hclique hedge
  simp only [S, Finset.card_map, embeddedVertices_card, Fintype.sum_sigma,
    Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at h
  exact h

end Erdos1017.TransversalClique
