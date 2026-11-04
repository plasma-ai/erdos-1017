module

public import Erdos1017.IntegerTransfer.MultipartiteTypicalExtensions

/-!
# Regularity under role relabeling

Pulling a graph back along a vertex equivalence preserves rectangle densities
and regularity with no change in `ε`, and the role equivalence `roleEquiv`
relabels parts so that all-pairs regularity and positive density floors survive
arbitrary role permutations (`role_regular`, `role_density`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.GraphRelabel

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
/-- Pulling a graph back along a vertex equivalence preserves every finite
rectangle density after mapping its two endpoint sets. -/
theorem edgeDensity_comap (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : V ≃ W) (s t : Finset V) :
    (G.comap e).edgeDensity s t = G.edgeDensity (s.map e.toEmbedding) (t.map e.toEmbedding) := by
  have hinter : ((G.comap e).interedges s t).map (e.toEmbedding.prodMap e.toEmbedding) =
      G.interedges (s.map e.toEmbedding) (t.map e.toEmbedding) := by
    ext v
    simp only [Finset.mem_map, SimpleGraph.mem_interedges_iff, SimpleGraph.comap_adj]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hab⟩
    · rintro ⟨⟨a, ha, hleft⟩, ⟨b, hb, hright⟩, hab⟩
      refine ⟨(a, b), ⟨ha, hb, ?_⟩, ?_⟩
      · change e a = v.1 at hleft
        change e b = v.2 at hright
        rw [hleft, hright]
        exact hab
      · exact Prod.ext hleft hright
  have hcard := congrArg Finset.card hinter
  simp only [Finset.card_map, SimpleGraph.interedges] at hcard
  simp only [SimpleGraph.edgeDensity, Rel.edgeDensity, hcard, Finset.card_map]

omit [DecidableEq V] [DecidableEq W] in
/-- Regularity transports along the same equivalence, with no change in ε. -/
theorem isUniform_comap (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : V ≃ W) (s t : Finset V) (ε : ℝ)
    (h : G.IsUniform ε (s.map e.toEmbedding) (t.map e.toEmbedding)) :
    (G.comap e).IsUniform ε s t := by
  intro s' hs t' ht hs' ht'
  have hreg := h (Finset.map_subset_map.mpr hs) (Finset.map_subset_map.mpr ht)
    (by simpa only [Finset.card_map] using hs') (by simpa only [Finset.card_map] using ht')
  simpa only [edgeDensity_comap] using hreg

end Erdos1017.GraphRelabel

namespace Erdos1017.MultipartiteCounting

variable {A : Type*} [Fintype A] [DecidableEq A] {k : ℕ}

/-- Relabel roles without changing the vertices inside each part. -/
def roleEquiv (σ : Equiv.Perm (Fin k)) : (Fin k × A) ≃ (Fin k × A) :=
  Equiv.prodCongr σ (Equiv.refl A)

omit [Fintype A] [DecidableEq A] in
/-- The identity role permutation is the identity vertex equivalence. -/
theorem roleEquiv_refl : roleEquiv (A := A) (Equiv.refl (Fin k)) = Equiv.refl (Fin k × A) := by
  ext v <;> rfl

omit [DecidableEq A] in
/-- The role equivalence sends a labelled part to the corresponding original part. -/
theorem part_map_roleEquiv (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    (part (A := A) i).map (roleEquiv σ).toEmbedding = part (σ i) := by
  ext ⟨j, a⟩
  simp [part, roleEquiv, Equiv.eq_symm_apply]

omit [DecidableEq A] in
/-- All-pairs regularity survives arbitrary role permutations, including pairs
whose order is reversed by the permutation. -/
theorem role_regular (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin k)) (ε : ℝ)
    (h : ∀ i j : Fin k, i < j → G.IsUniform ε (part i) (part j))
    (i j : Fin k) (hij : i < j) :
    (G.comap (roleEquiv σ)).IsUniform ε (part i) (part j) := by
  apply GraphRelabel.isUniform_comap
  rw [part_map_roleEquiv, part_map_roleEquiv]
  rcases lt_or_gt_of_ne (σ.injective.ne hij.ne) with hlt | hgt
  · exact h _ _ hlt
  · exact (h _ _ hgt).symm

omit [DecidableEq A] in
/-- Positive pair density floors survive the same role permutation. -/
theorem role_density (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin k)) (δ : ℝ)
    (h : ∀ i j : Fin k, i < j → δ ≤ G.edgeDensity (part i) (part j))
    (i j : Fin k) (hij : i < j) :
    δ ≤ (G.comap (roleEquiv σ)).edgeDensity (part i) (part j) := by
  rw [GraphRelabel.edgeDensity_comap, part_map_roleEquiv, part_map_roleEquiv]
  rcases lt_or_gt_of_ne (σ.injective.ne hij.ne) with hlt | hgt
  · exact h _ _ hlt
  · rw [SimpleGraph.edgeDensity_comm]
    exact h _ _ hgt

end Erdos1017.MultipartiteCounting
