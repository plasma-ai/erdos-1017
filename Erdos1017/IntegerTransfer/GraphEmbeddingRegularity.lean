module

public import Erdos1017.IntegerTransfer.GraphRelabelRegularity
public import Mathlib.Data.Finset.Sort

/-!
# Regularity under vertex embeddings into ambient parts

Rectangle densities and regularity transport along an injective vertex map, so a
local labeled graph embedded in selected ambient parts (`partVertexEmbedding`)
keeps the original pair densities and uniformity (`part_regular_embedding`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.GraphEmbedding

variable {V W : Type*}

/-- Rectangle densities transport along an injective vertex map; surjectivity
onto the ambient graph is unnecessary for induced profile subgraphs. -/
theorem edgeDensity_comap (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : V ↪ W) (s t : Finset V) :
    (G.comap e).edgeDensity s t = G.edgeDensity (s.map e) (t.map e) := by
  have hinter : ((G.comap e).interedges s t).map (e.prodMap e) = G.interedges (s.map e) (t.map e) := by
    ext v
    simp only [Finset.mem_map, SimpleGraph.mem_interedges_iff, SimpleGraph.comap_adj]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hab⟩
    · rintro ⟨⟨a, ha, hleft⟩, ⟨b, hb, hright⟩, hab⟩
      refine ⟨(a, b), ⟨ha, hb, ?_⟩, ?_⟩
      · rw [hleft, hright]
        exact hab
      · exact Prod.ext hleft hright
  have hcard := congrArg Finset.card hinter
  simp only [Finset.card_map, SimpleGraph.interedges] at hcard
  simp only [SimpleGraph.edgeDensity, Rel.edgeDensity, hcard, Finset.card_map]

/-- Regularity of the mapped endpoint sets gives regularity in an induced profile graph. -/
theorem isUniform_comap (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : V ↪ W) (s t : Finset V) (ε : ℝ) (h : G.IsUniform ε (s.map e) (t.map e)) :
    (G.comap e).IsUniform ε s t := by
  intro s' hs t' ht hs' ht'
  have hreg := h (Finset.map_subset_map.mpr hs) (Finset.map_subset_map.mpr ht)
    (by simpa only [Finset.card_map] using hs') (by simpa only [Finset.card_map] using ht')
  simpa only [edgeDensity_comap] using hreg

end Erdos1017.GraphEmbedding

namespace Erdos1017.MultipartiteCounting

variable {k ℓ : ℕ} {A : Type*} [Fintype A]

/-- Embed a local labelled graph in the selected ambient parts. -/
def partVertexEmbedding (φ : Fin k ↪ Fin ℓ) : (Fin k × A) ↪ (Fin ℓ × A) :=
  φ.prodMap (Function.Embedding.refl A)

/-- A local labelled part maps onto the entire corresponding ambient part. -/
theorem part_map_embedding (φ : Fin k ↪ Fin ℓ) (i : Fin k) :
    (part (A := A) i).map (partVertexEmbedding φ) = part (φ i) := by
  rw [part, Finset.map_map]
  rfl

/-- Pair densities of a profile graph equal the original pair densities. -/
theorem part_density_embedding (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (φ : Fin k ↪ Fin ℓ) (i j : Fin k) :
    (G.comap (partVertexEmbedding φ)).edgeDensity (part i) (part j) = G.edgeDensity (part (φ i)) (part (φ j)) := by
  rw [GraphEmbedding.edgeDensity_comap, part_map_embedding, part_map_embedding]

/-- Uniformity transports to any selected family of ambient parts. -/
theorem part_regular_embedding (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (φ : Fin k ↪ Fin ℓ) (i j : Fin k) (ε : ℝ)
    (h : G.IsUniform ε (part (φ i)) (part (φ j))) :
    (G.comap (partVertexEmbedding φ)).IsUniform ε (part i) (part j) := by
  apply GraphEmbedding.isUniform_comap
  simpa only [part_map_embedding] using h

end Erdos1017.MultipartiteCounting
