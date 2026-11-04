module

public import Erdos1017.IntegerTransfer.MultipartiteProfileGraphs
public import Erdos1017.IntegerTransfer.TransversalCliqueEdges

/-!
# Ambient vertices and edges of an embedded transversal

This module defines the ambient vertices and edge coordinates of a transversal
embedded in selected ordered parts, with their cardinalities, and shows that a
realizing local assignment is a clique in the ambient graph
(`embeddedVertices_isClique`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

open TransversalThinning MultipartiteAllocation

variable {k ℓ : ℕ} {A : Type*} [DecidableEq A]

/-- The actual ambient vertices of a transversal in selected ordered parts. -/
def embeddedVertices (φ : Fin k ↪o Fin ℓ) (x : Fin k → A) : Finset (Fin ℓ × A) :=
  (vertices x).map (MultipartiteCounting.partVertexEmbedding φ.toEmbedding)

/-- The actual ambient edge coordinates of an embedded transversal. -/
def embeddedEdges (φ : Fin k ↪o Fin ℓ) (x : Fin k → A) : Finset (Coordinate ℓ A) :=
  (edges x).map (profileCoordinateEmbedding φ.toEmbedding)

theorem embeddedVertices_card (φ : Fin k ↪o Fin ℓ) (x : Fin k → A) :
    (embeddedVertices φ x).card = k := by
  rw [embeddedVertices, Finset.card_map, vertices_card]

theorem embeddedEdges_card (φ : Fin k ↪o Fin ℓ) (x : Fin k → A) :
    (embeddedEdges φ x).card = k.choose 2 := by
  rw [embeddedEdges, Finset.card_map, edges_card]

theorem mem_embeddedVertices (φ : Fin k ↪o Fin ℓ) (x : Fin k → A) (v : Fin ℓ × A) :
    v ∈ embeddedVertices φ x ↔ ∃ i, (φ i, x i) = v := by
  simp only [embeddedVertices, vertices, Finset.mem_map, Finset.mem_image, Finset.mem_univ,
    true_and, exists_exists_eq_and]
  rfl

/-- An embedded edge is precisely an increasing-role pair of its actual vertices. -/
theorem mem_embeddedEdges (φ : Fin k ↪o Fin ℓ) (x : Fin k → A) (v : Coordinate ℓ A) :
    v ∈ embeddedEdges φ x ↔ v.1.1 < v.2.1 ∧
      v.1 ∈ embeddedVertices φ x ∧ v.2 ∈ embeddedVertices φ x := by
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨hij, ha, hb⟩ := (mem_edges_iff x w).mp hw
    refine ⟨φ.strictMono hij, (mem_embeddedVertices φ x _).mpr ?_, (mem_embeddedVertices φ x _).mpr ?_⟩
    · exact ⟨w.1.1, Prod.ext rfl ha⟩
    · exact ⟨w.2.1, Prod.ext rfl hb⟩
  · rintro ⟨hlt, ha, hb⟩
    obtain ⟨i, hi⟩ := (mem_embeddedVertices φ x _).mp ha
    obtain ⟨j, hj⟩ := (mem_embeddedVertices φ x _).mp hb
    have hij : i < j := φ.lt_iff_lt.mp (by simpa only [← hi, ← hj] using hlt)
    refine Finset.mem_map.mpr ⟨((i, x i), (j, x j)), (mem_edges_iff x _).mpr ⟨hij, rfl, rfl⟩, ?_⟩
    exact Prod.ext hi hj

/-- Distinct vertices of an embedded transversal use distinct ambient parts. -/
theorem embeddedVertices_role_ne (φ : Fin k ↪o Fin ℓ) (x : Fin k → A)
    {v w : Fin ℓ × A} (hv : v ∈ embeddedVertices φ x) (hw : w ∈ embeddedVertices φ x)
    (hvw : v ≠ w) : v.1 ≠ w.1 := by
  obtain ⟨i, rfl⟩ := (mem_embeddedVertices φ x _).mp hv
  obtain ⟨j, rfl⟩ := (mem_embeddedVertices φ x _).mp hw
  intro h
  exact hvw (by rw [φ.injective h])

theorem embeddedVertices_injective (φ : Fin k ↪o Fin ℓ) :
    Function.Injective (embeddedVertices (A := A) φ) := by
  intro x y h
  funext i
  have hi : (φ i, x i) ∈ embeddedVertices φ y := by
    rw [← h]
    exact (mem_embeddedVertices φ x _).mpr ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := (mem_embeddedVertices φ y _).mp hi
  have hij : j = i := φ.injective (congrArg Prod.fst hj)
  simpa only [hij] using (congrArg Prod.snd hj).symm

variable [Fintype A]

/-- A realizing local assignment is an actual clique in the ambient graph. -/
theorem embeddedVertices_isClique (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (φ : Fin k ↪o Fin ℓ) (x : Fin k → A)
    (hx : x ∈ assignments (G.comap (MultipartiteCounting.partVertexEmbedding φ.toEmbedding))) :
    G.IsClique (embeddedVertices φ x : Set (Fin ℓ × A)) := by
  intro v hv w hw hvw
  obtain ⟨i, rfl⟩ := (mem_embeddedVertices φ x _).mp hv
  obtain ⟨j, rfl⟩ := (mem_embeddedVertices φ x _).mp hw
  exact vertices_isClique _ x hx
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    (fun h => hvw (congrArg (MultipartiteCounting.partVertexEmbedding φ.toEmbedding) h))

end Erdos1017.TransversalClique
