module

public import Erdos1017.IntegerTransfer.ThinningRoleTransport
public import Erdos1017.IntegerTransfer.TransversalBaseDegree

/-!
# Role relabeling of the transversal clique hypergraph

Relabeling roles transports realizing assignments, edges and the clique
hypergraph along the induced coordinate equivalence, and degree transport
identifies every role-pair degree with a first-two-role extension count.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

variable {k : ℕ} {A : Type*}

/-- Role-coordinate relabeling preserves increasing orientation. -/
theorem roleCoordinate_lt_iff (σ : Equiv.Perm (Fin k)) (v : Coordinate k A) :
    (roleCoordinate σ v).1.1 < (roleCoordinate σ v).2.1 ↔ v.1.1 < v.2.1 := by
  rcases v with ⟨⟨i, a⟩, ⟨j, b⟩⟩
  by_cases hij : i < j
  · by_cases hσ : σ i < σ j
    · simp [roleCoordinate, hij, hσ]
    · have hσ' : σ j < σ i := lt_of_le_of_ne (le_of_not_gt hσ) (σ.injective.ne hij.ne).symm
      simp [roleCoordinate, hij, hσ, hσ']
  · by_cases hσ : σ i < σ j
    · simp [roleCoordinate, hij, hσ, not_lt_of_ge hσ.le]
    · simp [roleCoordinate, hij, hσ]

end Erdos1017.TransversalThinning

namespace Erdos1017.TransversalClique

open TransversalThinning

variable {k : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
/-- The complete-clique condition can use all distinct roles rather than only
increasing pairs, because graph adjacency is symmetric. -/
theorem mem_assignments_distinct (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (X : Fin k → A) : X ∈ assignments G ↔
      ∀ i j : Fin k, i ≠ j → G.Adj (i, X i) (j, X j) := by
  rw [mem_assignments_iff]
  constructor
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact h i j hij
    · exact (h j i hji).symm
  · intro h i j hij
    exact h i j hij.ne

omit [DecidableEq A] in
/-- Relabeling the roles transports actual realizing assignments. -/
theorem assignments_role_iff (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin k)) (X : Fin k → A) :
    X ∈ assignments (G.comap (MultipartiteCounting.roleEquiv σ)) ↔
      (fun i => X (σ.symm i)) ∈ assignments G := by
  rw [mem_assignments_distinct, mem_assignments_distinct]
  constructor
  · intro h i j hij
    have h' := h (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij)
    simpa only [SimpleGraph.comap_adj, MultipartiteCounting.roleEquiv, Equiv.prodCongr_apply,
      Equiv.refl_apply, Equiv.apply_symm_apply, Prod.map_apply] using h'
  · intro h i j hij
    have h' := h (σ i) (σ j) (σ.injective.ne hij)
    simpa only [SimpleGraph.comap_adj, MultipartiteCounting.roleEquiv, Equiv.prodCongr_apply,
      Equiv.refl_apply, Equiv.symm_apply_apply, Prod.map_apply] using h'

omit [Fintype A] in
/-- The sampled coordinate equivalence relabels every actual edge of a transversal. -/
theorem edges_role_map (σ : Equiv.Perm (Fin k)) (X : Fin k → A) :
    (edges X).map (roleCoordinateEquiv σ).toEmbedding = edges (fun i => X (σ.symm i)) := by
  have hmem (v : Coordinate k A) : v ∈ edges X ↔
      roleCoordinateEquiv σ v ∈ edges (fun i => X (σ.symm i)) := by
    rw [mem_edges_iff, mem_edges_iff]
    simp only [roleCoordinateEquiv, Equiv.coe_fn_mk]
    have hlt := roleCoordinate_lt_iff σ v
    by_cases hv : v.1.1 < v.2.1
    · rw [roleCoordinate_of_lt σ v hv] at hlt ⊢
      split_ifs <;> simp_all [Equiv.symm_apply_apply, and_comm]
    · have hnot : ¬(roleCoordinate σ v).1.1 < (roleCoordinate σ v).2.1 := mt hlt.mp hv
      simp only [hv, hnot, false_and]
  ext w
  obtain ⟨v, rfl⟩ := (roleCoordinateEquiv (A := A) σ).surjective w
  simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hmem v

/-- The actual clique hypergraph transports along the same coordinate equivalence. -/
theorem hypergraph_role (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin k)) :
    HypergraphNibble.relabel (roleCoordinateEquiv σ)
      (hypergraph (G.comap (MultipartiteCounting.roleEquiv σ))) = hypergraph G := by
  ext e
  simp only [HypergraphNibble.relabel, hypergraph, Finset.mem_image]
  constructor
  · rintro ⟨a, ⟨X, hX, rfl⟩, rfl⟩
    rw [edges_role_map]
    exact ⟨_, (assignments_role_iff G σ X).mp hX, rfl⟩
  · rintro ⟨Y, hY, rfl⟩
    let X : Fin k → A := fun i => Y (σ i)
    have hX : X ∈ assignments (G.comap (MultipartiteCounting.roleEquiv σ)) := by
      rw [assignments_role_iff]
      simpa only [X, Equiv.apply_symm_apply] using hY
    refine ⟨edges X, ⟨X, hX, rfl⟩, ?_⟩
    rw [edges_role_map]
    simp only [X, Equiv.apply_symm_apply]

/-- Degree transport identifies every role-pair degree with its relabelled
first-two-role extension count. -/
theorem degree_role (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin k)) (v : Coordinate k A) :
    HypergraphNibble.degree (hypergraph (G.comap (MultipartiteCounting.roleEquiv σ))) v =
      HypergraphNibble.degree (hypergraph G) (roleCoordinateEquiv σ v) := by
  rw [← hypergraph_role G σ, HypergraphNibble.degree_relabel]

end Erdos1017.TransversalClique
