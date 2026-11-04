module

public import Erdos1017.IntegerTransfer.AllocatedEdgeCounts
public import Erdos1017.IntegerTransfer.EmbeddedCliqueGeometry
public import Erdos1017.IntegerTransfer.MultipartiteProfileRegularity
public import Erdos1017.IntegerTransfer.ThinnedPairCounts

/-!
# Transport of allocated edges along a profile embedding

An ordered profile embedding identifies the local sampled graph edges with the
ambient graph edges assigned that profile-layer label
(`map_graphEdges_eq_allocated`), using the profile support supplied by positive
categorical weight.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open TransversalThinning TransversalClique

variable {ℓ k C : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
/-- An ordered profile embedding identifies its local sampled graph edges with
the actual ambient graph edges assigned that profile-layer label. -/
theorem map_graphEdges_eq_allocated
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (K : Finset (Fin ℓ)) (c : Fin C) (φ : Fin k ↪o Fin ℓ)
    (hφ : ∀ i ∈ K, ∃ j, φ j = i)
    (X : Coordinate ℓ A → AllocationLabel ℓ C)
    (hsupport : ∀ v ∈ allocatedEdges G X (some (K, c)), v.1.1 ∈ K ∧ v.2.1 ∈ K) :
    (graphEdges (thinned (G.comap (MultipartiteCounting.partVertexEmbedding φ.toEmbedding))
      (fun v => CategoricalSampling.projection (some (K, c)) X (profileCoordinateEmbedding φ.toEmbedding v)))).map
        (profileCoordinateEmbedding φ.toEmbedding) = allocatedEdges G X (some (K, c)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨hlt, hadj⟩ := (Finset.mem_filter.mp hw).2
    have h := (thinned_adj_iff _ _ hlt w.1.2 w.2.2).mp hadj
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, φ.strictMono hlt, h.1⟩
    · simpa only [CategoricalSampling.projection, decide_eq_true_eq] using h.2
  · intro hv
    obtain ⟨hi, hj⟩ := hsupport v hv
    obtain ⟨i, hi⟩ := hφ v.1.1 hi
    obtain ⟨j, hj⟩ := hφ v.2.1 hj
    obtain ⟨hG, hlabel⟩ := Finset.mem_filter.mp hv
    obtain ⟨hlt, hadj⟩ := (Finset.mem_filter.mp hG).2
    have hij : i < j := φ.lt_iff_lt.mp (by simpa only [hi, hj] using hlt)
    let w : Coordinate k A := ((i, v.1.2), (j, v.2.2))
    have heq : profileCoordinateEmbedding φ.toEmbedding w = v := Prod.ext (Prod.ext hi rfl) (Prod.ext hj rfl)
    refine Finset.mem_map.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, ?_⟩, heq⟩
    apply (thinned_adj_iff _ _ hij _ _).mpr
    constructor
    · change G.Adj (φ i, v.1.2) (φ j, v.2.2)
      simpa only [hi, hj] using hadj
    · change decide (X (profileCoordinateEmbedding φ.toEmbedding w) = some (K, c)) = true
      exact decide_eq_true (heq ▸ hlabel)

omit [DecidableEq A] in
/-- Positive categorical weight supplies the profile support used by the edge transport. -/
theorem allocatedEdges_roles
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (mass : Finset (Fin ℓ) → ℝ) (hmass : ∀ K, 0 ≤ mass K)
    (X : Coordinate ℓ A → AllocationLabel ℓ C)
    (hX : 0 < CategoricalSampling.weight (allocationProbability G mass C) X)
    (K : Finset (Fin ℓ)) (c : Fin C) (v : Coordinate ℓ A)
    (hv : v ∈ allocatedEdges G X (some (K, c))) : v.1.1 ∈ K ∧ v.2.1 ∈ K := by
  obtain ⟨hvG, hvlabel⟩ := Finset.mem_filter.mp hv
  obtain ⟨K', c', hlabel, hi, hj, _⟩ := actual_edge_assigned G hparts mass hmass C X hX v (Finset.mem_filter.mp hvG).2.2
  have h := Option.some.inj (hvlabel.symm.trans hlabel)
  have hK : K = K' := congrArg Prod.fst h
  simpa only [hK] using And.intro hi hj

/-- The fixed profile enumeration covers every role of the profile. -/
theorem profileRoleEmbedding_surjective (K : Finset (Fin ℓ)) (hK : 2 ≤ K.card)
    (i : Fin ℓ) (hi : i ∈ K) : ∃ j, profileRoleEmbedding K hK j = i := by
  change i ∈ Set.range (profileRoleEmbedding K hK)
  rw [show Set.range (profileRoleEmbedding K hK) = K from K.range_orderEmbOfFin (by omega)]
  exact hi

end Erdos1017.MultipartiteAllocation
