module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphMeanMatching

/-!
# Transporting a hypergraph to its active vertex set

Hyperedges supported on a vertex set `U` are regarded as a hypergraph on the
subtype `U` (`onVertices`), with degrees, codegrees and matchings transported
exactly between the two views.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Regard hyperedges supported on U as subsets of the finite vertex type U. -/
def onVertices (H : Finset (Finset V)) (U : Finset V) : Finset (Finset U) :=
  H.image (fun e => e.subtype (fun v => v ∈ U))

omit [Fintype V] in
/-- Forgetting subtype membership recovers every supported hyperedge exactly. -/
theorem onVertices_map (H : Finset (Finset V)) (U : Finset V)
    (hsupport : ∀ e ∈ H, e ⊆ U) :
    (onVertices H U).image (fun e => e.map (Function.Embedding.subtype (fun v => v ∈ U))) = H := by
  ext e
  simp only [onVertices, Finset.mem_image]
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    simpa only [Finset.subtype_map_of_mem (hsupport b hb)] using hb
  · intro he
    exact ⟨e.subtype _, ⟨e, he, rfl⟩, Finset.subtype_map_of_mem (hsupport e he)⟩

omit [Fintype V] in
/-- Taking a subtype is injective among edges already supported on U. -/
theorem onVertices_injOn (H : Finset (Finset V)) (U : Finset V)
    (hsupport : ∀ e ∈ H, e ⊆ U) :
    Set.InjOn (fun e : Finset V => e.subtype (fun v => v ∈ U)) H := by
  intro e he f hf h
  have hmap := congrArg (fun s => s.map (Function.Embedding.subtype (fun v => v ∈ U))) h
  simpa only [Finset.subtype_map_of_mem (hsupport e he), Finset.subtype_map_of_mem (hsupport f hf)] using hmap

omit [Fintype V] in
/-- Degree transport to the actual active vertex set. -/
theorem degree_onVertices (H : Finset (Finset V)) (U : Finset V)
    (hsupport : ∀ e ∈ H, e ⊆ U) (v : U) :
    degree (onVertices H U) v = degree H v := by
  have hfilter : (onVertices H U).filter (fun e => v ∈ e) =
      (H.filter (fun e => v.val ∈ e)).image (fun e => e.subtype (fun v => v ∈ U)) := by
    ext e
    simp only [onVertices, Finset.mem_filter, Finset.mem_image]
    aesop
  unfold degree
  rw [hfilter]
  apply Finset.card_image_of_injOn
  exact (onVertices_injOn H U hsupport).mono (Finset.filter_subset _ _)

omit [Fintype V] in
/-- Codegree transport to the actual active vertex set. -/
theorem codegree_onVertices (H : Finset (Finset V)) (U : Finset V)
    (hsupport : ∀ e ∈ H, e ⊆ U) (v w : U) :
    codegree (onVertices H U) v w = codegree H v w := by
  have hfilter : (onVertices H U).filter (fun e => v ∈ e ∧ w ∈ e) =
      (H.filter (fun e => v.val ∈ e ∧ w.val ∈ e)).image (fun e => e.subtype (fun v => v ∈ U)) := by
    ext e
    simp only [onVertices, Finset.mem_filter, Finset.mem_image]
    aesop
  unfold codegree
  rw [hfilter]
  apply Finset.card_image_of_injOn
  exact (onVertices_injOn H U hsupport).mono (Finset.filter_subset _ _)

omit [Fintype V] in
/-- Matchings on the active vertex type give the same actual edge family in V. -/
theorem matching_onVertices (H : Finset (Finset V)) (U : Finset V)
    (hsupport : ∀ e ∈ H, e ⊆ U)
    (M : Finset (Finset U)) (hM : M ⊆ onVertices H U)
    (hdisj : (M : Set (Finset U)).PairwiseDisjoint id) :
    ∃ P : Finset (Finset V), P ⊆ H ∧ (P : Set (Finset V)).PairwiseDisjoint id ∧ P.card = M.card := by
  let e := Function.Embedding.subtype (fun v => v ∈ U)
  refine ⟨M.image (fun s => s.map e), ?_, ?_, Finset.card_image_of_injective _ (Finset.map_injective e)⟩
  · have hsub : M.image (fun s => s.map e) ⊆
        (onVertices H U).image (fun s => s.map e) := Finset.image_subset_image hM
    exact hsub.trans (by rw [onVertices_map H U hsupport])
  · intro s hs t ht hst
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
    have hab : a ≠ b := fun h => hst (by rw [h])
    simpa only [Function.onFun, id_eq, Finset.disjoint_map] using hdisj ha hb hab

end Erdos1017.HypergraphNibble
