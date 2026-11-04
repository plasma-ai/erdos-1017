module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNearPerfectMatching

/-!
# Near-perfect matching on arbitrary finite vertex types

Relabeling every hyperedge along a vertex equivalence preserves degrees and
codegrees, so the near-perfect matching theorem applies to arbitrary finite
vertex types with the same thresholds chosen before the vertex type and the
hypergraph (`near_perfect_matching_fintype`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Relabel every vertex of every hyperedge by the same equivalence. -/
def relabel (e : V ≃ W) (H : Finset (Finset V)) : Finset (Finset W) :=
  H.image (fun s => s.map e.toEmbedding)

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem relabel_injective (e : V ≃ W) : Function.Injective (fun s : Finset V => s.map e.toEmbedding) :=
  Finset.map_injective e.toEmbedding

omit [Fintype V] [Fintype W] in
theorem degree_relabel (e : V ≃ W) (H : Finset (Finset V)) (v : V) :
    degree (relabel e H) (e v) = degree H v := by
  have hfilter : (relabel e H).filter (fun s => e v ∈ s) =
      (H.filter (fun s => v ∈ s)).image (fun s => s.map e.toEmbedding) := by
    ext s
    simp only [relabel, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hv⟩
      exact ⟨a, ⟨ha, by simpa using hv⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hv⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, by simpa using hv⟩
  unfold degree
  rw [hfilter, Finset.card_image_of_injective _ (relabel_injective e)]

omit [Fintype V] [Fintype W] in
theorem codegree_relabel (e : V ≃ W) (H : Finset (Finset V)) (v w : V) :
    codegree (relabel e H) (e v) (e w) = codegree H v w := by
  have hfilter : (relabel e H).filter (fun s => e v ∈ s ∧ e w ∈ s) =
      (H.filter (fun s => v ∈ s ∧ w ∈ s)).image (fun s => s.map e.toEmbedding) := by
    ext s
    simp only [relabel, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hv, hw⟩
      exact ⟨a, ⟨ha, by simpa using hv, by simpa using hw⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hv, hw⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, by simpa using hv, by simpa using hw⟩
  unfold codegree
  rw [hfilter, Finset.card_image_of_injective _ (relabel_injective e)]

/-- The matching input applies to arbitrary finite vertex types, with the same
thresholds chosen before the vertex type and hypergraph. -/
theorem near_perfect_matching_fintype (r : ℕ) (C δ : ℝ)
    (hr : 2 ≤ r) (hC : 1 ≤ C) (hδ : 0 < δ) :
    ∃ γ D₀ : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < D₀ ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (W : Finset V) (D : ℝ),
        D₀ ≤ D → (∀ e ∈ H, e.card = r) →
        (∀ v, (degree H v : ℝ) ≤ C * D) →
        (∀ v w, v ≠ w → (codegree H v w : ℝ) ≤ γ * D) →
        (∀ v, v ∉ W → (1 - γ) * D ≤ (degree H v : ℝ) ∧ (degree H v : ℝ) ≤ (1 + γ) * D) →
        (W.card : ℝ) ≤ γ * Fintype.card V →
        ∃ M : Finset (Finset V), M ⊆ H ∧ (M : Set (Finset V)).PairwiseDisjoint id ∧
          (1 - δ) * Fintype.card V / r ≤ (M.card : ℝ) := by
  classical
  obtain ⟨γ, D₀, hγ, hγ1, hD₀, hmatch⟩ := near_perfect_matching_with_exceptions r C δ hr hC hδ
  refine ⟨γ, D₀, hγ, hγ1, hD₀, ?_⟩
  intro V _ _ H W D hD huniform hmax hcodegree hregular hW
  let e := Fintype.equivFin V
  obtain ⟨M, hM, hdisj, hcard⟩ := hmatch (Fintype.card V) (relabel e H) (W.map e.toEmbedding) D hD
    (by rintro s hs; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs; simpa using huniform a ha)
    (by intro v; obtain ⟨v, rfl⟩ := e.surjective v
        simpa only [degree_relabel] using hmax v)
    (by intro v w hvw
        obtain ⟨v, rfl⟩ := e.surjective v
        obtain ⟨w, rfl⟩ := e.surjective w
        simpa only [codegree_relabel] using hcodegree v w (fun h => hvw (by rw [h])))
    (by intro v hv
        obtain ⟨v, rfl⟩ := e.surjective v
        have hv' : v ∉ W := by simpa using hv
        simpa only [degree_relabel] using hregular v hv')
    (by simpa using hW)
  refine ⟨relabel e.symm M, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp (hM ha)
    subst a
    have heq : Finset.map e.symm.toEmbedding (Finset.map e.toEmbedding b) = b := by
      ext v
      simp
    rwa [heq]
  · intro s hs t ht hst
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
    have hab : a ≠ b := fun h => hst (by rw [h])
    have hd := hdisj ha hb hab
    simpa only [Function.onFun, id_eq, Finset.disjoint_map] using hd
  · simpa only [relabel, Finset.card_image_of_injective _ (relabel_injective e.symm)] using hcard

end Erdos1017.HypergraphNibble
