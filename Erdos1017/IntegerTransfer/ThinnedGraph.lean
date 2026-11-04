module

public import Erdos1017.IntegerTransfer.TransversalThinning

/-!
# The thinned subgraph of a multipartite graph

This module defines the `thinned` subgraph obtained by independently retaining
inter-part edges, each indexed by its increasing-label coordinate, and the
base-retention event, and shows that conditional on retaining the base the
surviving extensions are exactly those whose non-base required edges were
sampled (`extensions_thinned`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A] {t u k : ℕ}

/-- The actual subgraph obtained by independently retaining inter-part edges.
Each unordered inter-part edge uses its increasing-label coordinate. -/
def thinned (G : SimpleGraph (Fin k × A)) (X : Coordinate k A → Bool) :
    SimpleGraph (Fin k × A) where
  Adj v w := G.Adj v w ∧
    ((v.1 < w.1 ∧ X (v, w) = true) ∨ (w.1 < v.1 ∧ X (w, v) = true))
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := G.irrefl h.1

instance (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj] (X : Coordinate k A → Bool) :
    DecidableRel (thinned G X).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

omit [Fintype A] [DecidableEq A] in
theorem thinned_le (G : SimpleGraph (Fin k × A)) (X : Coordinate k A → Bool) : thinned G X ≤ G :=
  fun _ _ h => h.1

omit [Fintype A] [DecidableEq A] in
theorem thinned_adj_iff (G : SimpleGraph (Fin k × A)) (X : Coordinate k A → Bool)
    {i j : Fin k} (hij : i < j) (a b : A) :
    (thinned G X).Adj (i, a) (j, b) ↔ G.Adj (i, a) (j, b) ∧ X ((i, a), (j, b)) = true := by
  simp only [thinned, hij, (not_lt_of_ge hij.le), true_and, false_and, or_false]

/-- Actual extensions in the original graph. -/
def extensions (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (x : Fin t → A) : Finset (Fin u → A) :=
  Finset.univ.filter (MultipartiteExtension.extensionRelation G x)

/-- The sampled base clique event, using exactly the base-edge coordinates. -/
def BaseRetained (x : Fin t → A) (X : Coordinate (t + u) A → Bool) : Prop :=
  ∀ i j : Fin t, i < j → X ((Fin.castAdd u i, x i), (Fin.castAdd u j, x j)) = true

instance (x : Fin t → A) (X : Coordinate (t + u) A → Bool) : Decidable (BaseRetained x X) :=
  inferInstanceAs (Decidable (∀ i j : Fin t, i < j → _))

/-- Conditional on retaining the base, surviving extension assignments are
exactly those whose non-base required edges were sampled. -/
theorem extensions_thinned (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (x : Fin t → A) (X : Coordinate (t + u) A → Bool) (hbase : BaseRetained x X) :
    extensions (thinned G X) x = BernoulliFamily.retained (extensions G x) (support x) X := by
  ext y
  simp only [extensions, BernoulliFamily.retained, Finset.mem_filter, Finset.mem_univ,
    true_and, MultipartiteExtension.extensionRelation, MultipartiteExtension.Realizes]
  constructor
  · intro h
    refine ⟨fun i j hij => (h i j hij).1, ?_⟩
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    have hij := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    exact ((thinned_adj_iff G X hij _ _).mp (h e.1 e.2 hij)).2
  · rintro ⟨hG, hX⟩ i j hij
    apply (thinned_adj_iff G X hij _ _).mpr
    refine ⟨hG i j hij, ?_⟩
    by_cases hj : j.val < t
    · have hi : i.val < t := by omega
      let a : Fin t := ⟨i.val, hi⟩
      let b : Fin t := ⟨j.val, hj⟩
      have ha : Fin.castAdd u a = i := by rfl
      have hb : Fin.castAdd u b = j := by rfl
      have hab : a < b := hij
      have h := hbase a b hab
      simpa only [← ha, ← hb, Fin.addCases_left] using h
    · apply hX
      apply Finset.mem_image.mpr
      refine ⟨(i, j), ?_, rfl⟩
      simp only [SharedBasePattern.extensionEdges, MultipartiteExtension.completeEdges,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hij, by omega⟩

omit [DecidableEq A] in
/-- Extension counts use the same actual finite set as the counting/concentration chain. -/
theorem extensions_card (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (x : Fin t → A) :
    ((extensions G x).card : ℝ) = CliqueExtension.count (MultipartiteExtension.extensionRelation G) x := by
  rfl

end Erdos1017.TransversalThinning
