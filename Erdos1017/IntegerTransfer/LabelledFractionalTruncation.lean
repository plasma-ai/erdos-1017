module

public import Erdos1017.IntegerTransfer.MultipartiteTypeMass
public import Erdos1017.IntegerTransfer.FractionalCliqueTruncation
public import Erdos1017.FractionalLimit.FractionalGraphEmbedding

/-!
# Bounded clique weights on labeled vertices

Relabeling subset weights preserves the fractional objective and every pair
load, and the attained finite linear program together with uniform truncation
gives bounded clique weights on labeled product vertices with exact edge loads
(`exists_uniform_bounded_labelled_partition`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators

variable {ℓ n N : ℕ}

/-- Relabeling an actual subset weight preserves the exact fractional objective. -/
theorem sum_subsetWeights_equiv {V : Type*} [Fintype V]
    (e : V ≃ Fin N) (w : Finset (Fin N) → ℝ) :
    (∑ S : Finset V, w (S.map e.toEmbedding)) = ∑ S, w S := by
  classical
  exact Fintype.sum_equiv (Equiv.finsetCongr e) _ _ (fun _ => rfl)

/-- Relabeling actual subset weights preserves the load on each actual pair. -/
theorem pairLoad_subsetWeights_equiv (e : (Fin ℓ × Fin n) ≃ Fin N)
    (w : Finset (Fin N) → ℝ) (v z : Fin ℓ × Fin n) :
    pairLoad (fun S => w (S.map e.toEmbedding)) v z = FractionalGraph.pairLoad w (e v) (e z) := by
  classical
  unfold pairLoad FractionalGraph.pairLoad
  apply Fintype.sum_equiv (Equiv.finsetCongr e)
  intro S
  simp only [Equiv.finsetCongr_apply, Finset.mem_map, Equiv.toEmbedding_apply,
    e.injective.eq_iff, exists_eq_right]

/-- The attained finite LP and the uniform truncation theorem give actual
bounded clique weights on labelled product vertices, including exact edge loads.
The value is that of the same graph under any injective ambient embedding. -/
theorem exists_uniform_bounded_labelled_partition (τ : ℝ) (hτ : 0 < τ) :
    ∃ b : ℕ, 3 ≤ b ∧ ∀ ℓ n N : ℕ,
      ∀ (G : SimpleGraph (Fin ℓ × Fin n)) (f : (Fin ℓ × Fin n) ↪ Fin N),
        ∃ w : Finset (Fin ℓ × Fin n) → ℝ,
          (∀ S, 0 ≤ w S) ∧
          (∀ S, w S ≠ 0 → 2 ≤ S.card ∧ S.card ≤ b ∧ G.IsClique (S : Set (Fin ℓ × Fin n))) ∧
          (∀ v z, G.Adj v z → pairLoad w v z = 1) ∧
          (∑ S, w S) ≤ FractionalGraph.value (G.map f) + τ * (ℓ * n : ℕ) ^ 2 := by
  classical
  obtain ⟨r, hr, htrunc⟩ := FractionalGraph.exists_uniform_bounded_clique_partition τ hτ
  refine ⟨max 3 r, le_max_left _ _, ?_⟩
  intro ℓ n N G f
  let e := Fintype.equivFin (Fin ℓ × Fin n)
  let H := G.map e.toEmbedding
  obtain ⟨w, hw, hsupport, hcost⟩ := htrunc (Fintype.card (Fin ℓ × Fin n)) H
  let v (S : Finset (Fin ℓ × Fin n)) := w (S.map e.toEmbedding)
  have hclique (S : Finset (Fin ℓ × Fin n)) (hS : v S ≠ 0) : G.IsClique (S : Set (Fin ℓ × Fin n)) := by
    intro a ha z hz haz
    apply SimpleGraph.map_adj_apply.mp
    exact (hw.2.1 _ hS).2 (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
      (Finset.mem_map.mpr ⟨z, hz, rfl⟩) (e.injective.ne haz)
  let f' := e.symm.toEmbedding.trans f
  have hmap : H.map f' = G.map f := by
    dsimp only [H]
    rw [SimpleGraph.map_map]
    congr 1
    funext a
    exact congrArg f (e.symm_apply_apply a)
  have hvalue : FractionalGraph.value H = FractionalGraph.value (G.map f) := by
    rw [← FractionalGraph.value_map H f', hmap]
  refine ⟨v, (fun S => hw.1 _), ?_, ?_, ?_⟩
  · intro S hS
    have hsize := (hw.2.1 _ hS).1
    have hcap := hsupport _ hS
    simp only [Finset.card_map] at hsize hcap
    exact ⟨hsize, hcap.trans (le_max_right _ _), hclique S hS⟩
  · intro a z haz
    change pairLoad (fun S => w (S.map e.toEmbedding)) a z = 1
    rw [pairLoad_subsetWeights_equiv]
    exact hw.2.2 _ _ (SimpleGraph.map_adj_apply.mpr haz)
  · rw [sum_subsetWeights_equiv, ← hvalue]
    simpa only [Fintype.card_prod, Fintype.card_fin] using hcost

end Erdos1017.MultipartiteAllocation
