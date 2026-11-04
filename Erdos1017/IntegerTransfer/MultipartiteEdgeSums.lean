module

public import Erdos1017.IntegerTransfer.MultipartiteProfileGraphs

/-!
# Splitting edge sums by part pairs

This module separates part labels from within-part endpoint values
(`coordinatePairEquiv`), so that finite coordinate sums and weighted graph-edge
sums decompose exactly into their part-pair fibers and the inter-part edge count
is the sum of pair-edge counts (`graphEdges_card`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators

variable {ℓ : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- Separate part labels from within-part endpoint values. -/
def coordinatePairEquiv : TransversalThinning.Coordinate ℓ A ≃ (Fin ℓ × Fin ℓ) × (A × A) where
  toFun v := ((v.1.1, v.2.1), (v.1.2, v.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv := by rintro ⟨⟨i, a⟩, ⟨j, b⟩⟩; rfl
  right_inv := by rintro ⟨⟨i, j⟩, ⟨a, b⟩⟩; rfl

omit [DecidableEq A] in
/-- Arbitrary finite coordinate sums split by their actual role pairs. -/
theorem sum_coordinates (f : TransversalThinning.Coordinate ℓ A → ℝ) :
    (∑ v, f v) = ∑ e : Fin ℓ × Fin ℓ, ∑ p : A × A, f ((e.1, p.1), (e.2, p.2)) := by
  have h := Fintype.sum_equiv (coordinatePairEquiv (ℓ := ℓ) (A := A)) f
    (fun p => f ((p.1.1, p.2.1), (p.1.2, p.2.2))) (fun v => rfl)
  rw [h, Fintype.sum_prod_type]

omit [DecidableEq A] in
/-- Weighted actual graph edges decompose exactly into their part-pair fibres. -/
theorem sum_graphEdges (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (f : TransversalThinning.Coordinate ℓ A → ℝ) :
    (∑ v ∈ TransversalClique.graphEdges G, f v) =
      ∑ e ∈ MultipartiteExtension.completeEdges ℓ, ∑ p : A × A,
        if G.Adj (e.1, p.1) (e.2, p.2) then f ((e.1, p.1), (e.2, p.2)) else 0 := by
  simp only [TransversalClique.graphEdges, Finset.sum_filter]
  rw [sum_coordinates]
  simp only [MultipartiteExtension.completeEdges, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e.1 < e.2
  · simp only [he, true_and, ite_true]
  · simp only [he, false_and, ite_false, Finset.sum_const_zero]

omit [DecidableEq A] in
/-- The actual inter-part graph-edge count is the sum of actual pair-edge counts. -/
theorem graphEdges_card (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj] :
    ((TransversalClique.graphEdges G).card : ℝ) =
      ∑ e ∈ MultipartiteExtension.completeEdges ℓ, (pairEdgeCount G e.1 e.2 : ℝ) := by
  have h := sum_graphEdges G (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro e _
  rw [pairEdgeCount, Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

omit [DecidableEq A] in
/-- Per-pair upper bounds give the corresponding total edge-count upper bound. -/
theorem graphEdges_card_le (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (D : ℝ) (hD : ∀ i j : Fin ℓ, i < j → (pairEdgeCount G i j : ℝ) ≤ D) :
    ((TransversalClique.graphEdges G).card : ℝ) ≤ ℓ.choose 2 * D := by
  rw [graphEdges_card]
  calc
    _ ≤ ∑ _ ∈ MultipartiteExtension.completeEdges ℓ, D := Finset.sum_le_sum (fun e he => hD _ _ (Finset.mem_filter.mp he).2)
    _ = _ := by simp only [Finset.sum_const, TransversalClique.completeEdges_card, nsmul_eq_mul]

end Erdos1017.MultipartiteAllocation
