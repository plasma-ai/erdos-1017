module

public import Erdos1017.IntegerTransfer.MultipartiteEdgeSums

/-!
# Expected edge counts of a categorical allocation

This module defines `allocatedEdges`, the graph edges carrying one categorical
allocation label, and proves that every profile layer receives exactly its
required fractional number of edges in expectation, zero-mass profiles included
(`allocated_profile_expectation`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators

variable {ℓ C : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- Actual graph edges receiving one categorical allocation label. -/
def allocatedEdges {J : Type*} [DecidableEq J]
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (X : TransversalThinning.Coordinate ℓ A → J) (j : J) : Finset (TransversalThinning.Coordinate ℓ A) :=
  (TransversalClique.graphEdges G).filter (fun v => X v = j)

/-- Expected allocated cardinalities are computed from the exact single-label marginal. -/
theorem allocatedEdges_expectation {J : Type*} [Fintype J] [DecidableEq J]
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (q : TransversalThinning.Coordinate ℓ A → J → ℝ)
    (hq : ∀ v, ∑ j, q v j = 1) (j : J) :
    (∑ X, CategoricalSampling.weight q X * ((allocatedEdges G X j).card : ℝ)) =
      ∑ v ∈ TransversalClique.graphEdges G, q v j := by
  have hcard (X : TransversalThinning.Coordinate ℓ A → J) :
      ((allocatedEdges G X j).card : ℝ) =
        ∑ v ∈ TransversalClique.graphEdges G, if X v = j then (1 : ℝ) else 0 := by
    rw [Finset.card_eq_sum_ones]
    simp only [allocatedEdges, Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hfirst (v : TransversalThinning.Coordinate ℓ A) :
      (∑ X, CategoricalSampling.weight q X * (if X v = j then (1 : ℝ) else 0)) = q v j := by
    have h := CategoricalSampling.projection_expectation q hq j (fun B => Selector.bit (B v))
    rw [CliqueSampling.bernoulli_first_moment] at h
    simpa only [CategoricalSampling.projection, Selector.bit, decide_eq_true_eq] using h
  simp only [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun v _ => hfirst v)

omit [DecidableEq A] in
/-- Constant charge on a part pair is its actual graph-edge count times that charge. -/
theorem sum_pair_charge (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (i j : Fin ℓ) (z : ℝ) :
    (∑ p : A × A, if G.Adj (i, p.1) (j, p.2) then z else 0) = pairEdgeCount G i j * z := by
  rw [pairEdgeCount, Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]

/-- A role profile contains exactly choose(|K|,2) increasing role pairs. -/
theorem sum_profile_pairs (K : Finset (Fin ℓ)) (z : ℝ) :
    (∑ e ∈ MultipartiteExtension.completeEdges ℓ, if e.1 ∈ K ∧ e.2 ∈ K then z else 0) =
      K.card.choose 2 * z := by
  rw [← Finset.sum_filter]
  have heq : (MultipartiteExtension.completeEdges ℓ).filter (fun e => e.1 ∈ K ∧ e.2 ∈ K) =
      (K ×ˢ K).filter (fun e => e.1 < e.2) := by
    ext e
    simp only [MultipartiteExtension.completeEdges, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_product]
    tauto
  rw [heq, Finset.sum_const, Finset.card_product_filter_lt, nsmul_eq_mul]

/-- Every profile layer receives exactly its required fractional number of
edges in expectation, including zero-mass profiles. -/
theorem allocated_profile_expectation
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (w : Finset (Fin ℓ × A) → ℝ)
    (hsupport : ∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × A)))
    (hbalance : ∀ v z, G.Adj v z → pairLoad w v z = 1)
    (C : ℕ) (hC : 0 < C) (K : Finset (Fin ℓ)) (c : Fin C) :
    (∑ X, CategoricalSampling.weight (allocationProbability G (typeMass w) C) X *
      ((allocatedEdges G X (some (K, c))).card : ℝ)) =
      K.card.choose 2 * typeMass w K / C := by
  rw [allocatedEdges_expectation G _ (typeMass_allocationProbability_total G hparts w hsupport hbalance C hC), sum_graphEdges]
  have hCp : (0 : ℝ) < C := by exact_mod_cast hC
  have hinner (e : Fin ℓ × Fin ℓ) (he : e ∈ MultipartiteExtension.completeEdges ℓ) :
      (∑ p : A × A, if G.Adj (e.1, p.1) (e.2, p.2) then
        allocationProbability G (typeMass w) C ((e.1, p.1), (e.2, p.2)) (some (K, c)) else 0) =
      if e.1 ∈ K ∧ e.2 ∈ K then typeMass w K / C else 0 := by
    have hlt := (Finset.mem_filter.mp he).2
    by_cases hK : e.1 ∈ K ∧ e.2 ∈ K
    · by_cases hz : typeMass w K = 0
      · simp only [allocationProbability, hz, zero_div, ite_self, Finset.sum_const_zero]
      · have hpositive := typeMass_pair_positive G w hsupport K hz e.1 e.2 hK.1 hK.2 hlt.ne
        have hcount : (0 : ℝ) < pairEdgeCount G e.1 e.2 := by exact_mod_cast hpositive
        have hactive (p : A × A) : ActivePair G ((e.1, p.1), (e.2, p.2)) := ⟨hlt.ne, hpositive⟩
        simp only [allocationProbability, hactive, hK.1, hK.2, and_self, ite_true]
        rw [sum_pair_charge]
        field_simp
    · have hpoint (p : A × A) : allocationProbability G (typeMass w) C ((e.1, p.1), (e.2, p.2)) (some (K, c)) = 0 := by
        change (if ActivePair G ((e.1, p.1), (e.2, p.2)) ∧ e.1 ∈ K ∧ e.2 ∈ K then
          typeMass w K / ((C : ℝ) * pairEdgeCount G e.1 e.2) else 0) = 0
        exact ite_eq_right (fun h => hK h.2)
      simp only [hpoint, ite_self, Finset.sum_const_zero, ite_eq_right hK]
  rw [Finset.sum_congr rfl hinner, sum_profile_pairs]
  ring

end Erdos1017.MultipartiteAllocation
