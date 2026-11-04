module

public import Erdos1017.IntegerTransfer.AllocationResidualCost

/-!
# Expected number of residual allocated edges

The expected number of residual allocated edges is exactly the pair mass of the
unselected profile layers, derived from the fractional edge loads
(`residualAllocatedEdges_expectation`), and splitting every profile into `C`
layers preserves its total pair mass.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators

variable {ℓ C : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- Exact profile pair mass is the number of actual graph-edge coordinates. -/
theorem typeMass_pair_mass (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (w : Finset (Fin ℓ × A) → ℝ)
    (hsupport : ∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × A)))
    (hbalance : ∀ v z, G.Adj v z → pairLoad w v z = 1) :
    (∑ K, (K.card.choose 2 : ℝ) * typeMass w K) = (TransversalClique.graphEdges G).card := by
  have hpoint (K : Finset (Fin ℓ)) := sum_profile_pairs K (typeMass w K)
  simp_rw [← hpoint]
  rw [Finset.sum_comm, graphEdges_card]
  apply Finset.sum_congr rfl
  intro e he
  exact typeMass_pair_balance G hparts w hsupport hbalance e.1 e.2 (Finset.mem_filter.mp he).2.ne

/-- Splitting every profile into C layers preserves its exact total pair mass. -/
theorem sum_layer_pair_mass (mass : Finset (Fin ℓ) → ℝ) (hC : 0 < C) :
    (∑ s : Finset (Fin ℓ) × Fin C, (s.1.card.choose 2 : ℝ) * mass s.1 / C) =
      ∑ K, (K.card.choose 2 : ℝ) * mass K := by
  have hCp : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro K _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The residual first moment is exactly the pair mass of the unselected
profile layers, derived from the actual fractional edge loads. -/
theorem residualAllocatedEdges_expectation
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (w : Finset (Fin ℓ × A) → ℝ)
    (hsupport : ∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × A)))
    (hbalance : ∀ v z, G.Adj v z → pairLoad w v z = 1)
    (hC : 0 < C) (L : Finset (Finset (Fin ℓ) × Fin C)) :
    (∑ X, CategoricalSampling.weight (allocationProbability G (typeMass w) C) X *
      ((residualAllocatedEdges G X (fun i : L => some i.val)).card : ℝ)) =
      ∑ s : Finset (Fin ℓ) × Fin C,
        if s ∈ L then 0 else (s.1.card.choose 2 : ℝ) * typeMass w s.1 / C := by
  classical
  let q := allocationProbability G (typeMass w) C
  have htotal := CategoricalSampling.total q (typeMass_allocationProbability_total G hparts w hsupport hbalance C hC)
  have hinj : Function.Injective (fun i : L => (some i.val : AllocationLabel ℓ C)) := by
    intro i j h
    exact Subtype.ext (Option.some.inj h)
  have hdecomp (X : TransversalThinning.Coordinate ℓ A → AllocationLabel ℓ C) :=
    allocatedEdges_card_decomposition G X (fun i : L => some i.val) hinj
  have hmeans :
      (∑ X, CategoricalSampling.weight q X * ((residualAllocatedEdges G X (fun i : L => some i.val)).card : ℝ)) +
        (∑ i : L, (i.val.1.card.choose 2 : ℝ) * typeMass w i.val.1 / C) =
          (TransversalClique.graphEdges G).card := by
    have h := congrArg (fun f => ∑ X, CategoricalSampling.weight q X * f X) (funext hdecomp)
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_mul, htotal, one_mul] at h
    rw [Finset.sum_comm] at h
    simpa only [q, allocated_profile_expectation G hparts w hsupport hbalance C hC] using h
  have hsplit :
      (∑ s : Finset (Fin ℓ) × Fin C, if s ∈ L then 0 else (s.1.card.choose 2 : ℝ) * typeMass w s.1 / C) +
        (∑ i : L, (i.val.1.card.choose 2 : ℝ) * typeMass w i.val.1 / C) =
          (TransversalClique.graphEdges G).card := by
    rw [Finset.sum_coe_sort L (fun s => (s.1.card.choose 2 : ℝ) * typeMass w s.1 / C)]
    have hLsum : (∑ s ∈ L, (s.1.card.choose 2 : ℝ) * typeMass w s.1 / C) =
        ∑ s : Finset (Fin ℓ) × Fin C, if s ∈ L then (s.1.card.choose 2 : ℝ) * typeMass w s.1 / C else 0 := by
      simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hLsum, ← Finset.sum_add_distrib]
    have hpoint (s : Finset (Fin ℓ) × Fin C) :
        (if s ∈ L then 0 else (s.1.card.choose 2 : ℝ) * typeMass w s.1 / C) +
          (if s ∈ L then (s.1.card.choose 2 : ℝ) * typeMass w s.1 / C else 0) =
            (s.1.card.choose 2 : ℝ) * typeMass w s.1 / C := by split_ifs <;> simp
    simp only [hpoint]
    rw [sum_layer_pair_mass (typeMass w) hC, typeMass_pair_mass G hparts w hsupport hbalance]
  linarith only [hmeans, hsplit]

end Erdos1017.MultipartiteAllocation
