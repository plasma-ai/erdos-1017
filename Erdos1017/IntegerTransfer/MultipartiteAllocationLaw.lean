module

public import Erdos1017.IntegerTransfer.MultipartiteFractionalAllocation
public import Erdos1017.IntegerTransfer.CategoricalThinning

/-!
# The categorical allocation law from profile masses

This module defines the allocation labels (`C` mutually exclusive layers per
profile plus a dummy label) and the categorical law `allocationProbability`
derived from aggregate fractional profile masses, normalized by exact pair
balance; in a positive-weight outcome each graph edge is assigned to one profile
containing both roles with positive mass.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators

variable {ℓ C : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- Each profile receives C mutually exclusive allocation layers; a dummy label
handles coordinates that cannot represent inter-part graph edges. -/
abbrev AllocationLabel (ℓ C : ℕ) := Option (Finset (Fin ℓ) × Fin C)

/-- A coordinate has an active role pair exactly when the pair is distinct
and has an actual graph edge. -/
def ActivePair (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (v : TransversalThinning.Coordinate ℓ A) : Prop :=
  v.1.1 ≠ v.2.1 ∧ 0 < pairEdgeCount G v.1.1 v.2.1
deriving Decidable

/-- The categorical law derived from aggregate fractional profile masses. -/
def allocationProbability (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (mass : Finset (Fin ℓ) → ℝ) (C : ℕ) (v : TransversalThinning.Coordinate ℓ A) :
    AllocationLabel ℓ C → ℝ
  | none => if ActivePair G v then 0 else 1
  | some (K, _) => if ActivePair G v ∧ v.1.1 ∈ K ∧ v.2.1 ∈ K then
      mass K / ((C : ℝ) * pairEdgeCount G v.1.1 v.2.1) else 0

omit [DecidableEq A] in
/-- Actual aggregate masses give nonnegative probabilities on every coordinate. -/
theorem allocationProbability_nonneg (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (mass : Finset (Fin ℓ) → ℝ) (hmass : ∀ K, 0 ≤ mass K) (C : ℕ)
    (v : TransversalThinning.Coordinate ℓ A) (j : AllocationLabel ℓ C) :
    0 ≤ allocationProbability G mass C v j := by
  cases j with
  | none => simp only [allocationProbability]; split_ifs <;> norm_num
  | some j =>
    simp only [allocationProbability]
    split_ifs
    · exact div_nonneg (hmass _) (mul_nonneg (Nat.cast_nonneg C) (Nat.cast_nonneg _))
    · exact le_rfl

omit [DecidableEq A] in
/-- Exact pair balance makes the categorical allocation probabilities sum to one. -/
theorem allocationProbability_total (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (mass : Finset (Fin ℓ) → ℝ) (C : ℕ) (hC : 0 < C)
    (hbalance : ∀ i j : Fin ℓ, i ≠ j →
      (∑ K, if i ∈ K ∧ j ∈ K then mass K else 0) = pairEdgeCount G i j)
    (v : TransversalThinning.Coordinate ℓ A) :
    ∑ j : AllocationLabel ℓ C, allocationProbability G mass C v j = 1 := by
  classical
  by_cases hv : ActivePair G v
  · have hCp : (0 : ℝ) < C := by exact_mod_cast hC
    have hpair : (0 : ℝ) < pairEdgeCount G v.1.1 v.2.1 := by exact_mod_cast hv.2
    have hinner (K : Finset (Fin ℓ)) :
        (∑ c : Fin C, allocationProbability G mass C v (some (K, c))) =
          (if v.1.1 ∈ K ∧ v.2.1 ∈ K then mass K else 0) / pairEdgeCount G v.1.1 v.2.1 := by
      by_cases hK : v.1.1 ∈ K ∧ v.2.1 ∈ K
      · simp only [allocationProbability, hv, hK.1, hK.2, and_self, ite_true,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      · simp only [allocationProbability, hv, true_and, ite_eq_right hK, Finset.sum_const_zero, zero_div]
    rw [Fintype.sum_option, Fintype.sum_prod_type]
    simp_rw [hinner]
    simp only [allocationProbability, ite_eq_left hv, zero_add, ← Finset.sum_div,
      hbalance _ _ hv.1, div_self hpair.ne']
  · simp only [Fintype.sum_option, allocationProbability, hv, false_and, ite_false,
      Finset.sum_const_zero, add_zero]

/-- The probabilities derived from an actual fractional clique partition are
normalized; their pair-balance premise is proved from the original edge loads. -/
theorem typeMass_allocationProbability_total
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (w : Finset (Fin ℓ × A) → ℝ)
    (hsupport : ∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × A)))
    (hbalance : ∀ v z, G.Adj v z → pairLoad w v z = 1)
    (C : ℕ) (hC : 0 < C) (v : TransversalThinning.Coordinate ℓ A) :
    ∑ j : AllocationLabel ℓ C, allocationProbability G (typeMass w) C v j = 1 :=
  allocationProbability_total G (typeMass w) C hC
    (typeMass_pair_balance G hparts w hsupport hbalance) v

omit [DecidableEq A] in
/-- Every coordinate of a positive-weight categorical outcome has positive
single-coordinate probability. Thus impossible labels are never selected. -/
theorem allocation_coordinate_positive (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (mass : Finset (Fin ℓ) → ℝ) (hmass : ∀ K, 0 ≤ mass K) (C : ℕ)
    (X : TransversalThinning.Coordinate ℓ A → AllocationLabel ℓ C)
    (hX : 0 < CategoricalSampling.weight (allocationProbability G mass C) X)
    (v : TransversalThinning.Coordinate ℓ A) : 0 < allocationProbability G mass C v (X v) := by
  have hnonneg := allocationProbability_nonneg G mass hmass C v (X v)
  apply hnonneg.lt_of_ne'
  intro hz
  have hzero : CategoricalSampling.weight (allocationProbability G mass C) X = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ v) hz
  exact hX.ne' hzero

omit [DecidableEq A] in
/-- Every actual graph edge has an active pair. -/
theorem activePair_of_adj (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (v : TransversalThinning.Coordinate ℓ A) (hv : G.Adj v.1 v.2) : ActivePair G v := by
  constructor
  · intro hrole
    rcases v with ⟨⟨i, a⟩, ⟨j, b⟩⟩
    change i = j at hrole
    subst j
    exact hparts i a b hv
  · apply Finset.card_pos.mpr
    exact ⟨(v.1.2, v.2.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩

omit [DecidableEq A] in
/-- In a positive-weight outcome, each actual edge is assigned to one profile
containing both roles, with positive aggregate fractional mass. -/
theorem actual_edge_assigned (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (mass : Finset (Fin ℓ) → ℝ) (hmass : ∀ K, 0 ≤ mass K) (C : ℕ)
    (X : TransversalThinning.Coordinate ℓ A → AllocationLabel ℓ C)
    (hX : 0 < CategoricalSampling.weight (allocationProbability G mass C) X)
    (v : TransversalThinning.Coordinate ℓ A) (hv : G.Adj v.1 v.2) :
    ∃ K c, X v = some (K, c) ∧ v.1.1 ∈ K ∧ v.2.1 ∈ K ∧ 0 < mass K := by
  have hp := allocation_coordinate_positive G mass hmass C X hX v
  have hactive := activePair_of_adj G hparts v hv
  cases hlabel : X v with
  | none => simp only [hlabel, allocationProbability, ite_eq_left hactive, lt_self_iff_false] at hp
  | some j =>
    rcases j with ⟨K, c⟩
    have hK : v.1.1 ∈ K ∧ v.2.1 ∈ K := by
      by_contra h
      simp only [hlabel, allocationProbability, hactive, true_and, ite_eq_right h, lt_self_iff_false] at hp
    refine ⟨K, c, rfl, hK.1, hK.2, ?_⟩
    by_contra h
    have hz : mass K = 0 := le_antisymm (le_of_not_gt h) (hmass K)
    simp only [hlabel, allocationProbability, hactive, hK.1, hK.2, and_self, ite_true, hz,
      zero_div, lt_self_iff_false] at hp

end Erdos1017.MultipartiteAllocation
