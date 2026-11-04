module

public import Erdos1017.IntegerTransfer.AllocatedEdgeCounts

/-!
# Residual edges and the cost of local matchings

This module defines `residualAllocatedEdges`, the edges not assigned to a group
selected for clique matching, shows that matched-label fibers and residual edges
partition the graph-edge coordinates exactly, and bounds the cost of a local
near-perfect matching (`matching_cost_le`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators

variable {ℓ : ℕ} {A J I : Type*} [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J] [Fintype I]

/-- Actual edges not assigned to a group selected for clique matching. -/
def residualAllocatedEdges (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (X : TransversalThinning.Coordinate ℓ A → J) (label : I → J) :
    Finset (TransversalThinning.Coordinate ℓ A) :=
  (TransversalClique.graphEdges G).filter (fun v => X v ∉ Set.range label)

omit [DecidableEq A] [Fintype J] in
/-- The matched-label fibres and the remaining allocated edges partition the
actual graph-edge coordinates exactly. -/
theorem allocatedEdges_card_decomposition (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (X : TransversalThinning.Coordinate ℓ A → J) (label : I → J)
    (hinj : Function.Injective label) :
    ((residualAllocatedEdges G X label).card : ℝ) +
      ∑ i, ((allocatedEdges G X (label i)).card : ℝ) =
        (TransversalClique.graphEdges G).card := by
  classical
  have hcard (j : J) : ((allocatedEdges G X j).card : ℝ) =
      ∑ v ∈ TransversalClique.graphEdges G, if X v = j then (1 : ℝ) else 0 := by
    simp only [allocatedEdges, Finset.card_eq_sum_ones, Finset.sum_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hres : ((residualAllocatedEdges G X label).card : ℝ) =
      ∑ v ∈ TransversalClique.graphEdges G, if X v ∉ Set.range label then (1 : ℝ) else 0 := by
    simp only [residualAllocatedEdges, Finset.card_eq_sum_ones, Finset.sum_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hres]
  simp_rw [hcard]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : X v ∈ Set.range label
  · obtain ⟨i, hi⟩ := hv
    have hsingle : (∑ j : I, if X v = label j then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp only [hi, ite_true]
      · intro j _ hji
        exact ite_eq_right (fun h => hji (hinj (h.symm.trans hi.symm)))
      · simp
    have hv' : X v ∈ Set.range label := ⟨i, hi⟩
    simp only [hv', not_true_eq_false, ite_false, hsingle, zero_add]
  · have hzero : (∑ j : I, if X v = label j then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact ite_eq_right (fun h => hv ⟨j, h.symm⟩)
    simp only [hv, not_false_eq_true, ite_true, hzero, add_zero]

/-- A local near-perfect matching turns almost all of its allocated edges into
cliques at the correct fractional cost. -/
theorem matching_cost_le {E m r mass ρ : ℝ} (hE : 0 ≤ E) (hr : 1 ≤ r)
    (hρ : 0 ≤ ρ)
    (hmatching : (1 - ρ) * E / r ≤ m)
    (horder : E ≤ r * ((1 + ρ) * mass)) :
    E - (r - 1) * m ≤ (1 + ρ * r) * (1 + ρ) * mass := by
  have hrpos : 0 < r := by linarith
  have hmul := mul_le_mul_of_nonneg_left hmatching (sub_nonneg.mpr hr)
  have hupper := mul_le_mul_of_nonneg_left horder
    (show 0 ≤ (1 + ρ * r) / r from div_nonneg (by positivity) hrpos.le)
  have hid : E - (r - 1) * ((1 - ρ) * E / r) = ((1 + ρ * (r - 1)) / r) * E := by field_simp; ring
  have hcoef : ((1 + ρ * (r - 1)) / r) * E ≤ ((1 + ρ * r) / r) * E := by
    apply mul_le_mul_of_nonneg_right _ hE
    apply div_le_div_of_nonneg_right _ hrpos.le
    nlinarith only [hρ]
  calc
    E - (r - 1) * m ≤ E - (r - 1) * ((1 - ρ) * E / r) := sub_le_sub_left hmul E
    _ = _ := hid
    _ ≤ ((1 + ρ * r) / r) * E := hcoef
    _ ≤ (1 + ρ * r) * (1 + ρ) * mass := by
      convert hupper using 1
      field_simp

end Erdos1017.MultipartiteAllocation
