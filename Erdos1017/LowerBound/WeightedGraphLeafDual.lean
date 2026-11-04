module

public import Erdos1017.LowerBound.WeightedGraphTwoHeadDual

/-!
# Leaf graph dual

The leaf graph (`leafGraph`) is a complete head-and-tail graph with one extra
vertex adjacent only to the head; its dual matrix is supported on the graph, has
charge at most one, and gives a finite lower bound.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A complete head-and-tail graph with one extra vertex adjacent only to the head. -/
def leafGraph : SimpleGraph (Option (Option ι)) where
  Adj i j := i ≠ j ∧ (i = none → j = some none) ∧ (j = none → i = some none)
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro i h
    exact h.1 rfl⟩

omit [Fintype ι] in
theorem leafMatrix_supported (A B : ℝ) (i j : Option (Option ι))
    (hij : ¬(leafGraph : SimpleGraph (Option (Option ι))).Adj i j) :
    twoHeadMatrix 1 0 A B i j = 0 := by
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => cases j <;> simp_all [leafGraph, twoHeadMatrix, adjoinHeadMatrix]
  | some i =>
    cases j with
    | none => cases i <;> simp_all [leafGraph, twoHeadMatrix, adjoinHeadMatrix]
    | some j =>
      have heq : i = j := by simpa [leafGraph] using hij
      subst j
      exact twoHeadMatrix_diag _ _ _ _ _

theorem leaf_charge_le_one (j : ℕ) (hj : 0 < j) (S : Finset (Option (Option ι)))
    (hS : (leafGraph : SimpleGraph (Option (Option ι))).IsClique (S : Set _)) :
    finiteCharge (twoHeadMatrix 1 0 (2 / ((j : ℝ) + 1))
      (-2 / ((j : ℝ) * ((j : ℝ) + 1)))) S ≤ 1 := by
  by_cases hhead : none ∈ S
  · have htail (i : ι) : some (some i) ∉ S := by
      intro hi
      have h := hS hhead hi (by simp)
      have heq := h.2.1 rfl
      simp at heq
    rw [twoHead_charge]
    simp only [ite_eq_left hhead, htail, Finset.filter_false, Finset.card_empty,
      Nat.cast_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_self, zero_div, add_zero, one_mul]
    split_ifs <;> norm_num
  · have h := split_charge_le_one j hj
      (Finset.univ.filter fun i : Option ι => some i ∈ S)
    rw [oneHead_charge] at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [twoHead_charge]
    simpa only [ite_eq_right hhead, mul_zero, zero_mul, zero_add] using h

theorem leaf_finite_lower (j : ℕ) (hj : 0 < j) (w : Option (Option ι) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    finiteObjective w (twoHeadMatrix 1 0 (2 / ((j : ℝ) + 1))
      (-2 / ((j : ℝ) * ((j : ℝ) + 1)))) ≤
      FractionalGraph.densityLimit (finiteDensity (leafGraph : SimpleGraph (Option (Option ι))) w) :=
  finite_objective_le_densityLimit leafGraph w hw hsum _ (twoHeadMatrix_symm _ _ _ _)
    (leafMatrix_supported _ _) (leaf_charge_le_one j hj)

end Erdos1017.WeightedGraph
