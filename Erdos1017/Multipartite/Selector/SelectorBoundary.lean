module

public import Erdos1017.Multipartite.Selector.SelectorSigns
public import Erdos1017.Multipartite.Selector.SelectorLinearProgram
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Selector primal and dual on the closed cube

Every closed-cube target has an attained exact primal and an attained signed
dual of the same cost (`exists_signed_primal_dual`); zero coordinates are
removed and restored by `insertDual` and `insertWeights`, and a coordinate fixed
at one uses `unitDual`.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Selector

open scoped BigOperators

/-- Restore a removed zero-probability label with zero dual coefficients. -/
def insertDual {m : ℕ} (i : Fin (m + 1)) (D : Dual m) : Dual (m + 1) where
  alpha := i.insertNth 0 D.alpha
  beta := i.insertNth (fun _ => 0) (fun k => i.insertNth 0 (D.beta k))
  beta_symm k l := by
    induction k using i.succAboveCases <;> induction l using i.succAboveCases <;>
      simp [D.beta_symm]
  beta_diag k := by induction k using i.succAboveCases <;> simp [D.beta_diag]

theorem insertDual_objective {m : ℕ} (i : Fin (m + 1)) (D : Dual m)
    (p : Fin (m + 1) → ℝ) : objective p (insertDual i D) = objective (i.removeNth p) D := by
  unfold objective
  have hfirst : (∑ k, (insertDual i D).alpha k * p k) = ∑ k, D.alpha k * p (i.succAbove k) := by
    rw [Fin.sum_univ_succAbove _ i]
    simp [insertDual]
  have hpair : (∑ k, ∑ l, (insertDual i D).beta k l * (p k * p l)) =
      ∑ k, ∑ l, D.beta k l * (p (i.succAbove k) * p (i.succAbove l)) := by
    rw [Fin.sum_univ_succAbove _ i]
    simp only [insertDual, Fin.insertNth_apply_same, zero_mul, Finset.sum_const_zero, zero_add,
      Fin.insertNth_apply_succAbove]
    apply Finset.sum_congr rfl
    intro k _
    rw [Fin.sum_univ_succAbove _ i]
    simp
  rw [hfirst, hpair]
  rfl

theorem insertDual_feasible {m : ℕ} (i : Fin (m + 1)) (D : Dual m)
    (hD : DualFeasible D) : DualFeasible (insertDual i D) := by
  intro X
  unfold quadratic
  rw [insertDual_objective]
  exact hD (i.removeNth X)

/-- A removed label is false in every lifted selector outcome. -/
def insertWeights {m : ℕ} (i : Fin (m + 1)) (w : Selection m → ℝ)
    (X : Selection (m + 1)) : ℝ := if X i then 0 else w (i.removeNth X)

theorem insertWeights_sum {m : ℕ} (i : Fin (m + 1)) (w : Selection m → ℝ)
    (f : Selection (m + 1) → ℝ) :
    (∑ X, insertWeights i w X * f X) = ∑ X, w X * f (i.insertNth false X) := by
  rw [← (Fin.insertNthEquiv (fun _ : Fin (m + 1) => Bool) i).sum_comp]
  simp [Fin.insertNthEquiv, Fintype.sum_prod_type, insertWeights]

theorem insertWeights_cost {m : ℕ} (i : Fin (m + 1)) (w : Selection m → ℝ) :
    cost (insertWeights i w) = cost w := by
  simpa [cost] using insertWeights_sum i w (fun _ => 1)

theorem insertWeights_feasible {m : ℕ} (i : Fin (m + 1)) (p : Fin (m + 1) → ℝ)
    (hi : p i = 0) (w : Selection m → ℝ) (hw : PrimalFeasible (i.removeNth p) w) :
    PrimalFeasible p (insertWeights i w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X
    unfold insertWeights
    split_ifs
    · exact le_rfl
    · exact hw.1 _
  · simpa [insertWeights, Fin.removeNth_fun_const] using hw.2.1
  · intro k
    rw [insertWeights_sum]
    induction k using i.succAboveCases
    · simp [bit, hi]
    · simpa [Fin.removeNth] using hw.2.2.1 _
  · intro k l hkl
    rw [insertWeights_sum]
    induction k using i.succAboveCases <;> induction l using i.succAboveCases
    · exact (hkl rfl).elim
    · simp [bit, hi]
    · simp [bit, hi]
    · simpa [Fin.removeNth] using hw.2.2.2 _ _ (fun h => hkl (congrArg i.succAbove h))

/-- A coordinate fixed at probability one has a feasible dual of objective one. -/
def unitDual {m : ℕ} (i : Fin m) : Dual m where
  alpha k := if k = i then 1 else 0
  beta _ _ := 0
  beta_symm _ _ := rfl
  beta_diag _ := rfl

theorem unitDual_objective {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    objective p (unitDual i) = p i := by simp [objective, unitDual, ite_mul]

theorem unitDual_feasible {m : ℕ} (i : Fin m) : DualFeasible (unitDual i) := by
  intro X
  unfold quadratic
  rw [unitDual_objective]
  cases X i <;> norm_num [bit]

/-- Every closed-cube target has an attained exact primal and an attained signed
dual of the same cost. Zero coordinates are removed and restored explicitly. -/
theorem exists_signed_primal_dual {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    ∃ w : Selection m → ℝ, PrimalFeasible p w ∧
      ∃ D : Dual m, DualOptimal p D ∧ objective p D = cost w ∧
        (∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1) ∧ ∀ i j, D.beta i j ≤ 0 := by
  induction m with
  | zero =>
    have hp' : ∀ i, 0 < p i ∧ p i < 1 := fun i => Fin.elim0 i
    obtain ⟨w, hw, D, hD, heq⟩ := SelectorLinearProgram.exists_primal_dual p hp'
    exact ⟨w, hw, D, hD, heq, interior_optimal_signs p D hp' hD⟩
  | succ m ih =>
    by_cases hone : ∃ i, p i = 1
    · obtain ⟨i, hi⟩ := hone
      have hw := bernoulli_selector_feasible p hp
      have hcost : cost (selectorWeight p) = 1 := by
        apply le_antisymm (bernoulli_selector_cost_le_one p hp)
        simpa [unitDual_objective, hi] using weak_duality p (selectorWeight p)
          (unitDual i) hw (unitDual_feasible i)
      refine ⟨selectorWeight p, hw, unitDual i, ⟨unitDual_feasible i, ?_⟩, ?_, ?_, ?_⟩
      · intro D hD
        rw [unitDual_objective, hi]
        exact objective_le_one p D hp hD
      · rw [unitDual_objective, hi, hcost]
      · intro k
        simp only [unitDual]
        split_ifs <;> norm_num
      · intro k l
        exact le_rfl
    · by_cases hzero : ∃ i, p i = 0
      · obtain ⟨i, hi⟩ := hzero
        obtain ⟨w, hw, D, hD, heq, halpha, hbeta⟩ := ih (i.removeNth p)
          (fun k => hp (i.succAbove k))
        have hw' := insertWeights_feasible i p hi w hw
        have hD' := insertDual_feasible i D hD.1
        have heq' : objective p (insertDual i D) = cost (insertWeights i w) := by
          rw [insertDual_objective, insertWeights_cost]
          exact heq
        refine ⟨insertWeights i w, hw', insertDual i D, ⟨hD', ?_⟩, heq', ?_, ?_⟩
        · intro E hE
          rw [heq']
          exact weak_duality p _ E hw' hE
        · intro k
          induction k using i.succAboveCases
          · simp [insertDual]
          · simpa [insertDual] using halpha _
        · intro k l
          induction k using i.succAboveCases <;> induction l using i.succAboveCases
          · simp [insertDual]
          · simp [insertDual]
          · simp [insertDual]
          · simpa [insertDual] using hbeta _ _
      · have hp' : ∀ i, 0 < p i ∧ p i < 1 := by
          intro i
          exact ⟨lt_of_le_of_ne (hp i).1 (fun h => hzero ⟨i, h.symm⟩),
            lt_of_le_of_ne (hp i).2 (fun h => hone ⟨i, h⟩)⟩
        obtain ⟨w, hw, D, hD, heq⟩ := SelectorLinearProgram.exists_primal_dual p hp'
        exact ⟨w, hw, D, hD, heq, interior_optimal_signs p D hp' hD⟩

end Erdos1017.Selector
