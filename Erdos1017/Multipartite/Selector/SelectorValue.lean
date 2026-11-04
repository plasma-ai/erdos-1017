module

public import Erdos1017.FractionalLimit.Selector
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The exact finite selector value

`value` is the infimum of costs over nonnegative weights with exact moments; it
lies between zero and one, bounds every feasible dual objective, and is
identified by equal primal and dual costs without an attainment assumption.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Selector

open scoped BigOperators

/-- The exact finite selector value, defined from nonnegative weights with exact moments. -/
def value {m : ℕ} (p : Fin m → ℝ) : ℝ :=
  sInf {c | ∃ w, PrimalFeasible p w ∧ cost w = c}

theorem cost_nonneg {m : ℕ} (p : Fin m → ℝ) (w : Selection m → ℝ)
    (hw : PrimalFeasible p w) : 0 ≤ cost w := Finset.sum_nonneg (fun X _ => hw.1 X)

theorem value_le_cost {m : ℕ} (p : Fin m → ℝ) (w : Selection m → ℝ)
    (hw : PrimalFeasible p w) : value p ≤ cost w := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨v, hv, rfl⟩
    exact cost_nonneg p v hv
  · exact ⟨w, hw, rfl⟩

theorem value_nonneg {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : 0 ≤ value p := by
  refine le_csInf (s := {c | ∃ w, PrimalFeasible p w ∧ cost w = c})
    ⟨cost (selectorWeight p), selectorWeight p, bernoulli_selector_feasible p hp, rfl⟩ ?_
  rintro c ⟨w, hw, rfl⟩
  exact cost_nonneg p w hw

theorem value_le_one {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : value p ≤ 1 :=
  (value_le_cost p (selectorWeight p) (bernoulli_selector_feasible p hp)).trans
    (bernoulli_selector_cost_le_one p hp)

theorem objective_le_value {m : ℕ} (p : Fin m → ℝ) (D : Dual m)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hD : DualFeasible D) : objective p D ≤ value p := by
  refine le_csInf (s := {c | ∃ w, PrimalFeasible p w ∧ cost w = c})
    ⟨cost (selectorWeight p), selectorWeight p, bernoulli_selector_feasible p hp, rfl⟩ ?_
  rintro c ⟨w, hw, rfl⟩
  exact weak_duality p w D hw hD

/-- Equal primal and dual costs identify the infimum without an attainment assumption. -/
theorem value_eq_cost {m : ℕ} (p : Fin m → ℝ) (w : Selection m → ℝ) (D : Dual m)
    (hw : PrimalFeasible p w) (hD : DualFeasible D) (heq : objective p D = cost w) :
    value p = cost w := by
  apply le_antisymm (value_le_cost p w hw)
  refine le_csInf (s := {c | ∃ v, PrimalFeasible p v ∧ cost v = c}) ⟨cost w, w, hw, rfl⟩ ?_
  rintro c ⟨v, hv, rfl⟩
  rw [← heq]
  exact weak_duality p v D hv hD

end Erdos1017.Selector
