module

public import Erdos1017.Multipartite.Selector.SelectorValue
public import Erdos1017.Multipartite.Selector.SelectorBoundary

/-!
# Attainment and relaxed bounds for the selector value

The exact selector value is attained by both a primal and a signed dual, and any
relaxed selector bounds it without exact moments (`value_le_relaxed_cost`).
-/

@[expose] public section

namespace Erdos1017.Selector

/-- The exact selector value is attained by both a primal and a signed dual. -/
theorem value_attained {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    ∃ w, PrimalFeasible p w ∧ cost w = value p ∧ ∃ D, DualOptimal p D ∧
      objective p D = value p ∧ (∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1) ∧
        ∀ i j, D.beta i j ≤ 0 := by
  obtain ⟨w, hw, D, hD, heq, halpha, hbeta⟩ := exists_signed_primal_dual p hp
  have hvalue := value_eq_cost p w D hw hD.1 heq
  exact ⟨w, hw, hvalue.symm, D, hD, heq.trans hvalue.symm, halpha, hbeta⟩

/-- A relaxed selector bounds the exact optimum, without requiring its moments to be exact. -/
theorem value_le_relaxed_cost {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (w : Selection m → ℝ) (hw : RelaxedPrimalFeasible p w) : value p ≤ cost w := by
  obtain ⟨_, _, _, D, hD, heq, halpha, hbeta⟩ := value_attained p hp
  rw [← heq]
  exact relaxed_weak_duality p w D hw hD.1 (fun i => (halpha i).1) hbeta

end Erdos1017.Selector
