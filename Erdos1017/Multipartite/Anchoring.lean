module

public import Erdos1017.Multipartite.Multipartite
public import Erdos1017.Multipartite.Selector.SelectorValue
public import Erdos1017.Multipartite.Selector.SelectorLinearProgram
public import Erdos1017.Multipartite.Selector.SelectorSigns

/-!
# Anchoring from an exact selector and dual

An exact selector and an equally valued signed dual identify the anchored
partition value, giving largest-part anchoring when the secondary parts are
strictly smaller and positive.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Multipartite

/-- An exact selector and an equally valued signed dual identify the anchored partition value. -/
theorem anchoring_of_primal_dual {m : ℕ} (p : Fin m → ℝ)
    (w : Selector.Selection m → ℝ) (D : Selector.Dual m)
    (hw : Selector.PrimalFeasible p w) (hD : Selector.DualFeasible D)
    (hbeta : ∀ i j, D.beta i j ≤ 0) (heq : Selector.objective p D = Selector.cost w)
    (t : ℝ) : value (fun i => t * anchorMasses p i) = t ^ 2 * Selector.value p := by
  have hprimal := scale_feasible (anchorMasses p) (anchorWeight w) (anchor_feasible p w hw) t
  have hdual := anchor_dual_feasible D hD hbeta
  have hvalue := Selector.value_eq_cost p w D hw hD heq
  apply le_antisymm
  · calc
      value (fun i => t * anchorMasses p i) ≤ cost (fun X => t ^ 2 * anchorWeight w X) :=
        value_le_cost _ _ hprimal
      _ = t ^ 2 * Selector.value p := by rw [scale_cost, anchor_cost, hvalue]
  · calc
      t ^ 2 * Selector.value p = t ^ 2 * Selector.objective p D := by rw [hvalue, heq]
      _ = objective (fun i => t * anchorMasses p i) (anchorDual D) := by
        rw [scale_objective, anchor_objective]
      _ ≤ value (fun i => t * anchorMasses p i) := objective_le_value _ _ hdual ⟨_, hprimal⟩

/-- Largest-part anchoring for strictly smaller positive secondary parts. -/
theorem interior_anchoring {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (t : ℝ) :
    value (fun i => t * anchorMasses p i) = t ^ 2 * Selector.value p := by
  obtain ⟨w, hw, D, hD, heq⟩ := SelectorLinearProgram.exists_primal_dual p hp
  exact anchoring_of_primal_dual p w D hw hD.1
    (Selector.interior_optimal_signs p D hp hD).2 heq t

end Erdos1017.Multipartite
