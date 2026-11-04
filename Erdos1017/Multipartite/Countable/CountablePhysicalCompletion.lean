module

public import Erdos1017.Multipartite.Dust.CountableDustVariation
public import Erdos1017.Multipartite.Countable.CountableTypeCompletion

/-!
# Completion loss at arbitrary anchor mass

Partial completion of a head preserves the anchor's exterior row, the exact
completion loss is independent of the anchor mass, and completing positive mass
of a head after an admissible anchor correction produces a feasible dual with
its exact cost.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- Partial completion preserves the anchor's entire exterior row. -/
theorem anchorRow_completeType {D : Coefficients} (hD : D ∈ feasible) (i : ℕ)
    (q : Fin 2 → ℝ) (hq₀ : ∀ j, 0 ≤ q j) (hq : ∑ j, q j = 1)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p) (x s : ℝ) :
    anchorRow (Function.update p i (x + s * q 0)) (s * q 1) D =
      anchorRow (Function.update p i x) s (completeType D i (repeatPenalty D i) q) := by
  have hE := completeType_feasible hD i q hq₀ hq
  rw [anchorRow_update hD p hp hsum _ i, anchorRow_update hE p hp hsum _ i]
  simp only [anchorRow, head, linear, completeType]
  ring

/-- The exact completion loss is independent of the anchor mass. Every
coefficient is the actual averaged feasible completion coefficient. -/
theorem physicalObjective_completeType_loss {D : Coefficients} (hD : D ∈ feasible) (i : ℕ)
    (q : Fin 2 → ℝ) (hq₀ : ∀ j, 0 ≤ q j) (hq : ∑ j, q j = 1)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p) (hpi : p i = 0)
    (a x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    physicalObjective a (Function.update p i (x + s * q 0)) (s * q 1) D -
      physicalObjective a (Function.update p i x) s (completeType D i (repeatPenalty D i) q) =
        repeatPenalty D i * (x * (s * q 0) + (s * q 0) ^ 2 / 2) := by
  have hrow := anchorRow_completeType hD i q hq₀ hq p hp hsum x s
  have hloss := completeType_loss hD i q hq₀ hq p hp hsum hpi x s hx hs
  rw [physicalObjective_eq_objective, physicalObjective_eq_objective, hrow]
  linarith

/-- Completing positive mass of an old head, after an arbitrary admissible
anchor correction, produces a genuine feasible dual with its exact cost. -/
theorem exists_completed_head_objective {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s)
    (i : ℕ) (a r z : ℝ) (hz : 0 < z) (hret : 0 ≤ p i - r - z) :
    ∃ E ∈ feasible,
      physicalObjective a (Function.update p i (p i - r - z)) (s + z) E =
        physicalObjective a (Function.update p i (p i - r)) s D -
          repeatPenalty D i * ((p i - r) * z - z ^ 2 / 2) := by
  let S := s + z
  have hS : 0 < S := add_pos_of_nonneg_of_pos hs hz
  let q : Fin 2 → ℝ := fun j => if j = 0 then z / S else s / S
  have hq₀ (j : Fin 2) : 0 ≤ q j := by
    dsimp only [q]
    split_ifs <;> positivity
  have hq : ∑ j, q j = 1 := by
    rw [Fin.sum_univ_two]
    change z / S + s / S = 1
    rw [← add_div, show z + s = S by dsimp [S]; ring, div_self hS.ne']
  have hq0 : S * q 0 = z := by
    simp only [q, ↓reduceIte]
    field_simp
  have hq1 : S * q 1 = s := by
    norm_num [q]
    field_simp
  let E := completeType D i (repeatPenalty D i) q
  have hE : E ∈ feasible := completeType_feasible hD i q hq₀ hq
  have hp0 (j : ℕ) : 0 ≤ Function.update p i 0 j := by
    by_cases hj : j = i
    · subst j
      simp
    · simpa [Function.update_of_ne, hj] using hp j
  have hloss := physicalObjective_completeType_loss hD i q hq₀ hq
    (Function.update p i 0) hp0 (hsum.update i 0) (by simp) a (p i - r - z) S hret hS.le
  rw [hq0, hq1, Function.update_idem, Function.update_idem,
    show p i - r - z + z = p i - r by ring] at hloss
  refine ⟨E, hE, ?_⟩
  nlinarith [hloss]

end Erdos1017.MultipartiteCountableDual
