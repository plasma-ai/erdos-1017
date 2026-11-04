module

public import Erdos1017.Multipartite.Anchoring
public import Erdos1017.Multipartite.Selector.SelectorOptimalValue

/-!
# Largest-part anchoring with ties and zero parts

Largest-part anchoring extends to zero secondary parts and ties for the largest
part, with the exact normalized identity `largest_part_anchoring`, and the
independent selector gives the largest-part square upper bound.
-/

@[expose] public section

namespace Erdos1017.Multipartite

/-- Largest-part anchoring includes zero secondary parts and ties for the largest part. -/
theorem closed_anchoring {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (t : ℝ) :
    value (fun i => t * anchorMasses p i) = t ^ 2 * Selector.value p := by
  obtain ⟨w, hw, D, hD, heq, _, hbeta⟩ := Selector.exists_signed_primal_dual p hp
  exact anchoring_of_primal_dual p w D hw hD.1 hbeta heq t

/-- The value of a profile is the square of its largest part times the selector
value of the other parts, normalized by the largest. -/
theorem largest_part_anchoring {m : ℕ} (a : Option (Fin m) → ℝ)
    (ha : 0 < a none) (hsecondary : ∀ i, 0 ≤ a (some i) ∧ a (some i) ≤ a none) :
    value a = a none ^ 2 * Selector.value (fun i => a (some i) / a none) := by
  let p : Fin m → ℝ := fun i => a (some i) / a none
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := by
    intro i
    exact ⟨div_nonneg (hsecondary i).1 ha.le,
      (div_le_one ha).mpr (hsecondary i).2⟩
  have heq : (fun i => a none * anchorMasses p i) = a := by
    funext i
    cases i with
    | none => simp [anchorMasses, Option.elim']
    | some i => simp [anchorMasses, Option.elim', p, mul_div_cancel₀, ha.ne']
  simpa only [heq] using closed_anchoring p hp (a none)

/-- The independent selector gives the largest-part square upper bound. -/
theorem value_le_largest_part_sq {m : ℕ} (a : Option (Fin m) → ℝ)
    (ha : 0 < a none) (hsecondary : ∀ i, 0 ≤ a (some i) ∧ a (some i) ≤ a none) :
    value a ≤ a none ^ 2 := by
  rw [largest_part_anchoring a ha hsecondary]
  have hp : ∀ i, 0 ≤ a (some i) / a none ∧ a (some i) / a none ≤ 1 := by
    intro i
    exact ⟨div_nonneg (hsecondary i).1 ha.le, (div_le_one ha).mpr (hsecondary i).2⟩
  simpa using mul_le_mul_of_nonneg_left (Selector.value_le_one _ hp) (sq_nonneg (a none))

end Erdos1017.Multipartite
