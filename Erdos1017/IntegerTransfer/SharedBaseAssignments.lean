module

public import Erdos1017.IntegerTransfer.SharedBasePattern

/-!
# Splitting assignments into base and extension coordinates

This module splits a complete assignment into its base and extension coordinates
(`splitAssignment`), so that sums over assignments factor into base and
extension sums, and restricts a doubled assignment to either copy to select one
of the two extensions over the shared base.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.SharedBasePattern

open scoped BigOperators

variable {A : Type*} (t u : ℕ)

/-- Split a complete assignment into its base and extension coordinates. -/
def splitAssignment : (Fin (t + u) → A) ≃ (Fin t → A) × (Fin u → A) where
  toFun X := (fun i => X (Fin.castAdd u i), fun i => X (Fin.natAdd t i))
  invFun X := Fin.addCases X.1 X.2
  left_inv X := by
    funext i
    exact Fin.addCases (fun i => by simp) (fun i => by simp) i
  right_inv X := by
    apply Prod.ext <;> funext i <;> simp

/-- Summation over actual assignments splits into base and extension sums. -/
theorem sum_split [Fintype A] (f : (Fin (t + u) → A) → ℝ) :
    (∑ X, f X) = ∑ x : Fin t → A, ∑ y : Fin u → A, f (Fin.addCases x y) := by
  have h := (splitAssignment (A := A) t u).symm.sum_comp f
  simpa only [splitAssignment, Equiv.coe_fn_symm_mk, Fintype.sum_prod_type] using h.symm

theorem right_castAdd (i : Fin t) :
    right t u (Fin.castAdd u i) = Fin.castAdd u (Fin.castAdd u i) := by
  apply Fin.ext
  simp [right, i.isLt]

theorem right_natAdd (i : Fin u) :
    right t u (Fin.natAdd t i) = Fin.natAdd (t + u) i := by
  apply Fin.ext
  have hi : ¬ t + i.val < t := by omega
  simp [right, hi]
  omega

/-- Restricting a doubled assignment to its first copy selects the first extension. -/
theorem addCases_left (x : Fin t → A) (y z : Fin u → A) (i : Fin (t + u)) :
    (Fin.addCases (Fin.addCases x y) z : Fin (t + u + u) → A) (left t u i) =
      (Fin.addCases x y : Fin (t + u) → A) i := by
  simp [left]

/-- Restricting to the second copy keeps the same base and selects the second extension. -/
theorem addCases_right (x : Fin t → A) (y z : Fin u → A) (i : Fin (t + u)) :
    (Fin.addCases (Fin.addCases x y) z : Fin (t + u + u) → A) (right t u i) =
      (Fin.addCases x z : Fin (t + u) → A) i := by
  refine Fin.addCases ?_ ?_ i
  · intro i
    rw [right_castAdd]
    simp
  · intro i
    rw [right_natAdd]
    simp

end Erdos1017.SharedBasePattern
