module

public import Erdos1017.IntegerTransfer.WeightedRectangle

/-!
# Coordinate resampling in assignment sums

Resampling one or two coordinates of an assignment preserves the full assignment
sum with its exact multiplicity (`sum_update`, `sum_update_update`), and a bound
on each two-coordinate slice gives a bound on the complete sum
(`abs_sum_le_of_slices`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CliqueCounting

open scoped BigOperators

variable {ι A : Type*} [DecidableEq ι] [Fintype ι] [Fintype A]

/-- Swapping a stored coordinate with an extra coordinate is a bijection. -/
def swapCoordinate (i : ι) : ((ι → A) × A) ≃ ((ι → A) × A) where
  toFun z := (Function.update z.1 i z.2, z.1 i)
  invFun z := (Function.update z.1 i z.2, z.1 i)
  left_inv z := by
    rcases z with ⟨X, a⟩
    simp
  right_inv z := by
    rcases z with ⟨X, a⟩
    simp

/-- Resampling one coordinate preserves the full assignment sum, with its exact
multiplicity. No nonempty-domain assumption is needed. -/
theorem sum_update (f : (ι → A) → ℝ) (i : ι) :
    (∑ X : ι → A, ∑ a : A, f (Function.update X i a)) =
      Fintype.card A * ∑ X : ι → A, f X := by
  have h := (swapCoordinate (A := A) i).sum_comp (fun z => f z.1)
  simp only [swapCoordinate, Equiv.coe_fn_mk, Fintype.sum_prod_type] at h
  rw [h]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Finset.mul_sum]

/-- Resampling the endpoints of an edge preserves the assignment sum twice. -/
theorem sum_update_update (f : (ι → A) → ℝ) (i j : ι) :
    (∑ X : ι → A, ∑ a : A, ∑ b : A,
      f (Function.update (Function.update X i a) j b)) =
      (Fintype.card A : ℝ) ^ 2 * ∑ X : ι → A, f X := by
  rw [sum_update (fun X => ∑ b : A, f (Function.update X j b)) i, sum_update f j]
  ring

/-- A bound for each two-coordinate slice gives a bound for the complete
assignment sum, retaining the exact scaling when the domain is empty. -/
theorem abs_sum_le_of_slices (f : (ι → A) → ℝ) (i j : ι) (η : ℝ)
    (h : ∀ X : ι → A, |∑ a : A, ∑ b : A,
      f (Function.update (Function.update X i a) j b)| ≤ η) :
    (Fintype.card A : ℝ) ^ 2 * |∑ X : ι → A, f X| ≤
      Fintype.card (ι → A) * η := by
  have heq := sum_update_update f i j
  have hbound : |∑ X : ι → A, ∑ a : A, ∑ b : A,
      f (Function.update (Function.update X i a) j b)| ≤
      Fintype.card (ι → A) * η := by
    calc
      _ ≤ ∑ X : ι → A, |∑ a : A, ∑ b : A,
          f (Function.update (Function.update X i a) j b)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _X : ι → A, η := Finset.sum_le_sum (fun X _ => h X)
      _ = _ := by simp
  rw [heq, abs_mul, abs_of_nonneg (sq_nonneg _)] at hbound
  exact hbound

end Erdos1017.CliqueCounting
