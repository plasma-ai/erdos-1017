module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Score selection inside the support of the sampling law

Simultaneous score selection can be made inside the support of the finite
sampling law, which preserves deterministic restrictions on the allowed labels
(`exists_positive_all_scores_lt_one`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FiniteSampling

open scoped BigOperators

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

/-- Simultaneous score selection can be made inside the support of the actual
finite sampling law. This preserves deterministic restrictions on allowed labels. -/
theorem exists_positive_all_scores_lt_one (w : Ω → ℝ) (hw : ∀ X, 0 ≤ w X)
    (htotal : ∑ X, w X = 1) (Z : I → Ω → ℝ) (hZ : ∀ i X, 0 ≤ Z i X)
    (b : I → ℝ) (hmean : ∀ i, (∑ X, w X * Z i X) ≤ b i)
    (hbudget : ∑ i, b i < 1) : ∃ X, 0 < w X ∧ ∀ i, Z i X < 1 := by
  have hsum : (∑ X, w X * ∑ i, Z i X) < 1 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact (Finset.sum_le_sum (fun i _ => hmean i)).trans_lt hbudget
  obtain ⟨X, hwX, hX⟩ : ∃ X, 0 < w X ∧ (∑ i, Z i X) < 1 := by
    by_contra h
    push Not at h
    have hlarge : 1 ≤ ∑ X, w X * ∑ i, Z i X := by
      calc
        1 = ∑ X, w X := htotal.symm
        _ ≤ _ := Finset.sum_le_sum (fun X _ => by
          by_cases hz : w X = 0
          · simp only [hz, zero_mul, le_refl]
          · have hp : 0 < w X := (hw X).lt_of_ne' hz
            simpa using mul_le_mul_of_nonneg_left (h X hp) (hw X))
    exact (not_lt_of_ge hlarge) hsum
  refine ⟨X, hwX, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hZ j X) (Finset.mem_univ i)).trans_lt hX

end Erdos1017.FiniteSampling
