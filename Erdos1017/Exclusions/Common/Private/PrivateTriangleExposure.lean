module

public import Erdos1017.Exclusions.Common.TriangleInsertion

/-!
# Triangle exposure of a private root

For a two-neighbor private root with singleton-root mass `α` and missing-leaf
capacity `R`, the common triangle margin holds whenever `R ≤ α`, and a fresh
vertex in the second missed root fiber contributes nonpositively to the
insertion.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Erdos1017.TriangleInsertion

/-- If the fresh vertex lies in the second missed root fiber, it also
misses the designated old leaf. Its signed insertion contribution is
nonpositive even though the original root misses two fibers. -/
theorem majorant_le_private_K_cover (ell u v : ℝ) (b0 b1 b2 : Bool)
    (i p : Prop) [Decidable i] [Decidable p]
    (h0 : b0 = false ↔ i ∨ p)
    (hI1 : i → b1 = true) (hI2 : i → b2 = true)
    (hP1 : p → b1 = false)
    (hell : (1 / 2 : ℝ) ≤ ell) (hu : u ≤ 1 - ell) :
    majorant ell (u + v) (1 - v) (1 - u) b0 b1 b2 ≤
      (if i then u + v - ell else 0) +
        (if b1 = false then max (1 - ell - v) 0 else 0) +
        (if b2 = false then 1 - ell - u else 0) := by
  by_cases hi : i
  · have hb0 := h0.mpr (Or.inl hi)
    simp [majorant, hi, hb0, hI1 hi, hI2 hi]
  · by_cases hp : p
    · have hb0 := h0.mpr (Or.inr hp)
      have hb1 := hP1 hp
      cases hb2 : b2
      · have hm : majorant ell (u + v) (1 - v) (1 - u)
            b0 b1 false = -3 * ell := by simp [majorant, hb0, hb1]
        rw [hm]
        simp only [hi, hb1, ↓reduceIte, zero_add]
        linarith [le_max_right (1 - ell - v) 0]
      · have hm : majorant ell (u + v) (1 - v) (1 - u)
            b0 b1 true = 1 - 2 * ell := by simp [majorant, hb0, hb1]
        rw [hm]
        simp only [hi, hb1, Bool.true_eq_false, ↓reduceIte, zero_add]
        linarith [le_max_right (1 - ell - v) 0]
    · have hb0 : b0 = true := by cases b0 <;> simp_all
      cases b1 <;> cases b2 <;>
        simp only [majorant, hb0, hi, Bool.false_eq_true,
          Bool.true_eq_false, ↓reduceIte, zero_add, add_zero] <;>
        linarith [le_max_left (1 - ell - v) 0, le_max_right (1 - ell - v) 0]

/-- The two-neighbor private root has singleton-root mass `α` and
missing-leaf capacity `R`. Retaining the signed root term
gives the common triangle margin whenever `R ≤ α`. -/
theorem private_NN_star_capacity {α R ell u v : ℝ}
    (hα : 0 ≤ α) (hRα : R ≤ α)
    (hell : 0 ≤ ell) (hu : u ≤ 0) (hv : v ≤ 1) :
    α * (u + v - ell) + R * (max (1 - ell - v) 0 + (1 - ell - u)) ≤
      (1 - ell) * (α + R) := by
  by_cases h : 0 ≤ 1 - ell - v
  · rw [max_eq_left h]
    have ht : 0 ≤ (α - R) * (1 - ell - u - v) := by
      apply mul_nonneg
      · linarith
      · linarith [h, hu]
    nlinarith [mul_nonneg hα hell]
  · rw [max_eq_right (le_of_not_ge h)]
    have ht : (α - R) * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hu
    nlinarith [mul_nonneg hα (sub_nonneg.mpr hv)]

/-- If one old leaf lies outside the second missed fiber's
neighborhood, only the first fiber contributes to the root term.
Both positive leaf terms can be paid by the same capacity `A`. -/
theorem private_K_star_capacity {A ell u v : ℝ}
    (hA : 0 ≤ A) (hell : 0 ≤ ell) (hv : v ≤ 1) :
    A * (u + v - ell) + A * (max (1 - ell - v) 0 + (1 - ell - u)) ≤
      2 * (1 - ell) * A := by
  by_cases h : 0 ≤ 1 - ell - v
  · rw [max_eq_left h]
    nlinarith [mul_nonneg hA hell]
  · rw [max_eq_right (le_of_not_ge h)]
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hv)]

end Erdos1017.TriangleInsertion
