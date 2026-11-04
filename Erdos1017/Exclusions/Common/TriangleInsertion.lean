module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Inserting a fresh point into a tight triangle

This module defines a majorant for the eight adjacency patterns of a fresh point
inserted against a tight triangle, paid by four-point, three-point and pair
inequalities, and bounds it by the universal cover; with one nonpositive root
star the capacity is at most `delta` times the exterior mass.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TriangleInsertion

/-- The fresh-point insertion bound for the eight actual adjacency
patterns against a tight triangle. The stars are indexed by the missed
old vertex. -/
def majorant (ell s0 s1 s2 : ℝ) (b0 b1 b2 : Bool) : ℝ :=
  if b0 then
    if b1 then (if b2 then 0 else s2 - ell)
    else if b2 then s1 - ell else 1 - 2 * ell
  else if b1 then (if b2 then s0 - ell else 1 - 2 * ell)
    else if b2 then 1 - 2 * ell else -3 * ell

/-- Actual four-point, three-point and pair inequalities pay every
insertion pattern. Charges on the original nonedges are zero. -/
theorem insertion_le_majorant (ell s0 s1 s2 a0 a1 a2 : ℝ) (b0 b1 b2 : Bool)
    (h0 : b0 = false → a0 = 0) (h1 : b1 = false → a1 = 0)
    (h2 : b2 = false → a2 = 0)
    (hp0 : b0 = true → a0 ≤ 1) (hp1 : b1 = true → a1 ≤ 1)
    (hp2 : b2 = true → a2 ≤ 1)
    (ht01 : b0 = true → b1 = true → a0 + a1 ≤ s2)
    (ht02 : b0 = true → b2 = true → a0 + a2 ≤ s1)
    (ht12 : b1 = true → b2 = true → a1 + a2 ≤ s0)
    (hfour : b0 = true → b1 = true → b2 = true → a0 + a1 + a2 ≤ 0) :
    a0 + a1 + a2 - ell * ((if b0 then 0 else 1) +
      (if b1 then 0 else 1) + (if b2 then 0 else 1)) ≤
        majorant ell s0 s1 s2 b0 b1 b2 := by
  cases b0 <;> cases b1 <;> cases b2 <;> simp_all [majorant] <;> linarith

/-- Universality identifies the missed-root pattern exactly with the
root region. The remaining positive coefficients are paid by the two
closed missing sections, keeping the signed root-region coefficient. -/
theorem majorant_le_universal_cover (ell u v : ℝ) (b0 b1 b2 : Bool) (i : Prop)
    [Decidable i] (h0 : b0 = false ↔ i) (h1 : i → b1 = true) (h2 : i → b2 = true)
    (hell : 0 ≤ ell) (hu : u ≤ 0) :
    majorant ell (u + v) (1 - v) (1 - u) b0 b1 b2 ≤
      (if i then u + v - ell else 0) +
        (if b1 = false then max (1 - ell - v) 0 else 0) +
        (if b2 = false then 1 - ell - u else 0) := by
  by_cases hi : i
  · have hb0 := h0.mpr hi
    simp [majorant, hi, hb0, h1 hi, h2 hi]
  · have hb0 : b0 = true := by cases b0 <;> simp_all
    cases b1 <;> cases b2 <;>
      simp only [majorant, hb0, hi, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, zero_add, add_zero]
    all_goals linarith [le_max_left (1 - ell - v) 0, le_max_right (1 - ell - v) 0]

/-- With one nonpositive root star, the universal-root capacity estimate
cannot exceed delta times the exterior mass. This includes negative
second stars and the exact threshold v=delta. -/
theorem nonpositive_star_capacity {A ell u v : ℝ}
    (hA : 1 / 3 ≤ A) (hell : 0 ≤ ell) (hu : u ≤ 0) (hv : v ≤ 1) :
    A * (u + v - ell) + (1 - 2 * A) *
      (max (1 - ell - v) 0 + (1 - ell - u)) ≤ (1 - ell) * (1 - A) := by
  have hcoef : 0 ≤ 3 * A - 1 := by linarith
  have hA0 : 0 ≤ A := by linarith
  by_cases h : 0 ≤ 1 - ell - v
  · rw [max_eq_left h]
    have ht : (3 * A - 1) * (u + v - (1 - ell)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoef (by linarith)
    nlinarith [mul_nonneg hA0 hell]
  · rw [max_eq_right (le_of_not_ge h)]
    have ht := mul_nonpos_of_nonneg_of_nonpos hcoef hu
    have hv' := mul_nonpos_of_nonneg_of_nonpos hA0 (sub_nonpos.mpr hv)
    nlinarith

end Erdos1017.TriangleInsertion
