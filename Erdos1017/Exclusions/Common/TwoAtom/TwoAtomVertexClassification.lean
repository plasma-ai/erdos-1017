module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBoundaryThird

/-!
# Vertex classification of the two-atom count system

This module defines the remaining integer family with its whole tight support
and shows that vertex geometry, own guards and a scalar contact leave exactly
one such family; the all-count classification then constructs the `h`-maximizing
optimal vertex and its integer family.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- The derived remaining integer family and its entire actual tight support. -/
structure IntegerFamily (x : Coefficients) where
  index : ℕ
  index_ge_three : 3 ≤ index
  h_eq : x 0 = 2 * (index : ℝ) / ((index : ℝ) * ((index : ℝ) + 1))
  p_eq : x 2 = 2 / ((index : ℝ) * ((index : ℝ) + 1))
  r_eq : x 4 = 2 * ((index : ℝ) - 1) / ((index : ℝ) * ((index : ℝ) + 1))
  v_eq : x 1 = 1 - 2 / ((index : ℝ) * ((index : ℝ) + 1))
  q_eq : x 3 = 1 - 4 / ((index : ℝ) * ((index : ℝ) + 1))
  tight : ∀ k l, countTest k l x = 1 ↔
    (k = index ∧ l = 0) ∨ (k = index + 1 ∧ l = 0) ∨
      (k = 1 ∧ l = 1) ∨ (k = 2 ∧ l = 1) ∨ (k = 0 ∧ l = 2)

/-- Genuine vertex geometry, own guards and an actual scalar contact
leave exactly one derived integer family; every boundary is paid. -/
theorem integer_family_of_vertex_contact (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (ell : ℝ) (hg : OwnCountGuards x ell)
    (hcontact : ∃ l, countTest 0 l x = 1) : Nonempty (IntegerFamily x) := by
  have hx := hvertex.1
  rcases smallest_scalar_contact_two_or_three x hx ell hg.ell_half hg.q_lt_ell hg.ell_lt_v
      hcontact with ⟨hqlo, hv, htwo⟩ | ⟨hqlo, hqhi, hv, hthree⟩
  · have hrle := contact_two_r_lower x hx htwo
    rcases lt_or_eq_of_le hrle with hr | hr
    · rcases eq_or_lt_of_le hqlo with hq | hq
      · have hvthird : x 1 = 2 / 3 := by rw [← hq] at hv; linarith
        exact False.elim (not_vertex_contact_two_third_strict x hx ell hg hvthird hr hvertex)
      · obtain ⟨j, hj, hh, hp, hr, hv, hq, ht⟩ :=
          strict_contact_two_integer_family x hvertex ell hg hq hv htwo hr
        exact ⟨⟨j, hj, hh, hp, hr, hv, hq, ht⟩⟩
    · rcases eq_or_lt_of_le hqlo with hq | hq
      · have hvthird : x 1 = 2 / 3 := by rw [← hq] at hv; linarith
        exact False.elim (not_vertex_contact_two_third_boundary x hx ell hg hvthird htwo hr hvertex)
      · exact False.elim
          (not_vertex_contact_two_boundary_strict_q x hx ell hg hq hv htwo hr hvertex)
  · exact False.elim
      (not_vertex_of_scalar_contact_three x hx ell hg hqlo hqhi hv hthree hvertex)

/-- The all-count classification constructs its actual h-maximizing
optimal vertex and its integer family. Only each active dual's own guards
remain numeric hypotheses. -/
theorem exists_h_maximizing_integer_family {a b u e V : ℝ}
    (hab : a < b) (hb : 0 < b) (hu : 0 < u) (he : 0 < e) (hbu : u < b)
    (hentry : ∃ x ∈ optimalFace a b u e V, 0 < x 0)
    (hmax : ∀ x ∈ feasible, objective a b u e x ≤ V)
    (hown : ∀ x ∈ optimalFace a b u e V, 0 < x 0 → ∃ ell, OwnCountGuards x ell) :
    ∃ x ∈ feasible.extremePoints ℝ, objective a b u e x = V ∧
      (∀ y ∈ optimalFace a b u e V, y 0 ≤ x 0) ∧
      ∃ ell, OwnCountGuards x ell ∧ Nonempty (IntegerFamily x) := by
  obtain ⟨x₀, hx₀, hh₀⟩ := hentry
  obtain ⟨x, hx, hobj, hH⟩ := exists_h_maximizing_optimal_vertex hab hb hu he ⟨x₀, hx₀⟩ hmax
  have hh : 0 < x 0 := hh₀.trans_le (hH x₀ hx₀)
  obtain ⟨ell, hg⟩ := hown x ⟨hx.1, hobj⟩ hh
  have hcontact := exists_scalar_axis_contact_of_optimal hbu he x hx.1 hg.positive
    (fun y hy => (hmax y hy).trans_eq hobj.symm)
  exact ⟨x, hx, hobj, hH, ell, hg, integer_family_of_vertex_contact x hx ell hg hcontact⟩

end Erdos1017.TwoAtomCountGate
