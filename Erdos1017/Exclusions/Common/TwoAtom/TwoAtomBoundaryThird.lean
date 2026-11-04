module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBoundaryVertex

/-!
# Two-atom boundary at `q = 1/3` and `r = h/2`

On this boundary only the `R` counts two or three can be tight and the only
`l = 1` contact is `k = 2`, so active-row independence fails: the possible fifth
count normal is dependent, as explicit directions witness.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- At the boundary q=1/3,r=h/2, only R counts two or three may be tight. -/
theorem boundary_third_axis_support (x : Coefficients) (hx : x ∈ feasible)
    (ell : ℝ) (hg : OwnCountGuards x ell) (hv : x 1 = 2 / 3)
    (k : ℕ) (ht : countTest k 0 x = 1) : k = 2 ∨ k = 3 := by
  have hh : x 0 < 2 / 3 := hg.h_lt_ell.trans (by linarith [hg.ell_lt_v])
  have hp : 1 / 6 < x 2 := by linarith [hg.p_floor, hg.ell_lt_v]
  have hk0 : k ≠ 0 := by intro h; simp [h, countTest_apply] at ht
  have hk1 : k ≠ 1 := by
    intro h
    norm_num [h, countTest_apply] at ht
    linarith
  have hk3 : k ≤ 3 := by
    by_contra h
    have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast (show 4 ≤ k by omega)
    have hprev : TightCounts.value 0 (x 0) (x 2) (k - 1) ≤ 1 := by
      simpa [countTest_eq_line] using hx.2.2.1 (k - 1) 0
    have ht' : TightCounts.value 0 (x 0) (x 2) k = 1 := by
      simpa [countTest_eq_line] using ht
    have hpen := penalty_bound_of_tight 0 (x 0) (x 2) k (by omega) hprev ht'
    have hprod : (12 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod (hg.positive 2).le
    nlinarith only [hp, hpen, hmul]
  omega

/-- At q=1/3,r=h/2, the only possible l=1 contact is k=2. -/
theorem boundary_third_one_support (x : Coefficients) (hx : x ∈ feasible)
    (ell : ℝ) (hg : OwnCountGuards x ell) (hv : x 1 = 2 / 3) (hr : x 0 = 2 * x 4)
    (k : ℕ) (ht : countTest k 1 x = 1) : k = 2 := by
  have hh : x 0 < 2 / 3 := hg.h_lt_ell.trans (by linarith [hg.ell_lt_v])
  have hp : 1 / 6 < x 2 := by linarith [hg.p_floor, hg.ell_lt_v]
  have hk0 : k ≠ 0 := by
    intro h
    norm_num [h, countTest_apply] at ht
    linarith
  have hk1 : k ≠ 1 := by
    intro h
    norm_num [h, countTest_apply] at ht
    linarith
  have hk2 : k ≤ 2 := by
    by_contra h
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
    have hprev : TightCounts.value (x 1) (x 0 - x 4) (x 2) (k - 1) ≤ 1 := by
      simpa [countTest_eq_line] using hx.2.2.1 (k - 1) 1
    have ht' : TightCounts.value (x 1) (x 0 - x 4) (x 2) k = 1 := by
      simpa [countTest_eq_line] using ht
    have hpen := penalty_bound_of_tight (x 1) (x 0 - x 4) (x 2) k (by omega) hprev ht'
    have hprod : (6 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod (hg.positive 2).le
    nlinarith only [hp, hpen, hmul, hv]
  omega

/-- The q=1/3,r=h/2 boundary fails genuine active-row independence.
Its potentially fifth count normal is dependent; actual directions witness it. -/
theorem not_vertex_contact_two_third_boundary (x : Coefficients)
    (hx : x ∈ feasible) (ell : ℝ) (hg : OwnCountGuards x ell)
    (hv : x 1 = 2 / 3) (hcontact : countTest 0 2 x = 1) (hr : x 0 = 2 * x 4) :
    x ∉ feasible.extremePoints ℝ := by
  have hh : x 0 < 2 / 3 := hg.h_lt_ell.trans (by linarith [hg.ell_lt_v])
  have hboth : ¬(countTest 2 0 x = 1 ∧ countTest 3 0 x = 1) := by
    rintro ⟨h2, h3⟩
    norm_num [countTest_apply] at h2 h3
    linarith
  have hR2L : countTest 2 0 x = 1 → ∀ k, countTest k 1 x ≠ 1 := by
    intro h2 k hk
    have hkeq := boundary_third_one_support x hx ell hg hv hr k hk
    subst k
    norm_num [countTest_apply] at h2 hk
    linarith
  intro hvertex
  by_cases hR2 : countTest 2 0 x = 1
  · let v : Coefficients := ![2, 0, 4, 0, 1]
    have hzero := active_direction_eq_zero x hvertex hg.positive v (by
      intro k l ht
      by_cases hk : k = 0
      · subst k
        norm_num [v, countTest_apply]
      · by_cases hl0 : l = 0
        · subst l
          rcases boundary_third_axis_support x hx ell hg hv k ht with h | h
          · subst k
            norm_num [v, countTest_apply]
          · exact False.elim (hboth ⟨hR2, h ▸ ht⟩)
        · by_cases hl1 : l = 1
          · subst l
            exact False.elim (hR2L hR2 k ht)
          · by_cases hl2 : l = 2
            · subst l
              have hkeq := (contact_two_mixed_two_tight x hx (hg.positive 2) hcontact k
                (Nat.pos_of_ne_zero hk) ht).1
              subst k
              norm_num [v, countTest_apply]
            · have hs := contact_two_high_rows_slack x hx ell hg hcontact k l
                (Nat.pos_of_ne_zero hk) (by omega)
              linarith only [hs, ht])
    have h := congrFun hzero 4
    norm_num [v] at h
  · let v : Coefficients := ![2, 0, 2, 0, 1]
    have hzero := active_direction_eq_zero x hvertex hg.positive v (by
      intro k l ht
      by_cases hk : k = 0
      · subst k
        norm_num [v, countTest_apply]
      · by_cases hl0 : l = 0
        · subst l
          rcases boundary_third_axis_support x hx ell hg hv k ht with h | h
          · exact False.elim (hR2 (h ▸ ht))
          · subst k
            norm_num [v, countTest_apply]
        · by_cases hl1 : l = 1
          · subst l
            have hkeq := boundary_third_one_support x hx ell hg hv hr k ht
            subst k
            norm_num [v, countTest_apply]
          · by_cases hl2 : l = 2
            · subst l
              have hkeq := (contact_two_mixed_two_tight x hx (hg.positive 2) hcontact k
                (Nat.pos_of_ne_zero hk) ht).1
              subst k
              norm_num [v, countTest_apply]
            · have hs := contact_two_high_rows_slack x hx ell hg hcontact k l
                (Nat.pos_of_ne_zero hk) (by omega)
              linarith only [hs, ht])
    have h := congrFun hzero 4
    norm_num [v] at h

end Erdos1017.TwoAtomCountGate
