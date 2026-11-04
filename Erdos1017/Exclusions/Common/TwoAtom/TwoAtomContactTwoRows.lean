module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomContactThree

/-!
# Tight rows at contact two

Adding one `R` to a scalar `E₂` contact gives `r ≥ h/2`, the only mixed `l = 2`
contact is `(1,2)` and forces `r = h/2`, higher mixed rows are slack, and on
`q = 1/3` with `r > h/2` only axis rows remain.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- Adding one R to an actual scalar E2 contact gives r>=h/2. -/
theorem contact_two_r_lower (x : Coefficients) (hx : x ∈ feasible)
    (hcontact : countTest 0 2 x = 1) : x 0 ≤ 2 * x 4 := by
  have h12 := hx.2.2.1 1 2
  norm_num [countTest_apply] at hcontact h12
  linarith

/-- Scalar E2 has only the two displayed possible old integer contacts. -/
theorem contact_two_axis_support (x : Coefficients) (hx : x ∈ feasible)
    (hqlo : 1 / 3 ≤ x 3) (hqhi : x 3 < 1) (hv : x 1 = (1 + x 3) / 2)
    (hcontact : countTest 0 2 x = 1) (l : ℕ) (hl : countTest 0 l x = 1) :
    l = 2 ∨ (l = 3 ∧ x 3 = 1 / 3) := by
  have hp : 0 < x 3 := by linarith
  have hline (n : ℕ) : countTest 0 n x = TightCounts.value 0 (x 1) (x 3) n := by
    rw [countTest_apply]
    unfold TightCounts.value
    ring
  have hfeas (n : ℕ) : TightCounts.value 0 (x 1) (x 3) n ≤ 1 := by
    rw [← hline]
    exact hx.2.2.1 0 n
  rcases lt_trichotomy l 2 with h | h | h
  · have hadj := TightCounts.tight_counts_adjacent 0 (x 1) (x 3) hp hfeas l 2 h
      (by rwa [← hline]) (by rwa [← hline])
    have hl1 : l = 1 := by omega
    norm_num [hl1, countTest_apply] at hl
    linarith
  · exact Or.inl h
  · have hadj := TightCounts.tight_counts_adjacent 0 (x 1) (x 3) hp hfeas 2 l h
      (by rwa [← hline]) (by rwa [← hline])
    right
    refine ⟨hadj, ?_⟩
    norm_num [hadj, countTest_apply] at hl
    linarith

/-- The only possible mixed l=2 contact is (1,2), and it forces the
r=h/2 boundary. No mixed count list is supplied. -/
theorem contact_two_mixed_two_tight (x : Coefficients) (hx : x ∈ feasible)
    (hp : 0 < x 2) (hcontact : countTest 0 2 x = 1) (k : ℕ) (hk : 0 < k)
    (htight : countTest k 2 x = 1) : k = 1 ∧ x 0 = 2 * x 4 := by
  have hr := contact_two_r_lower x hx hcontact
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hdiff := mul_nonneg (sub_nonneg.mpr hr) (Nat.cast_nonneg k)
  have hk1 : k = 1 := by
    by_contra h
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    have hbin : 0 < (k : ℝ) * ((k : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    have hpen := mul_pos hp hbin
    norm_num [countTest_apply] at htight hcontact
    nlinarith only [hpen, hdiff, htight, hcontact]
  refine ⟨hk1, ?_⟩
  norm_num [hk1, countTest_apply] at htight hcontact
  linarith

/-- Every mixed E count at least three is strictly slack at contact two. -/
theorem contact_two_high_rows_slack (x : Coefficients) (hx : x ∈ feasible) (ell : ℝ)
    (hg : OwnCountGuards x ell) (hcontact : countTest 0 2 x = 1) (k l : ℕ)
    (hk : 0 < k) (hl : 3 ≤ l) : countTest k l x < 1 := by
  have hr := contact_two_r_lower x hx hcontact
  have hr3 : x 0 < 3 * x 4 := by nlinarith [hg.h_pos]
  exact contact_three_high_rows_slack x hx ell hg hr3 k l hk hl

/-- On q=1/3 the strict r>h/2 regime has no tight mixed row. The
potential l=1 rows are paid by the old R count at 2k-1. -/
theorem contact_two_third_strict_mixed_slack (x : Coefficients) (hx : x ∈ feasible)
    (ell : ℝ) (hg : OwnCountGuards x ell)
    (hv : x 1 = 2 / 3) (hr : x 0 < 2 * x 4)
    (k l : ℕ) (hk : 0 < k) (hl : 0 < l) : countTest k l x < 1 := by
  have hkn : 0 < (k : ℝ) := by exact_mod_cast hk
  have hp := hg.positive 2
  by_cases hl1 : l = 1
  · subst l
    have hbase : (k : ℝ) * x 0 / 2 - x 2 * k * ((k : ℝ) - 1) / 2 ≤ 1 / 3 := by
      by_cases hk1 : k = 1
      · norm_num [hk1]
        linarith [hg.h_lt_ell, hg.ell_lt_v]
      · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
        have hc := hx.2.2.1 (2 * k - 1) 0
        have hcast : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
        norm_num [countTest_apply, hcast] at hc
        by_cases hs : 0 ≤ x 0 - x 2 * ((k : ℝ) - 1)
        · have hscale := mul_nonneg hs (show 0 ≤ (k : ℝ) / 2 - 1 by linarith)
          nlinarith only [hc, hscale]
        · have hneg := mul_nonpos_of_nonneg_of_nonpos hkn.le (le_of_not_ge hs)
          nlinarith only [hneg]
    have hstrict := mul_pos hkn (sub_pos.mpr hr)
    norm_num [countTest_apply, hv] at ⊢
    nlinarith only [hbase, hstrict]
  · have hln : (2 : ℝ) ≤ l := by exact_mod_cast (show 2 ≤ l by omega)
    have hlr := mul_nonneg (hg.positive 4).le (sub_nonneg.mpr hln)
    have hneg : x 0 - x 4 * l < 0 := by nlinarith only [hr, hlr]
    have hstrict := mul_neg_of_pos_of_neg hkn hneg
    have hbin : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
      simpa using TightCounts.gap_nonneg 0 k
    have hpen := mul_nonneg hp.le hbin
    have haxis := hx.2.2.1 0 l
    rw [countTest_apply] at haxis ⊢
    norm_num only [Nat.cast_zero, zero_mul, mul_zero, sub_zero, zero_add] at haxis
    nlinarith only [haxis, hstrict, hpen]

/-- q=1/3 with strict r>h/2 leaves only axis rows, which cannot span
five coordinates. The actual r-only direction witnesses the failure. -/
theorem not_vertex_contact_two_third_strict (x : Coefficients) (hx : x ∈ feasible)
    (ell : ℝ) (hg : OwnCountGuards x ell)
    (hv : x 1 = 2 / 3) (hr : x 0 < 2 * x 4) : x ∉ feasible.extremePoints ℝ := by
  intro hvertex
  let v : Coefficients := ![0, 0, 0, 0, 1]
  have heq := active_direction_eq_zero x hvertex hg.positive v (by
    intro k l ht
    have haxis : k = 0 ∨ l = 0 := by
      by_contra h
      push Not at h
      have hs := contact_two_third_strict_mixed_slack x hx ell hg hv hr k l
        (Nat.pos_of_ne_zero h.1) (Nat.pos_of_ne_zero h.2)
      linarith only [hs, ht]
    rcases haxis with h | h <;> subst_vars <;> norm_num [v, countTest_apply])
  have h := congrFun heq 4
  norm_num [v] at h

end Erdos1017.TwoAtomCountGate
