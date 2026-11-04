module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomAxisContact

/-!
# Positivity of the two-atom penalties

From all-count tests, `h > 0` forces a positive `R` penalty, a zero `E` penalty
forces `v ≤ 0` and `r ≥ 0`, and a positive own `E` row excludes `q = 0`; with
global optimality this builds the positive coefficient vector and a finite
scalar contact.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- A genuinely all-count linear bound has nonpositive slope. -/
theorem nonpos_of_all_nat_linear_tests (s : ℝ) (hs : ∀ n : ℕ, (n : ℝ) * s ≤ 1) : s ≤ 0 := by
  by_contra h
  have hs0 : 0 < s := lt_of_not_ge h
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / s)
  have hlarge := (div_lt_iff₀ hs0).mp hn
  linarith [hs n]

/-- h>0 forces a positive R penalty from genuine unbounded R-axis tests. -/
theorem p_pos_of_h_pos (x : Coefficients) (hx : x ∈ feasible) (hh : 0 < x 0) : 0 < x 2 := by
  by_contra h
  have hp0 : x 2 = 0 := le_antisymm (le_of_not_gt h) hx.1
  have hs := nonpos_of_all_nat_linear_tests (x 0) (fun n => by
    have ht := hx.2.2.1 n 0
    simpa [countTest_apply, hp0, mul_comm] using ht)
  linarith

/-- A zero E penalty makes the actual BE slope nonpositive. -/
theorem v_nonpos_of_q_zero (x : Coefficients) (hx : x ∈ feasible) (hq : x 3 = 0) : x 1 ≤ 0 :=
  nonpos_of_all_nat_linear_tests (x 1) (fun n => by
    simpa [countTest_apply, hq, mul_comm] using hx.2.2.1 0 n)

/-- A zero E penalty makes the actual cross penalty nonnegative, using
unanchored R+lE tests; no prior r sign is assumed. -/
theorem r_nonneg_of_q_zero (x : Coefficients) (hx : x ∈ feasible) (hq : x 3 = 0) : 0 ≤ x 4 := by
  have hs := nonpos_of_all_nat_linear_tests (-x 4) (fun n => by
    simpa [unanchoredTest_apply, hq, mul_comm] using hx.2.2.2.1 1 n)
  linarith

/-- The actual positive E charge row excludes q=0 without a contact or
an r floor, because both signs follow from original all-count tests. -/
theorem q_pos_of_positive_E_charge_row (x : Coefficients) (hx : x ∈ feasible)
    {b u e : ℝ} (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hE : 0 < b * x 1 - x 4 * u - x 3 * e) : 0 < x 3 := by
  by_contra h
  have hq : x 3 = 0 := le_antisymm (le_of_not_gt h) hx.2.1
  have hv := v_nonpos_of_q_zero x hx hq
  have hr := r_nonneg_of_q_zero x hx hq
  have hB := mul_nonpos_of_nonneg_of_nonpos hb hv
  have hR := mul_nonneg hr hu
  rw [hq, zero_mul, sub_zero] at hE
  linarith

/-- A same own gamma/ell E-row gives its strict positivity from genuine
mass signs, then derives q>0 without a circular scalar contact premise. -/
theorem q_pos_of_own_E_row (x : Coefficients) (hx : x ∈ feasible)
    {a b u e ell gamma : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hell : 0 ≤ ell) (hgamma : 0 < gamma)
    (hrow : gamma + ell * a = b * x 1 - x 4 * u - x 3 * e) : 0 < x 3 := by
  apply q_pos_of_positive_E_charge_row x hx hb hu
  rw [← hrow]
  exact add_pos_of_pos_of_nonneg hgamma (mul_nonneg hell ha)

/-- Any real finite scalar-axis contact has v>0 by original q>=0. -/
theorem v_pos_of_scalar_axis_contact (x : Coefficients) (hx : x ∈ feasible)
    (hcontact : ∃ l, countTest 0 l x = 1) : 0 < x 1 := by
  obtain ⟨l, hl⟩ := hcontact
  have hbin : 0 ≤ (l : ℝ) * ((l : ℝ) - 1) := by
    simpa using TightCounts.gap_nonneg 0 l
  have hpen := mul_nonneg hx.2.1 hbin
  rw [countTest_apply] at hl
  norm_num only [Nat.cast_zero, mul_zero, zero_mul, sub_zero, zero_add] at hl
  by_contra h
  have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (Nat.cast_nonneg l)
  nlinarith only [hl, hpen, hprod]

/-- The physical own E-row and actual global optimality construct the
entire positive vector and a finite scalar contact in the correct order:
p,q positive first, then q-only contact, then r,v positive. -/
theorem positive_coefficients_and_contact_of_own_E_row
    {a b u e ell gamma : ℝ} (hbu : u < b) (he : 0 < e)
    (x : Coefficients) (hx : x ∈ feasible) (hh : 0 < x 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hell : 0 ≤ ell) (hgamma : 0 < gamma)
    (hrow : gamma + ell * a = b * x 1 - x 4 * u - x 3 * e)
    (hmax : ∀ y ∈ feasible, objective a b u e y ≤ objective a b u e x) :
    (∀ i, 0 < x i) ∧ ∃ l, countTest 0 l x = 1 := by
  have hp := p_pos_of_h_pos x hx hh
  have hq := q_pos_of_own_E_row x hx ha hb hu hell hgamma hrow
  have hcontact := exists_scalar_axis_contact_of_optimal_of_q_pos hbu he x hx hq hmax
  have hr := r_pos_of_scalar_axis_contact x hx hh hcontact
  have hv := v_pos_of_scalar_axis_contact x hx hcontact
  refine ⟨?_, hcontact⟩
  intro i
  fin_cases i
  · exact hh
  · exact hv
  · exact hp
  · exact hq
  · exact hr

end Erdos1017.TwoAtomCountGate
