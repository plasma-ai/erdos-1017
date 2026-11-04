module

public import Erdos1017.Multipartite.TightCounts
public import Mathlib.Tactic.FieldSimp

/-!
# Scalar contradiction on the one-exterior boundary

This module defines the `repeatCharge` of the child with one independent
exterior part, shows the adjacent-contact family has a full repeat penalty paid
by one consecutive-integer gap, and derives a contradiction between that family,
an own slope above one half, the own stationary row and the first-moment lower
bound.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CoveredOneExterior

/-- The child with one independent exterior part permits arbitrarily
many copies of that part after paying its mutual repeat penalty. -/
def repeatCharge (t v d q D : ℝ) (r n : ℕ) : ℝ :=
  (r : ℝ) * t + (n : ℝ) * v - D * (r : ℝ) * ((r : ℝ) - 1) / 2 -
    d * (r : ℝ) * (n : ℝ) - q * (n : ℝ) * ((n : ℝ) - 1) / 2

/-- The adjacent-contact family has a genuine full repeat penalty.
Every natural copy count is paid by the same consecutive-integer gap. -/
theorem integer_family_repeat_feasible (j k : ℕ) (hj : 0 < j) (hkj : k ≤ j)
    (r n : ℕ) :
    repeatCharge (1 - (k : ℝ) * ((k : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)))
      (2 * (j : ℝ) / ((j : ℝ) * ((j : ℝ) + 1)))
      (2 * ((j : ℝ) - k) / ((j : ℝ) * ((j : ℝ) + 1)))
      (2 / ((j : ℝ) * ((j : ℝ) + 1)))
      (2 * ((j : ℝ) - k) ^ 2 / ((j : ℝ) * ((j : ℝ) + 1))) r n ≤ 1 := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hJ : 0 < (j : ℝ) * ((j : ℝ) + 1) := by positivity
  have hcast : ((j - k : ℕ) : ℝ) = (j : ℝ) - k := by
    exact Nat.cast_sub hkj
  have hgap := TightCounts.gap_nonneg j (n + (j - k) * r)
  push_cast at hgap
  rw [hcast] at hgap
  apply (mul_le_mul_iff_of_pos_right hJ).mp
  unfold repeatCharge
  field_simp [ne_of_gt hJ]
  nlinarith only [hgap]

/-- The one-exterior-part boundary cannot have the adjacent-contact
family, its own slope above one half, its own stationary row and the
first-moment lower bound on the same child cost law. -/
theorem integer_family_row_contradiction (j k : ℕ) (hk : 1 ≤ k) (hkj : k < j)
    {ell b e : ℝ} (hell : 1 / 2 < ell) (hb : 0 < b)
    (hfirst : (k : ℝ) * b ≤ e)
    (hrow : b * ((k : ℝ) * ((k : ℝ) + 1)) =
      e * ((j : ℝ) * ((j : ℝ) + 1) * ell - 2 * ((j : ℝ) - k)))
    (hrepeat : ell < 2 * ((j : ℝ) - k) ^ 2 / ((j : ℝ) * ((j : ℝ) + 1))) : False := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hjr : (k : ℝ) < j := by exact_mod_cast hkj
  have hj0 : (0 : ℝ) < j := by linarith
  have hJ : 0 < (j : ℝ) * ((j : ℝ) + 1) := by positivity
  have hrep := (lt_div_iff₀ hJ).mp hrepeat
  rcases le_or_gt j (2 * k) with hhalf | hhalf
  · have hhalf' : (j : ℝ) ≤ 2 * k := by exact_mod_cast hhalf
    have hprod := mul_nonneg
      (show 0 ≤ (j : ℝ) - 2 * ((j : ℝ) - k) by linarith)
      (show 0 ≤ (j : ℝ) + 2 * ((j : ℝ) - k) by linarith)
    have hslope := mul_pos (show 0 < ell - 1 / 2 by linarith) hJ
    nlinarith only [hrep, hprod, hslope, hjr, hkr]
  · have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast (show 3 ≤ j by omega)
    have he : 0 < e := by nlinarith [mul_pos (show (0 : ℝ) < k by linarith) hb]
    have hK : 0 < b * ((k : ℝ) * ((k : ℝ) + 1)) := by positivity
    have hden : 0 < (j : ℝ) * ((j : ℝ) + 1) * ell - 2 * ((j : ℝ) - k) := by
      exact (pos_iff_pos_of_mul_pos (hrow ▸ hK)).mp he
    have hmul := mul_le_mul_of_nonneg_right hfirst hden.le
    rw [← hrow] at hmul
    have hcancel : (k : ℝ) *
        ((j : ℝ) * ((j : ℝ) + 1) * ell - 2 * ((j : ℝ) - k)) ≤
        (k : ℝ) * ((k : ℝ) + 1) := by
      apply (mul_le_mul_iff_of_pos_left hb).mp
      nlinarith only [hmul]
    have hbound : (j : ℝ) * ((j : ℝ) + 1) * ell ≤ 2 * j - k + 1 := by
      have hc := (mul_le_mul_iff_of_pos_left (show (0 : ℝ) < k by linarith)).mp hcancel
      linarith only [hc]
    have hquadratic := mul_nonneg (show (0 : ℝ) ≤ j by linarith)
      (show 0 ≤ (j : ℝ) - 3 by linarith)
    have hslope := mul_pos (show 0 < ell - 1 / 2 by linarith) hJ
    nlinarith only [hbound, hquadratic, hslope, hkr]

/-- The same contradiction in the original coefficient and row variables;
clearing the family denominator is part of the proof. -/
theorem contradiction_of_stationary_row (j k : ℕ) (hk : 1 ≤ k) (hkj : k < j)
    {t d ell b e : ℝ} (hell : 1 / 2 < ell) (hb : 0 < b)
    (hfirst : (k : ℝ) * b ≤ e)
    (ht : t = 1 - (k : ℝ) * ((k : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)))
    (hd : d = 2 * ((j : ℝ) - k) / ((j : ℝ) * ((j : ℝ) + 1)))
    (hrow : b * (1 - t) = e * (ell - d))
    (hrepeat : ell < 2 * ((j : ℝ) - k) ^ 2 / ((j : ℝ) * ((j : ℝ) + 1))) : False := by
  have hj : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hJ : (j : ℝ) * ((j : ℝ) + 1) ≠ 0 := by positivity
  have hscaled : b * ((k : ℝ) * ((k : ℝ) + 1)) =
      e * ((j : ℝ) * ((j : ℝ) + 1) * ell - 2 * ((j : ℝ) - k)) := by
    rw [ht, hd] at hrow
    field_simp [hJ] at hrow
    nlinarith only [hrow]
  exact integer_family_row_contradiction j k hk hkj hell hb hfirst hscaled hrepeat

end Erdos1017.CoveredOneExterior
