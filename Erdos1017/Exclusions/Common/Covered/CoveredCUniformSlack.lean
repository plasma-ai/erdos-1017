module

public import Erdos1017.Exclusions.Common.Covered.CoveredRepeatWitness

/-!
# Uniform count slack for the secondary C part

This module defines the rooted count charge `countCharge` with one secondary
independent part, shows that the three penalty floors give uniform slack at
every natural count, so the star/penalty edit is feasible on a two-sided
interval, and derives the mass balance from optimality.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CoveredC

/-- The rooted count charge with one secondary independent part. The two
linear incidences are the old root stars minus the secondary penalties. -/
def countCharge (t a b p q r : ℝ) (k l : ℕ) : ℝ :=
  t + k * a + l * b - p * k * ((k : ℝ) - 1) / 2 -
    q * l * ((l : ℝ) - 1) / 2 - r * k * l

private theorem nat_pair_nonneg (k : ℕ) : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
  by_cases hk : k = 0
  · simp [hk]
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    exact mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hk1)

/-- The three actual penalty floors give a uniform slack at every
natural count; no finite-active-set or supplied slack estimate is used. -/
theorem uniform_count_slack (t a b p q r s0 m0 : ℝ) (k l : ℕ)
    (ht : t = 1 - s0) (ha : a ≤ s0) (hb : b ≤ s0)
    (hp : m0 ≤ p) (hq : m0 ≤ q) (hr : m0 ≤ r) :
    ((k : ℝ) + l - 1) * (m0 * ((k : ℝ) + l) / 2 - s0) ≤
      1 - countCharge t a b p q r k l := by
  have hpa := mul_nonneg (sub_nonneg.mpr hp) (nat_pair_nonneg k)
  have hqa := mul_nonneg (sub_nonneg.mpr hq) (nat_pair_nonneg l)
  have hra := mul_nonneg (sub_nonneg.mpr hr)
    (mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (Nat.cast_nonneg l))
  have hka := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sub_nonneg.mpr ha)
  have hlb := mul_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l) (sub_nonneg.mpr hb)
  unfold countCharge
  nlinarith

/-- The simultaneous star/penalty edit has a concrete two-sided interval
paying every count, including zero, one, and arbitrarily large counts. -/
theorem countCharge_perturb_le_one (t a b p q r s0 m0 : ℝ)
    (ht : t = 1 - s0) (hs0 : 0 < s0) (hm0 : s0 < m0)
    (ha : a ≤ s0) (hb : b ≤ s0) (hp : m0 ≤ p) (hq : m0 ≤ q) (hr : m0 ≤ r)
    (eps : ℝ) (heps : |eps| ≤ min s0 (m0 - s0)) (k l : ℕ) :
    countCharge (t + eps) (a - eps) (b - eps) p q r k l ≤ 1 := by
  have heps0 : eps ≤ s0 := (le_abs_self eps).trans (heps.trans (min_le_left _ _))
  have hepsLow : -(m0 - s0) ≤ eps :=
    (neg_le_neg (heps.trans (min_le_right _ _))).trans (neg_abs_le eps)
  by_cases hzero : k + l = 0
  · have hk : k = 0 := by omega
    have hl : l = 0 := by omega
    simp only [countCharge, hk, hl, Nat.cast_zero, zero_mul, mul_zero, zero_div,
      add_zero, sub_zero]
    linarith
  by_cases hone : k + l = 1
  · rcases (show (k = 1 ∧ l = 0) ∨ (k = 0 ∧ l = 1) by omega) with h | h
    · obtain ⟨rfl, rfl⟩ := h
      simp only [countCharge, Nat.cast_zero, Nat.cast_one, one_mul, zero_mul,
        sub_self, mul_zero, zero_div, add_zero, sub_zero]
      linarith
    · obtain ⟨rfl, rfl⟩ := h
      simp only [countCharge, Nat.cast_zero, Nat.cast_one, one_mul, zero_mul,
        sub_self, mul_zero, zero_div, add_zero, sub_zero]
      linarith
  have hn : (2 : ℝ) ≤ (k : ℝ) + l := by exact_mod_cast (show 2 ≤ k + l by omega)
  have hn0 : 0 ≤ (k : ℝ) + l - 1 := by linarith
  have hm0pos : 0 ≤ m0 := by linarith
  have hgap := mul_nonneg hm0pos (show 0 ≤ (k : ℝ) + l - 2 by linarith)
  have hfactor : m0 - s0 ≤ m0 * ((k : ℝ) + l) / 2 - s0 := by nlinarith
  have hpay := mul_le_mul_of_nonneg_left hfactor hn0
  have hslack := uniform_count_slack t a b p q r s0 m0 k l ht ha hb hp hq hr
  have hmove := mul_le_mul_of_nonneg_right hepsLow hn0
  have heq : countCharge (t + eps) (a - eps) (b - eps) p q r k l =
      countCharge t a b p q r k l - eps * ((k : ℝ) + l - 1) := by
    unfold countCharge
    ring
  rw [heq]
  nlinarith

/-- Actual optimality on both signs of a nonzero perturbation interval
forces the mass balance given by its exact objective slope. -/
theorem mass_balance_of_perturb_optimal (b u e cell radius : ℝ)
    (hcell : 0 < cell) (hradius : 0 < radius)
    (hopt : ∀ eps : ℝ, |eps| ≤ radius → eps * cell * (b - u - e) ≤ 0) :
    b = u + e := by
  have hpos := hopt radius (by rw [abs_of_pos hradius])
  have hneg := hopt (-radius) (by rw [abs_neg, abs_of_pos hradius])
  have hzero : radius * cell * (b - u - e) = 0 := by nlinarith
  have hnonzero : radius * cell ≠ 0 := ne_of_gt (mul_pos hradius hcell)
  have heq := (mul_eq_zero.mp hzero).resolve_left hnonzero
  linarith

/-- The balanced original rows contradict a strictly larger E star.
Every mass, row equality, and triangle bound is kept explicit. -/
theorem not_balanced_rows (b u e s0 h z ell v d : ℝ)
    (hu : 0 ≤ u) (he : 0 < e) (hmass : b = u + e)
    (hrow : b * s0 = u * (h - z) + e * (ell - d))
    (hR : h - z ≤ s0) (hE : v - d ≤ s0) (hv : ell < v) : False := by
  rw [hmass] at hrow
  have h₁ := mul_le_mul_of_nonneg_left hR hu
  have h₂ := mul_le_mul_of_nonneg_left hE he.le
  have hstrict := mul_pos he (sub_pos.mpr hv)
  nlinarith

end Erdos1017.CoveredC
