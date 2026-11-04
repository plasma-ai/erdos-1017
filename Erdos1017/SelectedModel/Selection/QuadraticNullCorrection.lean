module

public import Erdos1017.Models.Selection.QuadraticConstraint

/-!
# Implicit correction for a quadratic density constraint

The branch `nullCorrection` solves a quadratic density equation exactly near
zero, and a polynomial with only linear and quadratic terms vanishing on a
neighborhood has zero coefficients, so positive transverse shifted cost and
local optimality force both density coefficients of a null direction to vanish.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Erdos1017.Variation

/-- The small implicit branch for a quadratic density constraint with a
possibly nonzero first variation in its original direction. -/
def nullCorrection (l a b c d t : ℝ) : ℝ :=
  -2 * (l * t + a * t ^ 2) /
    (b + 2 * c * t + Real.sqrt ((b + 2 * c * t) ^ 2 - 4 * d * (l * t + a * t ^ 2)))

@[simp] theorem nullCorrection_zero (l a b c d : ℝ) :
    nullCorrection l a b c d 0 = 0 := by
  simp [nullCorrection]

theorem nullCorrection_continuousAt_zero (l a b c d : ℝ) (hb : 0 < b) :
    ContinuousAt (nullCorrection l a b c d) 0 := by
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, sub_zero,
      Real.sqrt_sq hb.le]
    linarith

/-- The explicitly constructed branch solves the complete density
equation exactly near zero; no correction path is a hypothesis. -/
theorem nullCorrection_solves_eventually (l a b c d : ℝ) (hb : 0 < b) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      l * t + a * t ^ 2 + (b + 2 * c * t) * nullCorrection l a b c d t +
        d * (nullCorrection l a b c d t) ^ 2 = 0 := by
  have hdisc : Continuous (fun t : ℝ =>
      (b + 2 * c * t) ^ 2 - 4 * d * (l * t + a * t ^ 2)) := by fun_prop
  have hd : ∀ᶠ t in 𝓝 (0 : ℝ),
      0 < (b + 2 * c * t) ^ 2 - 4 * d * (l * t + a * t ^ 2) :=
    hdisc.continuousAt.eventually (lt_mem_nhds (by simpa using sq_pos_of_pos hb))
  have hden : Continuous (fun t : ℝ => b + 2 * c * t +
      Real.sqrt ((b + 2 * c * t) ^ 2 - 4 * d * (l * t + a * t ^ 2))) := by fun_prop
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), b + 2 * c * t +
      Real.sqrt ((b + 2 * c * t) ^ 2 - 4 * d * (l * t + a * t ^ 2)) ≠ 0 := by
    apply hden.continuousAt.eventually_ne
    simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, sub_zero,
      Real.sqrt_sq hb.le]
    linarith
  filter_upwards [hd, hn] with t ht hne
  have hs := Real.sq_sqrt ht.le
  dsimp only [nullCorrection]
  generalize hr : Real.sqrt ((b + 2 * c * t) ^ 2 - 4 * d * (l * t + a * t ^ 2)) = r
    at hs hne ⊢
  generalize hq : b + 2 * c * t = q at hs hne ⊢
  field_simp [hne]
  linear_combination (l * t + a * t ^ 2) * hs

/-- A polynomial with only linear and quadratic terms that vanishes on
a neighborhood has both coefficients zero. -/
theorem linear_quadratic_coefficients_eq_zero (l a : ℝ)
    (hzero : ∀ᶠ t in 𝓝 (0 : ℝ), l * t + a * t ^ 2 = 0) : l = 0 ∧ a = 0 := by
  obtain ⟨ε, hε, hpoly⟩ := Metric.eventually_nhds_iff.mp hzero
  have hpd : dist (ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have hnd : dist (-ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith)]
    linarith
  have hp : l * (ε / 2) + a * (ε / 2) ^ 2 = 0 := hpoly hpd
  have hn : l * (-ε / 2) + a * (-ε / 2) ^ 2 = 0 := hpoly hnd
  have ha : a * ε ^ 2 = 0 := by nlinarith
  have ha0 : a = 0 := (mul_eq_zero.mp ha).resolve_right (sq_pos_of_pos hε).ne'
  have hl : l * ε = 0 := by rw [ha0] at hp; nlinarith
  exact ⟨(mul_eq_zero.mp hl).resolve_right hε.ne', ha0⟩

/-- Positive transverse shifted cost and actual local optimality force
both density coefficients of a null direction to vanish. The implicit
correction is constructed from the density polynomial internally. -/
theorem null_density_coefficients_eq_zero (l a b c d q : ℝ)
    (hb : 0 < b) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ t s : ℝ, |t| < ε → |s| < ε →
      l * t + a * t ^ 2 + (b + 2 * c * t) * s + d * s ^ 2 = 0 → q * s ^ 2 ≤ 0) :
    l = 0 ∧ a = 0 := by
  apply linear_quadratic_coefficients_eq_zero
  have hs := nullCorrection_continuousAt_zero l a b c d hb
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < ε :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  have hs' : ∀ᶠ t in 𝓝 (0 : ℝ), |nullCorrection l a b c d t| < ε :=
    hs.abs.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [ht, hs', nullCorrection_solves_eventually l a b c d hb] with t ht hs hroot
  have hcost := hmax t (nullCorrection l a b c d t) ht hs hroot
  have hsq : (nullCorrection l a b c d t) ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_right hcost hq
  have hs0 : nullCorrection l a b c d t = 0 :=
    sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
  simpa only [hs0, mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] using hroot

end Erdos1017.Variation
