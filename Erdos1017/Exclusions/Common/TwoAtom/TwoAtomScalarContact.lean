module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomCountActive

/-!
# Scalar contact of an optimal two-atom vector

This module defines the tilt that raises `BE` and the `RE` penalty together on
the full slice and shows that global optimality forces a finite scalar-axis
contact, whose smallest value is two or three under the strict own-floor guards.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- Raise BE and the RE penalty together on the genuine full slice. -/
def scalarTilt (x : Coefficients) (t : ℝ) : Coefficients := x + t • ![0, 1, 0, 0, 1]

theorem countTest_scalarTilt (x : Coefficients) (t : ℝ) (k l : ℕ) :
    countTest k l (scalarTilt x t) = countTest k l x + t * l * (1 - (k : ℝ)) := by
  simp [scalarTilt, countTest_apply, Matrix.vecHead, Matrix.vecTail]
  ring

theorem objective_scalarTilt (a b u e : ℝ) (x : Coefficients) (t : ℝ) :
    objective a b u e (scalarTilt x t) = objective a b u e x + e * (b - u) * t := by
  simp [objective_apply, scalarTilt, Matrix.vecHead, Matrix.vecTail]
  ring

/-- Genuine global optimality forces an actual finite scalar-axis contact.
The improving BE/RE tilt uses only all-count feasibility. -/
theorem exists_scalar_axis_contact_of_optimal {a b u e : ℝ} (hbu : u < b) (he : 0 < e)
    (x : Coefficients) (hx : x ∈ feasible) (hpos : ∀ i, 0 < x i)
    (hmax : ∀ y ∈ feasible, objective a b u e y ≤ objective a b u e x) :
    ∃ l : ℕ, countTest 0 l x = 1 := by
  by_contra hn
  push Not at hn
  obtain ⟨N, hN⟩ := local_finiteness x hpos
  have hcont : ContinuousAt (scalarTilt x) 0 := by
    unfold scalarTilt
    fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, (∀ i, 0 < scalarTilt x t i) ∧
      ∀ k l, N ≤ k ∨ N ≤ l → countTest k l (scalarTilt x t) < 1 := by
    have ht : Tendsto (scalarTilt x) (𝓝 0) (𝓝 x) := by simpa [scalarTilt] using hcont.tendsto
    exact ht.eventually hN
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ∀ l : Fin N, countTest 0 l.val (scalarTilt x t) < 1 := by
    apply Filter.eventually_all.mpr
    intro l
    have hl : countTest 0 l.val x < 1 := lt_of_le_of_ne (hx.2.2.1 0 l.val) (hn l.val)
    have hc : ContinuousAt (fun t => countTest 0 l.val (scalarTilt x t)) 0 := by
      exact (countTest 0 l.val).continuous_of_finiteDimensional.continuousAt.comp hcont
    have ht : Tendsto (fun t => countTest 0 l.val (scalarTilt x t)) (𝓝 0)
        (𝓝 (countTest 0 l.val x)) := by simpa [scalarTilt] using hc.tendsto
    exact ht.eventually_lt_const hl
  have hgood : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ t → scalarTilt x t ∈ feasible := by
    filter_upwards [hnear, hsmall] with t ht hs ht0
    apply mem_feasible_of_nonnegative _ (fun i => (ht.1 i).le)
    intro k l
    by_cases hk : k = 0
    · subst k
      by_cases hl : l < N
      · exact (hs ⟨l, hl⟩).le
      · exact (ht.2 0 l (Or.inr (Nat.le_of_not_gt hl))).le
    · rw [countTest_scalarTilt]
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
      have hchange := mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg ht0 (Nat.cast_nonneg l)) (by linarith : 1 - (k : ℝ) ≤ 0)
      linarith [hx.2.2.1 k l]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hhalf : 0 < ε / 2 := half_pos hε
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hhalf]
    linarith
  have hfeas := hball hmem hhalf.le
  have hbound := hmax _ hfeas
  rw [objective_scalarTilt] at hbound
  have hgain := mul_pos (mul_pos he (sub_pos.mpr hbu)) hhalf
  linarith

/-- The smallest actual scalar contact is two or three under the genuine
strict own-floor guards. All integer cases are derived from old count tests. -/
theorem smallest_scalar_contact_two_or_three (x : Coefficients) (hx : x ∈ feasible)
    (ell : ℝ) (hell : 1 / 2 < ell) (hqell : x 3 < ell) (hvell : ell < x 1)
    (hcontact : ∃ l : ℕ, countTest 0 l x = 1) :
    (1 / 3 ≤ x 3 ∧ x 1 = (1 + x 3) / 2 ∧ countTest 0 2 x = 1) ∨
      (1 / 6 < x 3 ∧ x 3 < 1 / 3 ∧ x 1 = 1 / 3 + x 3 ∧ countTest 0 3 x = 1) := by
  let m := Nat.find hcontact
  have hm : countTest 0 m x = 1 := Nat.find_spec hcontact
  have hmOriginal := hm
  have hleast : ∀ l < m, countTest 0 l x ≠ 1 := fun l hl => Nat.find_min hcontact hl
  have hm2 : 2 ≤ m := by
    by_contra hn
    have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with hm0 | hm1
    · simp [hm0, countTest_apply] at hm
    · have haxis2 := hx.2.2.1 0 2
      norm_num [hm1, countTest_apply] at hm haxis2
      linarith
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hprev := hx.2.2.1 0 (m - 1)
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [countTest_apply] at hm hprev
  simp only [Nat.cast_zero, mul_zero, zero_mul, sub_zero, zero_add, hcast] at hm hprev
  have hprevMul := mul_le_mul_of_nonneg_right hprev (show 0 ≤ (m : ℝ) by positivity)
  have hpen : x 3 * m * ((m : ℝ) - 1) ≤ 2 := by nlinarith
  have hmv : (m : ℝ) * x 1 ≤ 2 := by nlinarith
  have hm3 : m ≤ 3 := by
    by_contra h
    have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast (show 4 ≤ m by omega)
    have hv : (1 / 2 : ℝ) < x 1 := hell.trans hvell
    have hmult := mul_lt_mul_of_pos_left hv (show 0 < (m : ℝ) by linarith)
    nlinarith
  have hm23 : m = 2 ∨ m = 3 := by omega
  rcases hm23 with hm2 | hm3
  · left
    have haxis3 := hx.2.2.1 0 3
    norm_num [hm2, countTest_apply] at hm haxis3
    exact ⟨by linarith, by linarith, by simpa only [hm2] using hmOriginal⟩
  · right
    have haxis2 := hx.2.2.1 0 2
    have hnot2 := hleast 2 (by omega)
    norm_num [hm3, countTest_apply] at hm haxis2
    have hqhi : x 3 < 1 / 3 := by
      by_contra h
      have heq : countTest 0 2 x = 1 := by
        rw [countTest_apply]
        norm_num
        linarith
      exact hnot2 heq
    refine ⟨by linarith, hqhi, by linarith, ?_⟩
    simpa only [hm3] using hmOriginal

end Erdos1017.TwoAtomCountGate
