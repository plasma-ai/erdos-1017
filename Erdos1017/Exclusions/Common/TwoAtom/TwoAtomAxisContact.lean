module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomScalarContact

/-!
# Scalar axis contact of the two-atom system

With `q > 0` alone, the improving `BE`/`RE` tilt has the `E`-axis tail it needs,
so an optimal vector has a finite scalar axis contact, and such a contact with
`h > 0` forces `r > 0` through its one-`R` extension.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

theorem unanchoredTest_scalarTilt (x : Coefficients) (t : ℝ) (k l : ℕ) :
    unanchoredTest k l (scalarTilt x t) = unanchoredTest k l x - t * k * l := by
  simp [scalarTilt, unanchoredTest_apply, Matrix.vecHead, Matrix.vecTail]
  ring

theorem firstAtomTest_scalarTilt (x : Coefficients) (t : ℝ) (k : ℕ) :
    firstAtomTest k (scalarTilt x t) = firstAtomTest k x := by
  simp [scalarTilt, firstAtomTest_apply, Matrix.vecHead, Matrix.vecTail]

/-- q>0 alone supplies the E-axis tail needed by the actual improving
BE/RE tilt. No sign of r, or positive full coefficient vector, is assumed. -/
theorem exists_scalar_axis_contact_of_optimal_of_q_pos {a b u e : ℝ}
    (hbu : u < b) (he : 0 < e) (x : Coefficients) (hx : x ∈ feasible) (hq : 0 < x 3)
    (hmax : ∀ y ∈ feasible, objective a b u e y ≤ objective a b u e x) :
    ∃ l : ℕ, countTest 0 l x = 1 := by
  by_contra hn
  push Not at hn
  let M := |x 1| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨N, hN⟩ := VertexClassification.uniform_tail M (x 3) hM hq
  have hcont : ContinuousAt (scalarTilt x) 0 := by unfold scalarTilt; fun_prop
  have hv : ∀ᶠ t : ℝ in 𝓝 0, scalarTilt x t 1 < M := by
    have hc : ContinuousAt (fun t => scalarTilt x t 1) 0 := by
      exact (continuous_apply 1).continuousAt.comp hcont
    have ht : Tendsto (fun t => scalarTilt x t 1) (𝓝 0) (𝓝 (x 1)) := by
      simpa [scalarTilt] using hc.tendsto
    exact ht.eventually_lt_const (by dsimp [M]; linarith [le_abs_self (x 1)])
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
    filter_upwards [hv, hsmall] with t ht hs ht0
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [scalarTilt, Matrix.vecHead, Matrix.vecTail] using hx.1
    · simpa [scalarTilt, Matrix.vecHead, Matrix.vecTail] using hx.2.1
    · intro k l
      by_cases hk : k = 0
      · subst k
        by_cases hl : l < N
        · exact (hs ⟨l, hl⟩).le
        · have htail := hN 0 (scalarTilt x t 1) (x 3) (by dsimp [M]; positivity)
            ht.le le_rfl l (Nat.le_of_not_gt hl)
          simpa [TightCounts.value, countTest_apply, scalarTilt, Matrix.vecHead, Matrix.vecTail,
            mul_comm]
            using htail.le
      · rw [countTest_scalarTilt]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
        have hchange := mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg ht0 (Nat.cast_nonneg l)) (by linarith : 1 - (k : ℝ) ≤ 0)
        linarith [hx.2.2.1 k l]
    · intro k l
      rw [unanchoredTest_scalarTilt]
      have hchange := mul_nonneg (mul_nonneg ht0 (Nat.cast_nonneg k)) (Nat.cast_nonneg l)
      linarith [hx.2.2.2.1 k l]
    · intro k
      rw [firstAtomTest_scalarTilt]
      exact hx.2.2.2.2 k
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hhalf : 0 < ε / 2 := half_pos hε
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hhalf]
    linarith
  have hbound := hmax _ (hball hmem hhalf.le)
  rw [objective_scalarTilt] at hbound
  have hgain := mul_pos (mul_pos he (sub_pos.mpr hbu)) hhalf
  linarith

/-- A real finite scalar contact and h>0 force r>0 through its actual
one-R extension, without using a copy-penalty or r-floor premise. -/
theorem r_pos_of_scalar_axis_contact (x : Coefficients) (hx : x ∈ feasible)
    (hh : 0 < x 0) (hcontact : ∃ l, countTest 0 l x = 1) : 0 < x 4 := by
  obtain ⟨l, hl⟩ := hcontact
  have hl0 : l ≠ 0 := by intro h; simp [h, countTest_apply] at hl
  have hln : 0 < (l : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hl0
  have htest := hx.2.2.1 1 l
  rw [countTest_apply] at htest hl
  norm_num only [Nat.cast_one, Nat.cast_zero, zero_mul, mul_zero, one_mul, sub_zero,
    zero_add, sub_self, zero_div] at htest hl
  by_contra h
  have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hln.le
  nlinarith only [htest, hl, hh, hprod]

end Erdos1017.TwoAtomCountGate
