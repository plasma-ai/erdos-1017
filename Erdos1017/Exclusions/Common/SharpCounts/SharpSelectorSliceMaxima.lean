module

public import Erdos1017.Exclusions.Common.SharpCounts.SharpSelectorCenteredMatrix
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Order.Compact

/-!
# Maxima of the sharp selector on the load-two slice

On the closed cube slice of total load exactly two, compactness gives a maximum
of the quadratic polynomial, feasible perturbations there force a vanishing
first variation and nonpositive Hessian energy, and total mass two below every
unit boundary forces three distinct occupied labels.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped BigOperators Classical Topology

namespace Erdos1017.Selector.Sharp

variable {ι : Type*} [Fintype ι]

/-- A linear term plus the actual half-Hessian quadratic energy. -/
def quadraticPolynomial (a : ι → ℝ) (C : ι → ι → ℝ) (p : ι → ℝ) : ℝ :=
  (∑ i, a i * p i) + matrixQuadratic C p / 2

/-- The closed cube slice of total load exactly two. -/
def sumTwoSlice : Set (ι → ℝ) := {p | (∀ i, p i ∈ Icc (0 : ℝ) 1) ∧ ∑ i, p i = 2}

/-- Compactness gives an actual maximum whenever the load-two slice is nonempty. -/
theorem exists_sumTwoSlice_max (a : ι → ℝ) (C : ι → ι → ℝ)
    (p : ι → ℝ) (hp : p ∈ sumTwoSlice) :
    ∃ x ∈ sumTwoSlice, IsMaxOn (quadraticPolynomial a C) sumTwoSlice x := by
  have he : (sumTwoSlice : Set (ι → ℝ)) = Icc (fun _ => 0) (fun _ => 1) ∩
      {x | ∑ i, x i = 2} := by
    ext x
    simp only [sumTwoSlice, mem_ofPred_eq, mem_inter_iff, mem_Icc, Pi.le_def]
    exact and_congr_left (fun _ => by simp only [← forall_and])
  have hcompact : IsCompact (sumTwoSlice : Set (ι → ℝ)) := by
    rw [he]
    exact isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)
  have hcont : Continuous (quadraticPolynomial a C) := by
    unfold quadraticPolynomial matrixQuadratic matrixRow
    fun_prop
  exact hcompact.exists_isMaxOn ⟨p, hp⟩ hcont.continuousOn

private theorem quadratic_coefficients_of_local_max {a b : ℝ}
    (h : ∀ᶠ t : ℝ in nhds 0, a * t + b * t ^ 2 ≤ 0) : a = 0 ∧ b ≤ 0 := by
  have hmax : IsLocalMax (fun t : ℝ => a * t + b * t ^ 2) 0 := by
    simpa only [IsLocalMax, IsMaxFilter, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using h
  have hd : HasDerivAt (fun t : ℝ => a * t + b * t ^ 2) a 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul a).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul b) using 1 <;> norm_num
    rfl
  have ha := hmax.hasDerivAt_eq_zero hd
  refine ⟨ha, ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  have ht := hball (show ε / 2 ∈ Metric.ball (0 : ℝ) ε by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith)
  rw [ha] at ht
  have hsq : 0 < (ε / 2) ^ 2 := sq_pos_of_pos (by positivity)
  exact nonpos_of_mul_nonpos_right (by simpa [mul_comm] using ht) hsq

/-- Every supported zero-sum direction remains in the actual cube slice
for sufficiently small positive and negative parameters. -/
theorem eventually_mem_sumTwoSlice (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Ico (0 : ℝ) 1) (hs : ∑ i, p i = 2)
    (z : ι → ℝ) (hz : ∑ i, z i = 0) (hsupport : ∀ i, p i = 0 → z i = 0) :
    ∀ᶠ t : ℝ in nhds 0, (fun i => p i + t * z i) ∈ sumTwoSlice := by
  have hcoord (i : ι) : ∀ᶠ t : ℝ in nhds 0, p i + t * z i ∈ Icc (0 : ℝ) 1 := by
    by_cases hi : p i = 0
    · simp only [hi, hsupport i hi, mul_zero, add_zero]
      exact Eventually.of_forall (fun _ => ⟨le_rfl, zero_le_one⟩)
    · have hpi : 0 < p i := lt_of_le_of_ne (hp i).1 (Ne.symm hi)
      have hc : Continuous (fun t : ℝ => p i + t * z i) := by fun_prop
      have hc' : Tendsto (fun t : ℝ => p i + t * z i) (nhds 0) (nhds (p i)) := by
        simpa using hc.tendsto 0
      have he := hc'.eventually (Ioo_mem_nhds hpi (hp i).2)
      filter_upwards [he] with t ht
      exact ⟨ht.1.le, ht.2.le⟩
  filter_upwards [Filter.eventually_all.mpr hcoord] with t ht
  refine ⟨ht, ?_⟩
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, hs, hz]

/-- Actual local feasible perturbations at an actual slice maximum
force vanishing first variation and nonpositive Hessian energy. -/
theorem variations_of_sumTwoSlice_max (a : ι → ℝ) (C : ι → ι → ℝ)
    (hC : ∀ i j, C i j = C j i) (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Ico (0 : ℝ) 1) (hs : ∑ i, p i = 2)
    (hmax : IsMaxOn (quadraticPolynomial a C) sumTwoSlice p)
    (z : ι → ℝ) (hz : ∑ i, z i = 0) (hsupport : ∀ i, p i = 0 → z i = 0) :
    (∑ i, z i * (a i + matrixRow C p i)) = 0 ∧ matrixQuadratic C z ≤ 0 := by
  have he : ∀ᶠ t : ℝ in nhds 0,
      (∑ i, z i * (a i + matrixRow C p i)) * t + (matrixQuadratic C z / 2) * t ^ 2 ≤ 0 := by
    filter_upwards [eventually_mem_sumTwoSlice p hp hs z hz hsupport] with t ht
    have hb : quadraticPolynomial a C (fun i => p i + t * z i) ≤ quadraticPolynomial a C p :=
      hmax ht
    have hexpand : quadraticPolynomial a C (fun i => p i + t * z i) =
        quadraticPolynomial a C p + (∑ i, z i * (a i + matrixRow C p i)) * t +
          (matrixQuadratic C z / 2) * t ^ 2 := by
      unfold quadraticPolynomial
      rw [matrixQuadratic_add_smul C hC]
      simp only [mul_add, Finset.sum_add_distrib]
      have hlin : (∑ i, a i * (t * z i)) = t * ∑ i, z i * a i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hlin]
      ring
    rw [hexpand] at hb
    linarith
  obtain ⟨hfirst, hsecond⟩ := quadratic_coefficients_of_local_max he
  exact ⟨hfirst, by linarith⟩

/-- Total mass two below every unit boundary forces three distinct
occupied labels; no lower bound on the ambient dimension is assumed. -/
theorem exists_positive_triple (p : ι → ℝ) (hp : ∀ i, p i ∈ Ico (0 : ℝ) 1)
    (hs : ∑ i, p i = 2) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ 0 < p i ∧ 0 < p j ∧ 0 < p k := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < p i := by
    by_contra h
    push Not at h
    have hn := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    linarith
  obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ 0 < p j := by
    by_contra h
    push Not at h
    have he : ∑ k, p k = p i := by
      apply Finset.sum_eq_single i
      · intro k _ hki
        exact le_antisymm (h k hki) (hp k).1
      · simp
    linarith [(hp i).2]
  obtain ⟨k, hki, hkj, hk⟩ : ∃ k, k ≠ i ∧ k ≠ j ∧ 0 < p k := by
    by_contra h
    push Not at h
    have ht (k : ι) : p k = (if k = i then p i else 0) + (if k = j then p j else 0) := by
      by_cases hki : k = i
      · subst k
        simp [Ne.symm hji]
      by_cases hkj : k = j
      · subst k
        simp [hji]
      have hk0 : p k = 0 := le_antisymm (h k hki hkj) (hp k).1
      simp [hki, hkj, hk0]
    have he : ∑ k, p k = p i + p j := by
      calc
        ∑ k, p k = ∑ k, ((if k = i then p i else 0) + (if k = j then p j else 0)) :=
          Finset.sum_congr rfl (fun k _ => ht k)
        _ = _ := by simp [Finset.sum_add_distrib]
    linarith [(hp i).2, (hp j).2]
  exact ⟨i, j, k, Ne.symm hji, Ne.symm hki, Ne.symm hkj, hi, hj, hk⟩

end Erdos1017.Selector.Sharp
