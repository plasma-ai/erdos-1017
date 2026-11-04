module

public import Erdos1017.Models.Kernel.BoundedPositiveIndex
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Quadratic moment residuals of bounded functions

An almost-everywhere quadratic relation permits at most two essential values,
and conversely more than two essential values give a bounded residual (the
projection of the square onto the span of one and the function) with positive
square moment and two zero moments, extendable by zero from a measurable block.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- An almost-everywhere quadratic relation permits at most two essential
real values, including when the underlying finite measure is zero. -/
theorem ae_two_values_of_quadratic_relation (φ : Ω → ℝ) (a b : ℝ)
    (hφ : ∀ᵐ x ∂μ, φ x ^ 2 = a + b * φ x) :
    ∃ s t : ℝ, ∀ᵐ x ∂μ, φ x = s ∨ φ x = t := by
  by_cases hμ : μ = 0
  · exact ⟨0, 0, by simp [hμ]⟩
  have : NeZero μ := ⟨hμ⟩
  obtain ⟨x, hx⟩ := hφ.exists
  refine ⟨φ x, b - φ x, ?_⟩
  filter_upwards [hφ] with y hy
  have hfactor : (φ y - φ x) * (φ y - (b - φ x)) = 0 := by nlinarith
  exact (mul_eq_zero.mp hfactor).imp sub_eq_zero.mp sub_eq_zero.mp

/-- Orthogonal projection of the actual square onto the span of one and
the original bounded function constructs its bounded quadratic residual. -/
theorem exists_quadratic_moment_residual (φ : Ω → ℝ)
    (hφ : AEStronglyMeasurable φ μ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B) :
    ∃ (f : Lp ℝ 2 μ) (a b : ℝ), f ∈ boundedL2Submodule μ ∧
      (∀ᵐ x ∂μ, f x = φ x ^ 2 - (a + b * φ x)) ∧
      (∫ x, f x ∂μ) = 0 ∧ (∫ x, φ x * f x ∂μ) = 0 ∧
      (∫ x, φ x ^ 2 * f x ∂μ) = ‖f‖ ^ 2 := by
  classical
  have hv : MemLp φ 2 μ := MemLp.of_bound hφ B hB
  have hqB : ∀ᵐ x ∂μ, ‖φ x ^ 2‖ ≤ B ^ 2 := by
    filter_upwards [hB] with x hx
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hq : MemLp (fun x => φ x ^ 2) 2 μ := MemLp.of_bound (hφ.pow 2) (B ^ 2) hqB
  let one := Lp.const 2 μ (1 : ℝ)
  let v := hv.toLp φ
  let q := hq.toLp (fun x => φ x ^ 2)
  let S := Submodule.span ℝ ({one, v} : Set (Lp ℝ 2 μ))
  have : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  let p := S.starProjection q
  let f := q - p
  have hone : one ∈ boundedL2Submodule μ := by
    refine ⟨1, by norm_num, ?_⟩
    filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with x hx
    rw [hx]
    norm_num
  have hvbound : v ∈ boundedL2Submodule μ := by
    refine ⟨B, hB0, ?_⟩
    filter_upwards [hv.coeFn_toLp, hB] with x hx hbound
    rw [hx]
    exact hbound
  have hqbound : q ∈ boundedL2Submodule μ := by
    refine ⟨B ^ 2, sq_nonneg _, ?_⟩
    filter_upwards [hq.coeFn_toLp, hqB] with x hx hbound
    rw [hx]
    exact hbound
  have hS : S ≤ boundedL2Submodule μ := by
    apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hone
    · exact hvbound
  have hp : p ∈ S := S.starProjection_apply_mem q
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hp
  have hf : f ∈ boundedL2Submodule μ := (boundedL2Submodule μ).sub_mem hqbound (hS hp)
  have horth (z : Lp ℝ 2 μ) (hz : z ∈ S) : ⟪f, z⟫ = 0 :=
    S.starProjection_inner_eq_zero q z hz
  have hfone : ⟪one, f⟫ = 0 := by
    rw [real_inner_comm]
    exact horth one (Submodule.subset_span (by simp))
  have hfv : ⟪v, f⟫ = 0 := by
    rw [real_inner_comm]
    exact horth v (Submodule.subset_span (by simp))
  have hfq : ⟪q, f⟫ = ‖f‖ ^ 2 := by
    have hporth := horth p hp
    have hporth' : ⟪p, f⟫ = 0 := (real_inner_comm f p).trans hporth
    have hself : ⟪f, f⟫ = ⟪q, f⟫ := by
      change ⟪q - p, f⟫ = _
      rw [inner_sub_left, hporth', sub_zero]
    rw [real_inner_self_eq_norm_sq] at hself
    exact hself.symm
  refine ⟨f, a, b, hf, ?_, ?_, ?_, ?_⟩
  · have heq : f = q - (a • one + b • v) := by rw [hab]
    rw [heq]
    filter_upwards [Lp.coeFn_sub q (a • one + b • v),
      Lp.coeFn_add (a • one) (b • v), Lp.coeFn_smul a one,
      Lp.coeFn_smul b v, Lp.coeFn_const 2 μ (1 : ℝ), hv.coeFn_toLp,
      hq.coeFn_toLp] with x hsub hadd ha hb hone hvx hqx
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hadd]
    simp only [Pi.add_apply]
    rw [ha, hb]
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [Function.const_apply] at hone
    rw [hone, hvx, hqx, mul_one]
  · have honeinner : ⟪one, f⟫ = ∫ x, f x ∂μ := by
      simpa [one] using L2.inner_indicatorConstLp_one
        MeasurableSet.univ (measure_ne_top μ Set.univ) f
    rwa [honeinner] at hfone
  · rw [L2.inner_def] at hfv
    rw [← hfv]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with x hx
    change v x = φ x at hx
    simp only [RCLike.inner_apply, conj_trivial, hx]
    ring
  · rw [L2.inner_def] at hfq
    rw [← hfq]
    apply integral_congr_ae
    filter_upwards [hq.coeFn_toLp] with x hx
    change q x = φ x ^ 2 at hx
    simp only [RCLike.inner_apply, conj_trivial, hx]
    ring

/-- More than two essential values leave a nonzero bounded residual with
a strictly positive square moment and the two required zero moments. -/
theorem exists_positive_quadratic_moment_residual (φ : Ω → ℝ)
    (hφ : AEStronglyMeasurable φ μ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B)
    (hnot : ¬∃ s t : ℝ, ∀ᵐ x ∂μ, φ x = s ∨ φ x = t) :
    ∃ f : Lp ℝ 2 μ, f ∈ boundedL2Submodule μ ∧
      (∫ x, f x ∂μ) = 0 ∧ (∫ x, φ x * f x ∂μ) = 0 ∧
      0 < ∫ x, φ x ^ 2 * f x ∂μ := by
  obtain ⟨f, a, b, hf, hrepr, hmean, hmoment, hsquare⟩ :=
    exists_quadratic_moment_residual φ hφ hB0 hB
  have hne : f ≠ 0 := by
    intro hz
    have hfzero : ∀ᵐ x ∂μ, f x = 0 := by
      rw [hz]
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
      exact hx
    have hrelation : ∀ᵐ x ∂μ, φ x ^ 2 = a + b * φ x := by
      filter_upwards [hrepr, hfzero] with x hx hzero
      linarith
    exact hnot (ae_two_values_of_quadratic_relation φ a b hrelation)
  refine ⟨f, hf, hmean, hmoment, ?_⟩
  rw [hsquare]
  exact sq_pos_of_pos (norm_pos_iff.mpr hne)

/-- Vanishing of the quadratic moment on all bounded tests orthogonal to
one and the function forces at most two essential values. -/
theorem ae_two_values_of_orthogonal_quadratic_moment_zero (φ : Ω → ℝ)
    (hφ : AEStronglyMeasurable φ μ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B)
    (hzero : ∀ f : Lp ℝ 2 μ, f ∈ boundedL2Submodule μ →
      (∫ x, f x ∂μ) = 0 → (∫ x, φ x * f x ∂μ) = 0 →
      (∫ x, φ x ^ 2 * f x ∂μ) = 0) :
    ∃ s t : ℝ, ∀ᵐ x ∂μ, φ x = s ∨ φ x = t := by
  by_contra hnot
  obtain ⟨f, hf, hmean, hmoment, hpositive⟩ :=
    exists_positive_quadratic_moment_residual φ hφ hB0 hB hnot
  rw [hzero f hf hmean hmoment] at hpositive
  exact (lt_irrefl 0) hpositive

/-- The residual on an actual measurable block extends by zero to a
bounded test under the original measure, preserving its moment identities. -/
theorem exists_supported_positive_quadratic_moment_residual
    (E : Set Ω) (hE : MeasurableSet E) (φ : Ω → ℝ)
    (hφ : AEStronglyMeasurable φ μ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B)
    (hnot : ¬∃ s t : ℝ, ∀ᵐ x ∂μ.restrict E, φ x = s ∨ φ x = t) :
    ∃ f : Lp ℝ 2 μ, f ∈ boundedL2Submodule μ ∧
      (∀ᵐ x ∂μ, x ∉ E → f x = 0) ∧
      (∫ x, f x ∂μ) = 0 ∧ (∫ x, φ x * f x ∂μ) = 0 ∧
      0 < ∫ x, φ x ^ 2 * f x ∂μ := by
  classical
  obtain ⟨g, hg, hmean, hmoment, hpositive⟩ :=
    exists_positive_quadratic_moment_residual φ hφ.restrict hB0 (ae_restrict_of_ae hB) hnot
  have hmem : MemLp (E.indicator (fun x => g x)) 2 μ :=
    (memLp_indicator_iff_restrict hE.nullMeasurableSet).mpr (Lp.memLp g)
  let f := hmem.toLp (E.indicator (fun x => g x))
  obtain ⟨C, hC, hbound⟩ := hg
  have hf : f ∈ boundedL2Submodule μ := by
    refine ⟨C, hC, ?_⟩
    filter_upwards [hmem.coeFn_toLp, (ae_restrict_iff' hE).mp hbound] with x hx hbound
    rw [hx]
    by_cases hxe : x ∈ E
    · simpa only [Set.indicator_of_mem hxe] using hbound hxe
    · simpa only [Set.indicator_of_notMem hxe, norm_zero] using hC
  have hmeanf : (∫ x, f x ∂μ) = 0 := by
    calc
      (∫ x, f x ∂μ) = ∫ x, E.indicator (fun x => g x) x ∂μ :=
        integral_congr_ae hmem.coeFn_toLp
      _ = ∫ x, g x ∂μ.restrict E := integral_indicator hE
      _ = 0 := hmean
  have hintegral (ψ : Ω → ℝ) : (∫ x, ψ x * f x ∂μ) =
      ∫ x, ψ x * g x ∂μ.restrict E := by
    calc
      (∫ x, ψ x * f x ∂μ) = ∫ x, E.indicator (fun x => ψ x * g x) x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hmem.coeFn_toLp] with x hx
        rw [hx]
        by_cases hxe : x ∈ E <;> simp [hxe]
      _ = _ := integral_indicator hE
  refine ⟨f, hf, ?_, hmeanf, ?_, ?_⟩
  · filter_upwards [hmem.coeFn_toLp] with x hx hxe
    rw [hx, Set.indicator_of_notMem hxe]
  · rw [hintegral φ]
    exact hmoment
  · rw [hintegral (fun x => φ x ^ 2)]
    exact hpositive

end Erdos1017.KernelOperator
