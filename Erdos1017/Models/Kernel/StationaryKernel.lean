module

public import Erdos1017.Models.Kernel.BoundedPositiveIndex

/-!
# Constant eigenvector of a stationary kernel

A constant row integral makes the constant unit function an eigenvector in `L²`,
with no distinguished eigenbasis direction assumed, and the stationary
eigenvalue has absolute value at most the kernel bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem constant_one_norm : ‖Lp.const 2 μ (1 : ℝ)‖ = 1 := by
  simp [Lp.norm_const 2 μ (1 : ℝ) (by norm_num)]

theorem inner_constant_one (f : Lp ℝ 2 μ) :
    ⟪Lp.const 2 μ (1 : ℝ), f⟫ = ∫ x, f x ∂μ := by
  simpa using L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top μ Set.univ) f

/-- A constant row integral gives the actual constant unit eigenvector in
L²; no distinguished eigenbasis direction is assumed. -/
theorem constant_one_eigenvector_of_stationary
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (ν : ℝ) (hstationary : ∀ᵐ x ∂μ, (∫ y, K x y ∂μ) = ν) :
    operator K hB0 hK hB (Lp.const 2 μ (1 : ℝ)) = ν • Lp.const 2 μ (1 : ℝ) := by
  apply Lp.ext
  filter_upwards [onL2_coe K hK hB (Lp.const 2 μ (1 : ℝ)), hstationary,
    Lp.coeFn_smul ν (Lp.const 2 μ (1 : ℝ)), Lp.coeFn_const 2 μ (1 : ℝ)] with x hx hs hm hc
  change onL2 K hK hB (Lp.const 2 μ (1 : ℝ)) x = _
  rw [hx, hm]
  change applyKernel (μ := μ) K (Lp.const 2 μ (1 : ℝ)) x = ν * (Lp.const 2 μ (1 : ℝ)) x
  rw [hc]
  have heq : applyKernel (μ := μ) K (Lp.const 2 μ (1 : ℝ)) x = ∫ y, K x y ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with y hy
    rw [hy]
    simp
  simpa using heq.trans hs

/-- The stationary eigenvalue has absolute value at most the kernel bound. -/
theorem stationary_value_abs_le
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (ν : ℝ) (hstationary : ∀ᵐ x ∂μ, (∫ y, K x y ∂μ) = ν) : |ν| ≤ B := by
  have he := constant_one_eigenvector_of_stationary K hB0 hK hB ν hstationary
  have hn := onL2_norm_le K hB0 hK hB (Lp.const 2 μ (1 : ℝ))
  change ‖operator K hB0 hK hB (Lp.const 2 μ (1 : ℝ))‖ ≤ _ at hn
  simpa only [he, norm_smul, constant_one_norm, mul_one, Real.norm_eq_abs] using hn

end Erdos1017.KernelOperator
