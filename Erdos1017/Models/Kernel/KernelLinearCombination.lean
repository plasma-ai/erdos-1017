module

public import Erdos1017.Models.Kernel.KernelSpectralPart
public import Erdos1017.Models.Kernel.StationaryKernel

/-!
# Scaling kernels and the constant eigenvector

Scaling a kernel scales its integral operator, and the constant eigenvector
identity implies the almost-everywhere row-integral identity without choosing
pointwise kernel representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem kernel_smul_bound {K : Ω → Ω → ℝ} {B : ℝ}
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (m : ℝ) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖m * K z.1 z.2‖ ≤ ‖m‖ * B := by
  filter_upwards [hB] with z hz
  simpa only [norm_mul] using mul_le_mul_of_nonneg_left hz (norm_nonneg m)

/-- Scaling the actual kernel scales its integral operator. -/
theorem operator_smul_kernel (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (m : ℝ) :
    operator (fun x y => m * K x y) (mul_nonneg (norm_nonneg m) hB0)
      (hK.const_mul m) (kernel_smul_bound hB m) = m • operator K hB0 hK hB := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  rw [smul_apply, real_inner_smul_left, operator_inner, operator_inner]
  simp_rw [mul_assoc]
  exact integral_const_mul m _

/-- The constant eigenvector identity implies the actual almost-everywhere
row-integral identity, without choosing pointwise kernel representatives. -/
theorem stationary_of_constant_one_eigenvector
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (ν : ℝ) (heigen : operator K hB0 hK hB (Lp.const 2 μ (1 : ℝ)) =
      ν • Lp.const 2 μ (1 : ℝ)) :
    ∀ᵐ x ∂μ, (∫ y, K x y ∂μ) = ν := by
  have hrep := onL2_coe K hK hB (Lp.const 2 μ (1 : ℝ))
  change ∀ᵐ x ∂μ, operator K hB0 hK hB (Lp.const 2 μ (1 : ℝ)) x = _ at hrep
  rw [heigen] at hrep
  filter_upwards [hrep, Lp.coeFn_smul ν (Lp.const 2 μ (1 : ℝ)),
    Lp.coeFn_const 2 μ (1 : ℝ)] with x hx hm hc
  have heq : applyKernel (μ := μ) K (Lp.const 2 μ (1 : ℝ)) x = ∫ y, K x y ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with y hy
    rw [hy]
    simp
  rw [hm] at hx
  change ν * (Lp.const 2 μ (1 : ℝ)) x = _ at hx
  simpa only [hc, Function.const_apply, mul_one, heq] using hx.symm

end Erdos1017.KernelOperator
