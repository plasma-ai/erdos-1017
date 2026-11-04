module

public import Erdos1017.Models.Kernel.SingularWeightStationarity
public import Erdos1017.Models.Selection.QuadraticSeparation

/-!
# Kernels perturbed by a scalar multiple

A kernel plus a scalar multiple of another bounded kernel is bounded
(`kernel_add_smul_bound`), and its kernel operator is the same combination of
the two operators (`operator_add_smul_kernel`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem kernel_add_smul_bound {A Y : Ω → Ω → ℝ} {B C : ℝ}
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖A z.1 z.2‖ ≤ B)
    (hC : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖Y z.1 z.2‖ ≤ C) (m : ℝ) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖Y z.1 z.2 + m * A z.1 z.2‖ ≤ C + ‖m‖ * B := by
  filter_upwards [hB, hC] with z hb hc
  exact (norm_add_le _ _).trans (add_le_add hc
    (by simpa only [norm_mul] using mul_le_mul_of_nonneg_left hb (norm_nonneg m)))

theorem operator_add_smul_kernel (A Y : Ω → Ω → ℝ) {B C : ℝ}
    (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hA : AEStronglyMeasurable (fun z : Ω × Ω => A z.1 z.2) (μ.prod μ))
    (hY : AEStronglyMeasurable (fun z : Ω × Ω => Y z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖A z.1 z.2‖ ≤ B)
    (hC : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖Y z.1 z.2‖ ≤ C) (m : ℝ) :
    operator (fun x y => Y x y + m * A x y)
      (add_nonneg hC0 (mul_nonneg (norm_nonneg m) hB0))
      (hY.add (hA.const_mul m)) (kernel_add_smul_bound hB hC m) =
      operator Y hC0 hY hC + m • operator A hB0 hA hB := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  rw [add_apply, smul_apply, inner_add_left, real_inner_smul_left,
    operator_inner, operator_inner, operator_inner]
  simp_rw [add_mul]
  rw [integral_add (integrable_bilinear hY hC f g)
    (integrable_bilinear (K := fun x y => m * A x y)
      (hA.const_mul m) (kernel_smul_bound hB m) f g)]
  congr 1
  simp_rw [mul_assoc]
  exact integral_const_mul m _

end Erdos1017.KernelOperator
