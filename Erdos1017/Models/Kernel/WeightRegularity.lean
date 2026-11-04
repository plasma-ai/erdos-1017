module

public import Erdos1017.Models.Kernel.KernelWeightVariation

/-!
# Vanishing first variation and constant rows

Vanishing first variation under mass-preserving bounded weights is exactly the
constant-row condition for a bounded row operator, so the regular/singular split
is precisely nonconstant versus constant degree of the kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.Variation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Vanishing first variation under mass-preserving bounded weights is
exactly the constant-row condition for a bounded row operator. -/
theorem weightFirstVariation_eq_zero_iff
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hrow : T (Lp.const 2 μ (1 : ℝ)) ∈ KernelOperator.boundedL2Submodule μ) :
    weightFirstVariation T = 0 ↔
      ∃ c : ℝ, T (Lp.const 2 μ (1 : ℝ)) = c • Lp.const 2 μ (1 : ℝ) := by
  constructor
  · intro hz
    refine ⟨∫ x, T (Lp.const 2 μ (1 : ℝ)) x ∂μ, ?_⟩
    apply bounded_row_constant_of_annihilates_directions _ hrow
    intro f
    have h := LinearMap.congr_fun hz f
    change 2 * ⟪T (Lp.const 2 μ (1 : ℝ)), directionToL2 f⟫ = 0 at h
    linarith
  · rintro ⟨c, hc⟩
    apply LinearMap.ext
    intro f
    change 2 * ⟪T (Lp.const 2 μ (1 : ℝ)), directionToL2 f⟫ = 0
    rw [hc, real_inner_smul_left, KernelOperator.inner_constant_one, direction_integral_zero]
    ring

/-- The regular/singular split is precisely nonconstant/constant degree for
the actual kernel, rather than an additional spectral assumption. -/
theorem kernel_weightFirstVariation_eq_zero_iff
    (A : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hA : AEStronglyMeasurable (fun z : Ω × Ω => A z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖A z.1 z.2‖ ≤ B) :
    weightFirstVariation (KernelOperator.operator A hB0 hA hB) = 0 ↔
      ∃ c : ℝ, ∀ᵐ x ∂μ, (∫ y, A x y ∂μ) = c := by
  rw [weightFirstVariation_eq_zero_iff _
    (KernelOperator.operator_range_bounded A hB0 hA hB (Lp.const 2 μ (1 : ℝ)))]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, KernelOperator.stationary_of_constant_one_eigenvector A hB0 hA hB c hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, KernelOperator.constant_one_eigenvector_of_stationary A hB0 hA hB c hc⟩

end Erdos1017.Variation
