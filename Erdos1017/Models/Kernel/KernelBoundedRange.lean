module

public import Erdos1017.Models.Kernel.BoundedPositiveIndex

/-!
# Bounded range of bounded kernel operators

An essentially bounded kernel sends every L² function to an essentially bounded
function on a probability space (`operator_range_bounded`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.KernelOperator

/-- An essentially bounded kernel sends every L² function to an essentially
bounded function on a probability space. -/
theorem operator_range_bounded
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (f : Lp ℝ 2 μ) :
    operator K hB0 hK hB f ∈ boundedL2Submodule μ := by
  refine ⟨B * (∫ x, ‖f x‖ ∂μ), mul_nonneg hB0 (integral_nonneg (fun _ => norm_nonneg _)), ?_⟩
  filter_upwards [onL2_coe K hK hB f,
    applyKernel_bound hB ((Lp.memLp f).integrable (by norm_num))] with x hx hb
  change ‖onL2 K hK hB f x‖ ≤ _
  rwa [hx]

end Erdos1017.KernelOperator
