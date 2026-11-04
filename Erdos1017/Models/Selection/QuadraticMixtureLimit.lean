module

public import Erdos1017.Models.Capped.CappedEditMultiplier

/-!
# Mixed edit and vertex curves

The exact mixed finite-edit/vertex curve is factored by its quadratic step
through a continuous quotient (`mixtureCurveQuotient`), and the constant-degree
hypothesis removes only the original first variation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace Erdos1017.Variation

variable {ι : Type*} [Fintype ι]

theorem finite_mixture_curve_identity (a b l q : ι → ℝ) (B Q t : ℝ) :
    (1 - ∑ i, t ^ 2 * (a i) ^ 2) * (B + Q * t ^ 2) +
        (∑ i, t ^ 2 * (a i) ^ 2 * (b i + l i * t + q i * t ^ 2)) - B =
      t ^ 2 * (Q + ∑ i, (a i) ^ 2 * ((b i - B) + l i * t + (q i - Q) * t ^ 2)) := by
  have hi (i : ι) : b i + l i * t + q i * t ^ 2 =
      (B + Q * t ^ 2) + ((b i - B) + l i * t + (q i - Q) * t ^ 2) := by ring
  have hsum : (∑ i, t ^ 2 * (a i) ^ 2 * (b i + l i * t + q i * t ^ 2)) =
      (∑ i, t ^ 2 * (a i) ^ 2) * (B + Q * t ^ 2) +
        t ^ 2 * ∑ i, (a i) ^ 2 * ((b i - B) + l i * t + (q i - Q) * t ^ 2) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hi]
    ring
  rw [hsum]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def mixtureCurveQuotient (T₀ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (T : ι → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : WeightDirections μ) (a : ι → ℝ) (t : ℝ) : ℝ :=
  weightSecondVariation T₀ f f + ∑ i, (a i) ^ 2 *
    ((⟪T i (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ -
      ⟪T₀ (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫) +
      weightFirstVariation (T i) f * t +
      (weightSecondVariation (T i) f f - weightSecondVariation T₀ f f) * t ^ 2)

theorem mixtureCurveQuotient_continuous (T₀ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (T : ι → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : WeightDirections μ) (a : ι → ℝ) :
    Continuous (mixtureCurveQuotient T₀ T f a) := by
  unfold mixtureCurveQuotient
  fun_prop

/-- Exact mixed finite-edit/vertex curve, factored by its quadratic step.
The constant-degree hypothesis removes only the old first variation. -/
theorem mixture_weight_curve_expansion (T₀ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (T : ι → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT₀ : T₀.toLinearMap.IsSymmetric) (hT : ∀ i, (T i).toLinearMap.IsSymmetric)
    (hfirst : weightFirstVariation T₀ = 0) (f : WeightDirections μ) (a : ι → ℝ) (t : ℝ) :
    ⟪((1 - ∑ i, t ^ 2 * (a i) ^ 2) • T₀ + ∑ i, (t ^ 2 * (a i) ^ 2) • T i)
        (vertexWeight (t • f)), vertexWeight (t • f)⟫ -
        ⟪T₀ (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ =
      t ^ 2 * mixtureCurveQuotient T₀ T f a t := by
  simp only [add_apply, sum_apply, smul_apply, inner_add_left, sum_inner, real_inner_smul_left]
  simp_rw [weight_curve_expansion T₀ hT₀, fun i => weight_curve_expansion (T i) (hT i),
    hfirst, LinearMap.zero_apply, zero_mul, add_zero]
  exact finite_mixture_curve_identity a
    (fun i => ⟪T i (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫)
    (fun i => weightFirstVariation (T i) f) (fun i => weightSecondVariation (T i) f f)
    _ _ t

end Erdos1017.Variation
