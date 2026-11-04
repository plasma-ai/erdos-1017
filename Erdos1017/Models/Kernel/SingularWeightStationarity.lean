module

public import Erdos1017.Models.Kernel.WeightRegularity
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Stationarity in the singular branch

A linear term dominated locally by quadratic terms vanishes, so constant density
degree and a local Lipschitz comparison force constant objective degree in the
singular branch with no multiplier assumed; a kernel form states the comparison
in pair integrals.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace Erdos1017.Variation

/-- A linear term dominated locally by quadratic terms vanishes. -/
theorem linear_eq_zero_of_eventual_quadratic_bound (l q r : ℝ)
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), l * t + q * t ^ 2 ≤ r * t ^ 2) : l = 0 := by
  have hmax : IsLocalMax (fun t : ℝ => l * t + (q - r) * t ^ 2) 0 := by
    filter_upwards [h] with t ht
    simp only [mul_zero, zero_pow (by omega : 2 ≠ 0), add_zero]
    nlinarith
  apply hmax.hasDerivAt_eq_zero
  convert (HasDerivAt.const_mul l (hasDerivAt_id (0 : ℝ))).add
    (HasDerivAt.const_mul (q - r) ((hasDerivAt_id (0 : ℝ)).pow 2)) using 1 <;> first | rfl | simp

/-- A local Lipschitz objective comparison when the density has zero first
variation forces the objective first variation to vanish. -/
theorem linear_eq_zero_of_local_quadratic_domination
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : E →ₗ[ℝ] ℝ) (A B : LinearMap.BilinForm ℝ E)
    (L ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ x : E, ‖x‖ < ε → C x + B x x ≤ L * |A x x|) : C = 0 := by
  apply LinearMap.ext
  intro v
  change C v = 0
  apply linear_eq_zero_of_eventual_quadratic_bound (C v) (B v v) (L * |A v v|)
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), ‖t • v‖ < ε := by
    have hc : ContinuousAt (fun t : ℝ => ‖t • v‖) 0 := by fun_prop
    exact hc.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [hsmall] with t ht
  have h := hbound (t • v) ht
  have hA : A (t • v) (t • v) = t ^ 2 * A v v := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hB : B (t • v) (t • v) = t ^ 2 * B v v := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hA, hB, map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (sq_nonneg t)] at h
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Constant density degree and the actual local Lipschitz comparison imply
constant objective degree in the singular branch. No multiplier is assumed. -/
theorem stationary_of_singular_weight_comparison
    (A Y : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hA : A.toLinearMap.IsSymmetric) (hY : Y.toLinearMap.IsSymmetric)
    (hYrow : Y (Lp.const 2 μ (1 : ℝ)) ∈ KernelOperator.boundedL2Submodule μ)
    (hsingular : weightFirstVariation A = 0)
    (L ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ f : WeightDirections μ, ‖f‖ < ε →
      ⟪Y (vertexWeight f), vertexWeight f⟫ - ⟪Y (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ ≤
        L * |⟪A (vertexWeight f), vertexWeight f⟫ -
          ⟪A (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫|) :
    ∃ c : ℝ, Y (Lp.const 2 μ (1 : ℝ)) = c • Lp.const 2 μ (1 : ℝ) := by
  apply (weightFirstVariation_eq_zero_iff Y hYrow).mp
  apply linear_eq_zero_of_local_quadratic_domination
    (weightFirstVariation Y) (weightSecondVariation A) (weightSecondVariation Y) L ε hε
  intro f hf
  have h := hbound f hf
  change _ - _ ≤ L * |_ - _| at h
  rw [show vertexWeight f = Lp.const 2 μ (1 : ℝ) + directionToL2 f from rfl,
    weighted_quadratic_expansion Y hY f, weighted_quadratic_expansion A hA f,
    hsingular, LinearMap.zero_apply] at h
  have ha (a b : ℝ) : a + 0 + b - a = b := by ring
  rw [ha] at h
  linarith

/-- Kernel form of singular-branch stationarity, with the local comparison
stated entirely in actual pair integrals. -/
theorem stationary_kernel_of_constant_degree_comparison
    (A Y : Ω → Ω → ℝ) {B C : ℝ} (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hA : AEStronglyMeasurable (fun z : Ω × Ω => A z.1 z.2) (μ.prod μ))
    (hY : AEStronglyMeasurable (fun z : Ω × Ω => Y z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖A z.1 z.2‖ ≤ B)
    (hC : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖Y z.1 z.2‖ ≤ C)
    (hAsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, A z.1 z.2 = A z.2 z.1)
    (hYsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, Y z.1 z.2 = Y z.2 z.1)
    (hsingular : ∃ c : ℝ, ∀ᵐ x ∂μ, (∫ y, A x y ∂μ) = c)
    (L ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ f : WeightDirections μ, ‖f‖ < ε →
      weightedPairIntegral Y (vertexWeight f) - weightedPairIntegral Y (Lp.const 2 μ (1 : ℝ)) ≤
        L * |weightedPairIntegral A (vertexWeight f) -
          weightedPairIntegral A (Lp.const 2 μ (1 : ℝ))|) :
    ∃ c : ℝ, ∀ᵐ x ∂μ, (∫ y, Y x y ∂μ) = c := by
  have hs := (kernel_weightFirstVariation_eq_zero_iff A hB0 hA hB).mpr hsingular
  obtain ⟨c, hc⟩ := stationary_of_singular_weight_comparison
    (KernelOperator.operator A hB0 hA hB) (KernelOperator.operator Y hC0 hY hC)
    (KernelOperator.operator_symmetric A hB0 hA hB hAsym)
    (KernelOperator.operator_symmetric Y hC0 hY hC hYsym)
    (KernelOperator.operator_range_bounded Y hC0 hY hC (Lp.const 2 μ (1 : ℝ)))
    hs L ε hε (by
      simpa only [weightedPairIntegral_eq A hB0 hA hB, weightedPairIntegral_eq Y hC0 hY hC]
        using hbound)
  exact ⟨c, KernelOperator.stationary_of_constant_one_eigenvector Y hC0 hY hC c hc⟩

end Erdos1017.Variation
