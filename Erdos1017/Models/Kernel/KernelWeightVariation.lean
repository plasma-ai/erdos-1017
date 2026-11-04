module

public import Erdos1017.Models.Kernel.RegularWeightVariation
public import Erdos1017.Models.Kernel.KernelLinearCombination

/-!
# Vertex weights and the pair integral

The vertex weight is defined as an `L²` class together with the unhalved
weighted pair integral, and local maximality of the pair integral under vertex
weights gives a stationary shifted kernel with positive index at most two.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.Variation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual vertex weight, as an L² class. -/
def vertexWeight (f : WeightDirections μ) : Lp ℝ 2 μ :=
  Lp.const 2 μ (1 : ℝ) + directionToL2 f

theorem vertexWeight_integral (f : WeightDirections μ) :
    (∫ x, vertexWeight f x ∂μ) = 1 := by
  rw [← KernelOperator.inner_constant_one]
  change ⟪Lp.const 2 μ (1 : ℝ), Lp.const 2 μ (1 : ℝ) + directionToL2 f⟫ = 1
  rw [inner_add_right, KernelOperator.inner_constant_one (directionToL2 f),
    direction_integral_zero, add_zero, real_inner_self_eq_norm_sq, KernelOperator.constant_one_norm]
  norm_num

theorem vertexWeight_nonnegative (f : WeightDirections μ) (hf : ‖f‖ < 1) :
    ∀ᵐ x ∂μ, 0 ≤ vertexWeight f x := by
  have hp := weight_nonnegative_of_norm_lt_one f.val hf
  filter_upwards [Lp.coeFn_add (Lp.const 2 μ (1 : ℝ)) (directionToL2 f),
    Lp.coeFn_const 2 μ (1 : ℝ), hp] with x ha hc hp
  change 0 ≤ (Lp.const 2 μ (1 : ℝ) + directionToL2 f) x
  rw [ha]
  change 0 ≤ (Lp.const 2 μ (1 : ℝ)) x + directionToL2 f x
  rw [hc]
  exact hp

/-- Unhalved pair mass under an actual vertex weight. -/
def weightedPairIntegral (K : Ω → Ω → ℝ) (f : Lp ℝ 2 μ) : ℝ :=
  ∫ z : Ω × Ω, K z.1 z.2 * f z.2 * f z.1 ∂μ.prod μ

theorem weightedPairIntegral_eq (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (f : Lp ℝ 2 μ) :
    weightedPairIntegral K f = ⟪KernelOperator.operator K hB0 hK hB f, f⟫ :=
  (KernelOperator.operator_inner K hB0 hK hB f f).symm

/-- Actual pair-integral local maximality gives stationarity and positive
index at most two for the actual shifted kernel. The regularity and local
maximality hypotheses remain explicit hypotheses on the model. -/
theorem exists_stationary_kernel_of_weight_local_max
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (A Y : Ω → Ω → ℝ) {B C : ℝ} (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hA : AEStronglyMeasurable (fun z : Ω × Ω => A z.1 z.2) (μ.prod μ))
    (hY : AEStronglyMeasurable (fun z : Ω × Ω => Y z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖A z.1 z.2‖ ≤ B)
    (hC : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖Y z.1 z.2‖ ≤ C)
    (hAsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, A z.1 z.2 = A z.2 z.1)
    (hYsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, Y z.1 z.2 = Y z.2 z.1)
    (hregular : weightFirstVariation (KernelOperator.operator A hB0 hA hB) ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hmax : ∀ f : WeightDirections μ, ‖f‖ < ε →
      weightedPairIntegral A (vertexWeight f) = weightedPairIntegral A (Lp.const 2 μ (1 : ℝ)) →
      weightedPairIntegral Y (vertexWeight f) ≤ weightedPairIntegral Y (Lp.const 2 μ (1 : ℝ))) :
    ∃ m ν D : ℝ, ∃ hD0 : 0 ≤ D,
      ∃ hM : AEStronglyMeasurable (fun z : Ω × Ω => Y z.1 z.2 - m * A z.1 z.2) (μ.prod μ),
      ∃ hD : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖Y z.1 z.2 - m * A z.1 z.2‖ ≤ D,
      (∀ᵐ x ∂μ, (∫ y, Y x y - m * A x y ∂μ) = ν) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace
        (KernelOperator.operator (fun x y => Y x y - m * A x y) hD0 hM hD)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace
        (KernelOperator.operator (fun x y => Y x y - m * A x y) hD0 hM hD)) ≤ 2 := by
  let TA := KernelOperator.operator A hB0 hA hB
  let TY := KernelOperator.operator Y hC0 hY hC
  have hmax' : ∀ f : WeightDirections μ, ‖f‖ < ε →
      ⟪TA (Lp.const 2 μ (1 : ℝ) + directionToL2 f), Lp.const 2 μ (1 : ℝ) + directionToL2 f⟫ =
        ⟪TA (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ →
      ⟪TY (Lp.const 2 μ (1 : ℝ) + directionToL2 f), Lp.const 2 μ (1 : ℝ) + directionToL2 f⟫ ≤
        ⟪TY (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ := by
    intro f hf he
    have hh := hmax f hf
    simp only [weightedPairIntegral_eq A hB0 hA hB, weightedPairIntegral_eq Y hC0 hY hC,
      vertexWeight] at hh
    exact hh he
  obtain ⟨m, ν, _, hrow, hfinite, hindex⟩ := exists_stationary_shift_of_weight_local_max TA TY
    (KernelOperator.operator_isCompact A hB0 hA hB) (KernelOperator.operator_isCompact Y hC0 hY hC)
    (KernelOperator.operator_symmetric A hB0 hA hB hAsym)
    (KernelOperator.operator_symmetric Y hC0 hY hC hYsym)
    (KernelOperator.operator_range_bounded A hB0 hA hB)
    (KernelOperator.operator_range_bounded Y hC0 hY hC) hregular ε hε hεone hmax'
  let D := C + ‖m‖ * B
  have hD0 : 0 ≤ D := add_nonneg hC0 (mul_nonneg (norm_nonneg m) hB0)
  have hM := hY.sub (hA.const_mul m)
  have hD := KernelOperator.kernel_sub_bound (K := Y) (L := fun x y => m * A x y)
    hC (KernelOperator.kernel_smul_bound hB m)
  have hop : KernelOperator.operator (fun x y => Y x y - m * A x y) hD0 hM hD = TY - m • TA := by
    rw [KernelOperator.operator_sub Y (fun x y => m * A x y) hC0
      (mul_nonneg (norm_nonneg m) hB0) hY (hA.const_mul m) hC (KernelOperator.kernel_smul_bound hB m),
      KernelOperator.operator_smul_kernel A hB0 hA hB m]
  refine ⟨m, ν, D, hD0, hM, hD, ?_, ?_, ?_⟩
  · apply KernelOperator.stationary_of_constant_one_eigenvector _ hD0 hM hD ν
    rwa [hop]
  · rwa [hop]
  · rwa [hop]

end Erdos1017.Variation
