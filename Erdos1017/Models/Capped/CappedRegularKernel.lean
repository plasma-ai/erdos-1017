module

public import Erdos1017.Models.Capped.CappedRegularSelection

/-!
# The regular shifted kernel of a capped optimizer

The shifted kernel and its operator (`shiftedKernel`, `shiftedOperator`) are
measurable and bounded with a stationary value, and all regular spectral and
edge-sign conclusions hold for one shifted kernel of the capped optimizer
(`exists_regular_kernel`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def shiftedKernel (W : Model Ω μ) (m : ℝ) (x y : Ω) : ℝ := shiftedMoment W m (x, y)

theorem shiftedKernel_measurable (W : Model Ω μ) (m : ℝ) :
    AEStronglyMeasurable (fun p : Ω × Ω => shiftedKernel W m p.1 p.2) (μ.prod μ) :=
  (W.stronglyMeasurable_moment (continuous_shiftedColor m).measurable.stronglyMeasurable).aestronglyMeasurable

theorem shiftedKernel_bound (W : Model Ω μ) (m : ℝ) :
    ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel W m p.1 p.2‖ ≤ 3 + ‖m‖ := by
  filter_upwards with p
  have h := norm_integral_le_of_norm_le_const (μ := W.kernel p)
    (Filter.Eventually.of_forall (shiftedColor_norm_le m))
  simpa only [shiftedKernel, shiftedMoment, DecoratedKernel.moment, probReal_univ, mul_one] using h

variable [IsProbabilityMeasure μ]

def shiftedOperator (W : Model Ω μ) (m : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  KernelOperator.operator (shiftedKernel W m) (by positivity)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m)

theorem shiftedOperator_eq (W : Model Ω μ) (m : ℝ) :
    shiftedOperator W m = chargeOperator W - m • adjacencyOperator W := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  simp only [shiftedOperator, chargeOperator, adjacencyOperator, sub_apply, smul_apply,
    inner_sub_left, real_inner_smul_left, KernelOperator.operator_inner]
  have hy := KernelOperator.integrable_bilinear (chargeKernel_measurable W) (chargeKernel_bound W) f g
  have ha := KernelOperator.integrable_bilinear (adjacencyKernel_measurable W) (adjacencyKernel_bound W) f g
  calc
    _ = ∫ p : Ω × Ω, chargeKernel W p.1 p.2 * f p.2 * g p.1 -
        m * (adjacencyKernel W p.1 p.2 * f p.2 * g p.1) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards with p
      simp only [shiftedKernel, shiftedMoment_eq, chargeKernel, adjacencyKernel]
      ring
    _ = _ := by rw [integral_sub hy (ha.const_mul m), integral_const_mul]

theorem shifted_stationary_value (W : Model Ω μ) (m ν : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν) :
    ν = 2 * (objective W - m * density W) := by
  rw [← integral_shiftedMoment]
  rw [integral_prod _ (integrable_shiftedMoment W m)]
  calc
    ν = ∫ _x : Ω, ν ∂μ := by simp
    _ = _ := (integral_congr_ae hrow).symm

/-- All regular spectral and edge-sign conclusions hold for one actual
shifted kernel of the capped optimizer. -/
theorem exists_regular_kernel [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (hd0 : 0 < density W) (hdhalf : density W < 1 / 2) :
    ∃ m ν : ℝ, m ∈ Set.Icc (-3) 1 ∧
      Variation.weightFirstVariation (chargeOperator W) =
        m • Variation.weightFirstVariation (adjacencyOperator W) ∧
      (∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Set.Icc 0 4) ∧
      (∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) ∧
      (∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν) ∧
      ν = 2 * (objective W - m * density W) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 2 := by
  obtain ⟨m, ν, hm, heigen, hfinite, hindex⟩ := exists_regular_multiplier W hW hregular
  refine ⟨m, ν, regular_multiplier_bounds W hW m hm hregular hd0 hdhalf, hm,
    regular_shiftedMoment_mem W hW m hm hregular hd0 hdhalf,
    regular_shiftedMoment_complementary W hW m hm hregular, ?_⟩
  have hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν := by
    apply KernelOperator.stationary_of_constant_one_eigenvector _ (by positivity)
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m) ν
    change shiftedOperator W m (Lp.const 2 μ (1 : ℝ)) = _
    rwa [shiftedOperator_eq]
  refine ⟨hrow, shifted_stationary_value W m ν hrow, ?_, ?_⟩
  · rwa [shiftedOperator_eq]
  · rwa [shiftedOperator_eq]

end Erdos1017.CappedModel
