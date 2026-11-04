module

public import Erdos1017.SelectedModel.Selection.FullUniversalComparison

/-!
# Positivity of gamma for full optimizers

Universal vertices and exact density-restoring vertex weights force
`gamma = nu + m` to be positive whenever the bounded transverse shifted
direction is positive, also in the stationary case.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Actual universal vertices and exact density-restoring vertex weights
force positive `gamma=nu+m` whenever the bounded transverse shifted
direction is positive and the density is below one half. -/
theorem full_gamma_pos_of_positive_direction (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m ν : ℝ) (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hdhalf : density W < 1 / 2)
    (u : Variation.WeightDirections μ)
    (hu : 0 < Variation.weightFirstVariation (adjacencyOperator W) u)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u) : 0 < ν + m := by
  have hfirst := shiftedFirstVariation_zero_of_stationary W m ν hrow
  have hν := shifted_stationary_value W m ν hrow
  let ε := 1 / (‖u‖ + 1)
  have hε : 0 < ε := div_pos (by norm_num) (by positivity)
  have hεeq : ε * (‖u‖ + 1) = 1 := div_mul_cancel₀ _ (by positivity : ‖u‖ + 1 ≠ 0)
  have hγ : 0 < 2 * (objective W - m * density W) + m := by
    apply Variation.gamma_pos_of_universal_comparison (2 * (1 - 2 * density W))
      (Variation.weightFirstVariation (adjacencyOperator W) u)
      (Variation.weightSecondVariation (adjacencyOperator W) u u)
      (Variation.weightSecondVariation (shiftedOperator W m) u u) _ (by linarith) hu hq ε hε
    intro τ s hτ _ hs hroot
    have hnorm : ‖s • u‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hmul := mul_le_mul_of_nonneg_right hs.le (norm_nonneg u)
      nlinarith
    exact full_universal_reweight_comparison W hW hopt m hfirst u τ s hτ hnorm hroot
  rwa [← hν] at hγ

theorem full_gamma_pos_of_stationary_positive_direction (W : Model Ω μ)
    (hW : FullFeasible W) (hopt : objective W = FractionalGraph.densityLimit (density W)) (m ν : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hdhalf : density W < 1 / 2)
    (hpositive : ∃ u : Variation.WeightDirections μ,
      Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0 ∧
        0 < Variation.weightSecondVariation (shiftedOperator W m) u u) : 0 < ν + m := by
  obtain ⟨u, hu, hq⟩ := hpositive
  rcases lt_or_gt_of_ne hu with hu | hu
  · apply full_gamma_pos_of_positive_direction W hW hopt m ν hrow hdhalf (-u)
    · simpa only [map_neg] using neg_pos.mpr hu
    · simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hq
  · exact full_gamma_pos_of_positive_direction W hW hopt m ν hrow hdhalf u hu hq

end Erdos1017.CappedModel
