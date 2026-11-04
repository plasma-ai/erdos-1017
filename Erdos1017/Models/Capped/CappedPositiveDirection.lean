module

public import Erdos1017.Models.Capped.CappedStrictSupport

/-!
# Positive directions from positive eigenvectors

The regular first variation makes the stationary multiplier unique, any positive
bounded mean-zero direction is transverse to adjacency in the regular case, and
a positive mean-zero eigenvector of the bounded shifted kernel produces a
bounded mean-zero direction with positive second variation, giving strict
support.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem firstVariation_identity_of_shifted_zero (W : Model Ω μ) (m : ℝ)
    (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0) :
    Variation.weightFirstVariation (chargeOperator W) =
      m • Variation.weightFirstVariation (adjacencyOperator W) := by
  apply LinearMap.ext
  intro f
  have h := LinearMap.congr_fun hfirst f
  change 2 * ⟪shiftedOperator W m (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 f⟫ = 0 at h
  rw [shiftedOperator_eq, sub_apply, smul_apply, inner_sub_left, real_inner_smul_left] at h
  change 2 * ⟪chargeOperator W (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 f⟫ =
    m * (2 * ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 f⟫)
  linarith

/-- The tangent inequality belongs to the same stationary multiplier: the
regular first variation makes that scalar unique. -/
theorem regular_tangent_nonpositive (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (m : ℝ) (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (f : Variation.WeightDirections μ)
    (hf : Variation.weightFirstVariation (adjacencyOperator W) f = 0) :
    Variation.weightSecondVariation (shiftedOperator W m) f f ≤ 0 := by
  have hlocal : ∀ g : Variation.WeightDirections μ, ‖g‖ < 1 →
      ⟪adjacencyOperator W (Variation.vertexWeight g), Variation.vertexWeight g⟫ =
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ →
      ⟪chargeOperator W (Variation.vertexWeight g), Variation.vertexWeight g⟫ ≤
        ⟪chargeOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ := by
    intro g hg hd
    have hd' : Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight g) =
        Variation.weightedPairIntegral (adjacencyKernel W) (Lp.const 2 μ (1 : ℝ)) := by
      simpa only [weighted_adjacency_eq] using hd
    have h := weight_local_max W hW g hg hd'
    change Variation.weightedPairIntegral (chargeKernel W) (Variation.vertexWeight g) ≤
      Variation.weightedPairIntegral (chargeKernel W) (Lp.const 2 μ (1 : ℝ)) at h
    simpa only [weighted_charge_eq] using h
  obtain ⟨m', hm', hquad, _⟩ := Variation.exists_multiplier_of_weight_local_max
    (adjacencyOperator W) (chargeOperator W) (adjacencyOperator_symmetric W)
    (chargeOperator_symmetric W) hregular 1 (by norm_num) le_rfl hlocal
  have hm := firstVariation_identity_of_shifted_zero W m hfirst
  have hex : ∃ u : Variation.WeightDirections μ,
      Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0 := by
    by_contra h
    push Not at h
    exact hregular (LinearMap.ext h)
  obtain ⟨u, hu⟩ := hex
  have heq := LinearMap.congr_fun (hm'.symm.trans hm) u
  simp only [LinearMap.smul_apply, smul_eq_mul] at heq
  have hscalar : m' = m := (mul_eq_mul_right_iff.mp heq).resolve_right hu
  have h := hquad f hf
  rw [hscalar, ← shiftedOperator_eq] at h
  exact h

/-- Any positive bounded meanzero direction is transverse to adjacency in
the regular case, as required by the actual strict-support construction. -/
theorem positive_direction_transverse (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (m : ℝ) (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (u : Variation.WeightDirections μ)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u) :
    Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0 := by
  intro hu
  exact (not_le_of_gt hq) (regular_tangent_nonpositive W hW m hfirst hregular u hu)

/-- A supplied positive meanzero eigenvector of the actual bounded shifted
kernel produces an actual bounded meanzero direction with positive second
variation. Boundedness follows from the integral operator's range. -/
theorem exists_positive_direction_of_eigenvector (W : Model Ω μ) (m : ℝ)
    (w : Lp ℝ 2 μ) (hw : w ≠ 0) (hmean : (∫ x, w x ∂μ) = 0)
    (σ : ℝ) (hσ : 0 < σ) (heigen : shiftedOperator W m w = σ • w) :
    ∃ u : Variation.WeightDirections μ,
      0 < Variation.weightSecondVariation (shiftedOperator W m) u u := by
  have hbounded : w ∈ KernelOperator.boundedL2Submodule μ := by
    have hrange : shiftedOperator W m w ∈ KernelOperator.boundedL2Submodule μ :=
      KernelOperator.operator_range_bounded _ _ _ _ w
    have h := (KernelOperator.boundedL2Submodule μ).smul_mem σ⁻¹
      hrange
    rwa [heigen, inv_smul_smul₀ hσ.ne'] at h
  obtain ⟨u, hu⟩ := Variation.exists_direction_of_bounded_mean_zero w hbounded hmean
  refine ⟨u, ?_⟩
  change 0 < ⟪shiftedOperator W m (Variation.directionToL2 u), Variation.directionToL2 u⟫
  rw [hu, heigen, real_inner_smul_left]
  rw [real_inner_self_eq_norm_sq]
  exact mul_pos hσ (sq_pos_of_pos (norm_pos_iff.mpr hw))

theorem strict_support_of_positive_eigenvector (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (m ν : ℝ) (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (w : Lp ℝ 2 μ) (hw : w ≠ 0) (hmean : (∫ x, w x ∂μ) = 0)
    (σ : ℝ) (hσ : 0 < σ) (heigen : shiftedOperator W m w = σ • w)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      (if 0 < shiftedMoment W m p then 1 else 0) := by
  have hfirst := shiftedFirstVariation_zero_of_stationary W m ν hrow
  obtain ⟨u, hq⟩ := exists_positive_direction_of_eigenvector W m w hw hmean σ hσ heigen
  exact strict_support_of_stationary_positive_direction W hW m ν hrow
    ⟨u, positive_direction_transverse W hW m hfirst hregular u hq, hq⟩ hnonneg hcomp

end Erdos1017.CappedModel
