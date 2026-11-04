module

public import Erdos1017.SelectedModel.Selection.FullStrictSupport
public import Erdos1017.SelectedModel.Selection.FullPositiveGamma

/-!
# Consequences of a positive mean-zero eigenvector

At a regular full extremizer, the tangent inequality fixes the stationary
multiplier, a positive bounded mean-zero direction is transverse to adjacency,
and a positive mean-zero eigenvector gives strict support and positive gamma.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The tangent inequality belongs to the same stationary multiplier: the
regular first variation makes that scalar unique. -/
theorem full_regular_tangent_nonpositive (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
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
    have h := full_weight_local_max W hW hopt g hg hd'
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
theorem full_positive_direction_transverse (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m : ℝ) (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (u : Variation.WeightDirections μ)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u) :
    Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0 := by
  intro hu
  exact (not_le_of_gt hq) (full_regular_tangent_nonpositive W hW hopt m hfirst hregular u hu)

/-- True full-model extremality and a supplied positive meanzero
eigenvector imply strict support through the actual full edit comparison. -/
theorem full_strict_support_of_positive_eigenvector (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
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
  exact full_strict_support_of_stationary_positive_direction W hW hopt m ν hrow
    ⟨u, full_positive_direction_transverse W hW hopt m hfirst hregular u hq, hq⟩ hnonneg hcomp

/-- The actual universal competitor gives positive gamma for a genuine
full extremizer under the same regular positive-eigenvector hypotheses. -/
theorem full_gamma_pos_of_positive_eigenvector [StandardBorelSpace Ω] [NullSingletonClass μ]
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m ν : ℝ) (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (hdhalf : density W < 1 / 2)
    (w : Lp ℝ 2 μ) (hw : w ≠ 0) (hmean : (∫ x, w x ∂μ) = 0)
    (σ : ℝ) (hσ : 0 < σ) (heigen : shiftedOperator W m w = σ • w) : 0 < ν + m := by
  have hfirst := shiftedFirstVariation_zero_of_stationary W m ν hrow
  obtain ⟨u, hq⟩ := exists_positive_direction_of_eigenvector W m w hw hmean σ hσ heigen
  exact full_gamma_pos_of_stationary_positive_direction W hW hopt m ν hrow hdhalf
    ⟨u, full_positive_direction_transverse W hW hopt m hfirst hregular u hq, hq⟩

end Erdos1017.CappedModel
