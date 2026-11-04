module

public import Erdos1017.Models.Capped.CappedAffineEdit
public import Erdos1017.Models.Selection.QuadraticEditCorrection

/-!
# Edit multiplier from the mixed expansion

The exact mixed edit and vertex-weight expansion keeps the edit contribution to
the transverse derivative and quadratic coefficient, and every affine capped
edit obeys the same regular multiplier as the vertex directions
(`affine_edit_sign`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.Variation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem weight_curve_expansion (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : T.toLinearMap.IsSymmetric) (u : WeightDirections μ) (s : ℝ) :
    ⟪T (vertexWeight (s • u)), vertexWeight (s • u)⟫ =
      ⟪T (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ +
        weightFirstVariation T u * s + weightSecondVariation T u u * s ^ 2 := by
  change ⟪T (Lp.const 2 μ (1 : ℝ) + directionToL2 (s • u)),
    Lp.const 2 μ (1 : ℝ) + directionToL2 (s • u)⟫ = _
  rw [weighted_quadratic_expansion T hT]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The exact mixed edit/vertex expansion, retaining the edit contribution
to the transverse derivative and quadratic coefficient. -/
theorem affine_weight_curve_expansion (T₀ T₁ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT₀ : T₀.toLinearMap.IsSymmetric) (hT₁ : T₁.toLinearMap.IsSymmetric)
    (u : WeightDirections μ) (τ s : ℝ) :
    ⟪(T₀ + τ • (T₁ - T₀)) (vertexWeight (s • u)), vertexWeight (s • u)⟫ -
        ⟪T₀ (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ =
      (⟪T₁ (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ -
        ⟪T₀ (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫) * τ +
      (weightFirstVariation T₀ u + (weightFirstVariation T₁ u - weightFirstVariation T₀ u) * τ) * s +
      (weightSecondVariation T₀ u u +
        (weightSecondVariation T₁ u u - weightSecondVariation T₀ u u) * τ) * s ^ 2 := by
  simp only [add_apply, smul_apply, sub_apply, inner_add_left, inner_sub_left, real_inner_smul_left]
  rw [weight_curve_expansion T₀ hT₀, weight_curve_expansion T₁ hT₁]
  ring

end Erdos1017.Variation

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem adjacency_constant_inner (W : Model Ω μ) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ = 2 * density W := by
  rw [← weighted_adjacency_eq, weightedPairIntegral_one]
  unfold density adjacencyKernel
  ring

theorem charge_constant_inner (W : Model Ω μ) :
    ⟪chargeOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ = 2 * objective W := by
  rw [← weighted_charge_eq, weightedPairIntegral_one]
  unfold objective chargeKernel
  ring

/-- Every actual affine capped edit obeys the same regular multiplier as
the vertex directions. The comparison uses constructed feasible edited
models and exact quadratic vertex reweighting corrections. -/
theorem affine_edit_sign (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (E : AffineEdit W) (m : ℝ)
    (hm : Variation.weightFirstVariation (chargeOperator W) =
      m • Variation.weightFirstVariation (adjacencyOperator W))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0) :
    objective (E.model 1) - objective W - m * (density (E.model 1) - density W) ≤ 0 := by
  have hex : ∃ u, 0 < Variation.weightFirstVariation (adjacencyOperator W) u := by
    have hn : ∃ u, Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0 := by
      by_contra h
      push Not at h
      exact hregular (LinearMap.ext h)
    obtain ⟨u, hu⟩ := hn
    rcases lt_or_gt_of_ne hu with hu | hu
    · exact ⟨-u, by simpa using neg_pos.mpr hu⟩
    · exact ⟨u, hu⟩
  obtain ⟨u, hu⟩ := hex
  let T₀ := adjacencyOperator W
  let T₁ := adjacencyOperator (E.model 1)
  let S₀ := chargeOperator W
  let S₁ := chargeOperator (E.model 1)
  let one := Lp.const 2 μ (1 : ℝ)
  let a := ⟪T₁ one, one⟫ - ⟪T₀ one, one⟫
  let b := Variation.weightFirstVariation T₀ u
  let c := Variation.weightFirstVariation T₁ u - Variation.weightFirstVariation T₀ u
  let d := Variation.weightSecondVariation T₀ u u
  let e := Variation.weightSecondVariation T₁ u u - Variation.weightSecondVariation T₀ u u
  let A := ⟪S₁ one, one⟫ - ⟪S₀ one, one⟫
  let B := Variation.weightFirstVariation S₀ u
  let C := Variation.weightFirstVariation S₁ u - Variation.weightFirstVariation S₀ u
  let D := Variation.weightSecondVariation S₀ u u
  let F := Variation.weightSecondVariation S₁ u u - Variation.weightSecondVariation S₀ u u
  let ε := 1 / (‖u‖ + 1)
  have hε : 0 < ε := div_pos (by norm_num) (by positivity)
  have hεone : ε ≤ 1 := (div_le_one (by positivity : 0 < ‖u‖ + 1)).mpr (by linarith [norm_nonneg u])
  have hεeq : ε * (‖u‖ + 1) = 1 := div_mul_cancel₀ _ (by positivity : ‖u‖ + 1 ≠ 0)
  have hB : B = m * b := by
    have h := LinearMap.congr_fun hm u
    simpa only [LinearMap.smul_apply, smul_eq_mul] using h
  have hsign : A - m * a ≤ 0 := by
    apply Variation.edit_sign_of_local_max a b c d e A B C D F m hu hB ε hε
    intro τ s hτ hτε hs hroot
    let t : unitInterval := ⟨τ, hτ, (hτε.trans_le hεone).le⟩
    have hnorm : ‖s • u‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hmul := mul_le_mul_of_nonneg_right hs.le (norm_nonneg u)
      have hpos := mul_pos hε (by norm_num : (0 : ℝ) < 1)
      nlinarith
    have hden := Variation.affine_weight_curve_expansion T₀ T₁
      (adjacencyOperator_symmetric W) (adjacencyOperator_symmetric (E.model 1)) u τ s
    have hcost := Variation.affine_weight_curve_expansion S₀ S₁
      (chargeOperator_symmetric W) (chargeOperator_symmetric (E.model 1)) u τ s
    have hden0 : ⟪adjacencyOperator (E.model t) (Variation.vertexWeight (s • u)),
        Variation.vertexWeight (s • u)⟫ = ⟪T₀ one, one⟫ := by
      rw [adjacencyOperator_affine]
      change ⟪(T₀ + τ • (T₁ - T₀)) (Variation.vertexWeight (s • u)),
        Variation.vertexWeight (s • u)⟫ = _
      change a * τ + (b + c * τ) * s + (d + e * τ) * s ^ 2 = 0 at hroot
      change _ = a * τ + (b + c * τ) * s + (d + e * τ) * s ^ 2 at hden
      linarith
    have := weightedMeasure_probability ((Lp.memLp (Variation.vertexWeight (s • u))).integrable (by norm_num))
      (Variation.vertexWeight_nonnegative (s • u) hnorm) (Variation.vertexWeight_integral (s • u))
    have hfeas := feasible_reweight (E.model t) (E.feasible r hW.1 t) (s • u) hnorm
    have hd : density (reweight (E.model t) (s • u) hnorm) = density W := by
      have h := density_reweight (E.model t) (s • u) hnorm
      change density (reweight (E.model t) (s • u) hnorm) =
        Variation.weightedPairIntegral (adjacencyKernel (E.model t)) (Variation.vertexWeight (s • u)) / 2 at h
      rw [weighted_adjacency_eq, hden0] at h
      change _ = ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ / 2 at h
      rw [adjacency_constant_inner] at h
      linarith
    have hmax := hW.2 (weightedMeasure (μ := μ) (Variation.vertexWeight (s • u)))
      (withDensity_absolutelyContinuous _ _) (reweight (E.model t) (s • u) hnorm) hfeas hd
    have hc := objective_reweight (E.model t) (s • u) hnorm
    change objective (reweight (E.model t) (s • u) hnorm) =
      Variation.weightedPairIntegral (chargeKernel (E.model t)) (Variation.vertexWeight (s • u)) / 2 at hc
    rw [weighted_charge_eq, chargeOperator_affine] at hc
    change _ = ⟪(S₀ + τ • (S₁ - S₀)) (Variation.vertexWeight (s • u)),
      Variation.vertexWeight (s • u)⟫ / 2 at hc
    have hbase : ⟪S₀ one, one⟫ = 2 * objective W := charge_constant_inner W
    change _ = A * τ + (B + C * τ) * s + (D + F * τ) * s ^ 2 at hcost
    linarith
  change (⟪chargeOperator (E.model 1) (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ -
    ⟪chargeOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫) -
      m * (⟪adjacencyOperator (E.model 1) (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ -
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫) ≤ 0 at hsign
  rw [charge_constant_inner, charge_constant_inner, adjacency_constant_inner, adjacency_constant_inner] at hsign
  nlinarith

end Erdos1017.CappedModel
