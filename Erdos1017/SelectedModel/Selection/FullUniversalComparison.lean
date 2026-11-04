module

public import Erdos1017.Models.Selection.FullModelEdits
public import Erdos1017.Models.Capped.CappedUniversalValues
public import Erdos1017.Models.Selection.QuadraticUniversalCorrection

/-!
# Comparison with the universal-vertex competitor

The universal-vertex competitor after bounded reweighting gives an exact shifted
second-variation comparison, including normalization, together with the
canonical mass of the adjoined universal vertex.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem exists_full_canonical_adjoinUniversal_mass [StandardBorelSpace Ω] [NullSingletonClass μ]
    {ν : Measure Ω} [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (W : Model Ω ν) (hW : FullFeasible W) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ V : Model Ω μ, FullFeasible V ∧
      density V = (density W + τ + τ ^ 2 / 2) / (1 + τ) ^ 2 ∧
      objective V = objective W / (1 + τ) ^ 2 := by
  let t := universalFraction τ hτ
  have : NullSingletonClass (universalMeasure ν t) := by unfold universalMeasure; infer_instance
  obtain ⟨h, hh⟩ := exists_measurePreserving (Ω := Ω) (Λ := Ω × Bool)
    (μ := μ) (ν := universalMeasure ν t)
  refine ⟨(adjoinUniversal W t).pullback h hh,
    (fun r => feasible_pullback _ (feasible_adjoinUniversal W (hW r) t) h hh), ?_, ?_⟩
  · rw [density_pullback]
    exact density_adjoinUniversal_mass W τ hτ
  · rw [objective_pullback]
    exact objective_adjoinUniversal_mass W τ hτ

/-- The actual universal-vertex competitor after bounded reweighting gives
the exact shifted second-variation comparison, including normalization. -/
theorem full_universal_reweight_comparison [StandardBorelSpace Ω] [NullSingletonClass μ]
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W)) (m : ℝ)
    (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (u : Variation.WeightDirections μ) (τ s : ℝ) (hτ : 0 ≤ τ) (hnorm : ‖s • u‖ < 1)
    (hroot : 2 * (1 - 2 * density W) * (τ + τ ^ 2 / 2) +
      Variation.weightFirstVariation (adjacencyOperator W) u * s +
      Variation.weightSecondVariation (adjacencyOperator W) u u * s ^ 2 = 0) :
    Variation.weightSecondVariation (shiftedOperator W m) u u * s ^ 2 ≤
      2 * (2 * (objective W - m * density W) + m) * (τ + τ ^ 2 / 2) := by
  let ν := weightedMeasure (μ := μ) (Variation.vertexWeight (s • u))
  have : IsProbabilityMeasure ν := weightedMeasure_probability
    ((Lp.memLp (Variation.vertexWeight (s • u))).integrable (by norm_num))
    (Variation.vertexWeight_nonnegative (s • u) hnorm) (Variation.vertexWeight_integral (s • u))
  have hν : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have : NullSingletonClass ν := ⟨fun x => hν (measure_singleton x)⟩
  let U := reweight W (s • u) hnorm
  have hU : FullFeasible U := fullFeasible_reweight W hW (s • u) hnorm
  obtain ⟨V, hV, hdV, hcV⟩ := exists_full_canonical_adjoinUniversal_mass (μ := μ) U hU τ hτ
  have hdU : density U = density W +
      (Variation.weightFirstVariation (adjacencyOperator W) u * s +
        Variation.weightSecondVariation (adjacencyOperator W) u u * s ^ 2) / 2 := by
    have h := density_reweight W (s • u) hnorm
    change density U = Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight (s • u)) / 2 at h
    rw [weighted_adjacency_eq, Variation.weight_curve_expansion _ (adjacencyOperator_symmetric W),
      adjacency_constant_inner] at h
    linarith
  have hden : density V = density W := by
    rw [hdV, hdU]
    apply (div_eq_iff (by positivity : (1 + τ) ^ 2 ≠ 0)).mpr
    nlinarith [hroot]
  have hmax := full_objective_le_of_density_eq W hopt μ V hV hden
  rw [hcV] at hmax
  have hcost : objective U ≤ objective W * (1 + τ) ^ 2 :=
    (div_le_iff₀ (by positivity : 0 < (1 + τ) ^ 2)).mp hmax
  have hm := firstVariation_identity_of_shifted_zero W m hfirst
  have hmfirst := LinearMap.congr_fun hm u
  simp only [LinearMap.smul_apply, smul_eq_mul] at hmfirst
  have hsecond : Variation.weightSecondVariation (shiftedOperator W m) u u =
      Variation.weightSecondVariation (chargeOperator W) u u -
        m * Variation.weightSecondVariation (adjacencyOperator W) u u := by
    change ⟪shiftedOperator W m (Variation.directionToL2 u), Variation.directionToL2 u⟫ = _
    rw [shiftedOperator_eq, sub_apply, smul_apply, inner_sub_left, real_inner_smul_left]
    rfl
  have hcU := objective_reweight W (s • u) hnorm
  change objective U = Variation.weightedPairIntegral (chargeKernel W) (Variation.vertexWeight (s • u)) / 2 at hcU
  rw [weighted_charge_eq, Variation.weight_curve_expansion _ (chargeOperator_symmetric W),
    charge_constant_inner] at hcU
  rw [hmfirst] at hcU
  rw [hsecond]
  linear_combination 2 * hcost - 2 * hcU - m * hroot

end Erdos1017.CappedModel
