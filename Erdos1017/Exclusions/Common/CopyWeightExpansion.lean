module

public import Erdos1017.SelectedModel.Structure.IntegrableRelativeWeight
public import Erdos1017.Models.Capped.CappedEditMultiplier
public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative

/-!
# Density and objective along a vertex reweighting

Under a small bounded transverse reweighting of the vertex weights, every
bounded copied row integrates affinely, while the physical density and the
physical objective of the original model follow exact quadratic curves
(`physicalDensity_vertexWeight_curve`, `physicalObjective_vertexWeight_curve`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual bounded weight curve has its scalar affine representative
on one original almost-everywhere event. -/
theorem vertexWeight_curve_ae (u : Variation.WeightDirections μ) (s : ℝ) :
    Variation.vertexWeight (s • u) =ᵐ[μ]
      fun x => 1 + s * Variation.directionToL2 u x := by
  change (Lp.const 2 μ (1 : ℝ) + Variation.directionToL2 (s • u) : Lp ℝ 2 μ) =ᵐ[μ] _
  rw [map_smul]
  filter_upwards [Lp.coeFn_add (Lp.const 2 μ (1 : ℝ)) (s • Variation.directionToL2 u),
    Lp.coeFn_const 2 μ (1 : ℝ), Lp.coeFn_smul s (Variation.directionToL2 u)]
    with x ha hc hs
  rw [ha]
  change (Lp.const 2 μ (1 : ℝ)) x + (s • Variation.directionToL2 u) x = _
  rw [hc, hs]
  rfl

/-- Every bounded copied row integrates affinely under the actual
transverse probability reweighting. -/
theorem integral_vertexWeight_curve (u : Variation.WeightDirections μ) (s : ℝ)
    (hs : ‖s • u‖ < 1) (f : Ω → ℝ) (hf : StronglyMeasurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ x, f x ∂weightedMeasure (μ := μ) (Variation.vertexWeight (s • u))) =
      (∫ x, f x ∂μ) + s * ∫ x, f x * Variation.directionToL2 u x ∂μ := by
  rw [integral_weightedMeasure_real _ (Lp.aestronglyMeasurable _).aemeasurable
    (Variation.vertexWeight_nonnegative _ hs)]
  have hi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable B
    (Eventually.of_forall hB)
  have hu : Integrable (fun x => f x * Variation.directionToL2 u x) μ :=
    ((Lp.memLp (Variation.directionToL2 u)).integrable (by norm_num)).bdd_mul
      hf.aestronglyMeasurable (Eventually.of_forall hB)
  have he : (fun x => Variation.vertexWeight (s • u) x * f x) =ᵐ[μ]
      fun x => f x + s * (f x * Variation.directionToL2 u x) := by
    filter_upwards [vertexWeight_curve_ae u s] with x hx
    rw [hx]
    ring
  rw [integral_congr_ae he, integral_add hi (hu.const_mul _), integral_const_mul]

/-- Original strict-support physical adjacency gives the same actual
quadratic density curve under every small bounded reweighting. -/
theorem physicalDensity_vertexWeight_curve (W : Model Ω μ) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (u : Variation.WeightDirections μ) (s : ℝ) (hs : ‖s • u‖ < 1) :
    FiniteCappedSamplingCost.physicalDensity
        (weightedMeasure (μ := μ) (Variation.vertexWeight (s • u)))
        (PhysicalRepresentative.adjacency W m) = density W +
      (Variation.weightFirstVariation (adjacencyOperator W) u * s +
        Variation.weightSecondVariation (adjacencyOperator W) u u * s ^ 2) / 2 := by
  let ν := weightedMeasure (μ := μ) (Variation.vertexWeight (s • u))
  have : IsProbabilityMeasure ν := weightedMeasure_probability
    ((Lp.memLp (Variation.vertexWeight (s • u))).integrable (by norm_num))
    (Variation.vertexWeight_nonnegative _ hs) (Variation.vertexWeight_integral _)
  have hac : ν.prod ν ≪ μ.prod μ :=
    (withDensity_absolutelyContinuous _ _).prod (withDensity_absolutelyContinuous _ _)
  have he : FiniteCappedSamplingCost.physicalDensity ν (PhysicalRepresentative.adjacency W m) =
      density (reweight W (s • u) hs) := by
    unfold FiniteCappedSamplingCost.physicalDensity density
    congr 1
    apply integral_congr_ae
    filter_upwards [hac.ae_le (PhysicalRepresentative.adjacency_moment_ae_eq W m hsupport)]
      with p hp
    exact hp.symm
  rw [he, density_reweight]
  change Variation.weightedPairIntegral (adjacencyKernel W)
    (Variation.vertexWeight (s • u)) / 2 = _
  rw [weighted_adjacency_eq,
    Variation.weight_curve_expansion _ (adjacencyOperator_symmetric W), adjacency_constant_inner]
  unfold density
  ring

/-- The original bounded symmetric physical charge has the same actual
quadratic objective curve; its multiplier is not changed by this identity. -/
theorem physicalObjective_vertexWeight_curve (W : Model Ω μ) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (u : Variation.WeightDirections μ) (s : ℝ) (hs : ‖s • u‖ < 1) :
    FiniteCappedSamplingCost.physicalObjective
        (weightedMeasure (μ := μ) (Variation.vertexWeight (s • u)))
        (PhysicalRepresentative.charge W m) = objective W +
      (Variation.weightFirstVariation (chargeOperator W) u * s +
        Variation.weightSecondVariation (chargeOperator W) u u * s ^ 2) / 2 := by
  let ν := weightedMeasure (μ := μ) (Variation.vertexWeight (s • u))
  have : IsProbabilityMeasure ν := weightedMeasure_probability
    ((Lp.memLp (Variation.vertexWeight (s • u))).integrable (by norm_num))
    (Variation.vertexWeight_nonnegative _ hs) (Variation.vertexWeight_integral _)
  have hac : ν.prod ν ≪ μ.prod μ :=
    (withDensity_absolutelyContinuous _ _).prod (withDensity_absolutelyContinuous _ _)
  have he : FiniteCappedSamplingCost.physicalObjective ν (PhysicalRepresentative.charge W m) =
      objective (reweight W (s • u) hs) := by
    unfold FiniteCappedSamplingCost.physicalObjective objective
    congr 1
    apply integral_congr_ae
    filter_upwards [hac.ae_le (PhysicalRepresentative.charge_ae_eq W m hsupport)] with p hp
    exact hp
  rw [he, objective_reweight]
  change Variation.weightedPairIntegral (chargeKernel W)
    (Variation.vertexWeight (s • u)) / 2 = _
  rw [weighted_charge_eq,
    Variation.weight_curve_expansion _ (chargeOperator_symmetric W), charge_constant_inner]
  unfold objective
  ring

end Erdos1017.CappedModel
