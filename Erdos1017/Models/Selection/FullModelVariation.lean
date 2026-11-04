module

public import Erdos1017.Models.Capped.CappedGrowingLimit
public import Erdos1017.Models.Capped.CappedKernelOperator
public import Erdos1017.Models.Kernel.KernelScalarPerturbation

/-!
# Vertex-weight variations of a full extremizer

Vertex reweighting preserves every sampled clique constraint of a fully feasible
model, and a full extremizer satisfies the local vertex-weight quadratic
comparison, which supplies a regular multiplier with positive index at most two
(`exists_full_regular_multiplier`), and in the constant-degree branch forces the
first vertex-weight variation of the charge operator to vanish
(`full_singular_charge_firstVariation_zero`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual vertex reweighting preserves every sampled clique constraint of a
fully feasible decorated model. -/
theorem fullFeasible_reweight (W : Model Ω μ) (hW : FullFeasible W)
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) :
    FullFeasible (reweight W f hf) :=
  fun r => feasible_reweight W (hW r) f hf

/-- A full extremizer satisfies the exact-density local vertex-weight
quadratic comparison without a capped maximality premise. -/
theorem full_weight_local_max (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1)
    (hd : Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight f) =
      Variation.weightedPairIntegral (adjacencyKernel W) (Lp.const 2 μ (1 : ℝ))) :
    Variation.weightedPairIntegral (chargeKernel W) (Variation.vertexWeight f) ≤
      Variation.weightedPairIntegral (chargeKernel W) (Lp.const 2 μ (1 : ℝ)) := by
  have : IsProbabilityMeasure (weightedMeasure (μ := μ) (Variation.vertexWeight f)) :=
    weightedMeasure_probability
      ((Lp.memLp (Variation.vertexWeight f)).integrable (by norm_num))
      (Variation.vertexWeight_nonnegative f hf) (Variation.vertexWeight_integral f)
  have hfull := fullFeasible_reweight W hW f hf
  have hbound := fullFeasible_objective_le_densityLimit (reweight W f hf) hfull
  have hd' : density (reweight W f hf) = density W := by
    rw [density_reweight W f hf]
    change Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight f) / 2 =
      density W
    rw [hd, weightedPairIntegral_one]
    rfl
  have hc : objective W = Variation.weightedPairIntegral (chargeKernel W)
      (Lp.const 2 μ (1 : ℝ)) / 2 := by
    rw [weightedPairIntegral_one]
    rfl
  rw [hd', ← hopt, objective_reweight W f hf] at hbound
  change Variation.weightedPairIntegral (chargeKernel W) (Variation.vertexWeight f) / 2 ≤
    objective W at hbound
  rw [hc] at hbound
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mp hbound

/-- The full-model bound and the finite-graph limit's three-Lipschitz law
give the singular branch's local quadratic comparison. -/
theorem full_weight_lipschitz_max (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) :
    Variation.weightedPairIntegral (chargeKernel W) (Variation.vertexWeight f) -
      Variation.weightedPairIntegral (chargeKernel W) (Lp.const 2 μ (1 : ℝ)) ≤
      3 * |Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight f) -
        Variation.weightedPairIntegral (adjacencyKernel W) (Lp.const 2 μ (1 : ℝ))| := by
  have : IsProbabilityMeasure (weightedMeasure (μ := μ) (Variation.vertexWeight f)) :=
    weightedMeasure_probability
      ((Lp.memLp (Variation.vertexWeight f)).integrable (by norm_num))
      (Variation.vertexWeight_nonnegative f hf) (Variation.vertexWeight_integral f)
  have hfull := fullFeasible_reweight W hW f hf
  have hbound := fullFeasible_objective_le_densityLimit (reweight W f hf) hfull
  have hlip := FractionalGraph.densityLimit_le_add
    (density (reweight W f hf)) (density W)
  have hd : density W = Variation.weightedPairIntegral (adjacencyKernel W)
      (Lp.const 2 μ (1 : ℝ)) / 2 := by
    rw [weightedPairIntegral_one]
    rfl
  have hc : objective W = Variation.weightedPairIntegral (chargeKernel W)
      (Lp.const 2 μ (1 : ℝ)) / 2 := by
    rw [weightedPairIntegral_one]
    rfl
  rw [density_reweight W f hf] at hbound hlip
  rw [objective_reweight W f hf] at hbound
  change Variation.weightedPairIntegral (chargeKernel W) (Variation.vertexWeight f) / 2 ≤
    FractionalGraph.densityLimit
      (Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight f) / 2) at hbound
  change FractionalGraph.densityLimit
      (Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight f) / 2) ≤
    FractionalGraph.densityLimit (density W) +
      3 * |Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight f) / 2 -
        density W| at hlip
  rw [← hopt, hd, hc, ← sub_div, abs_div] at hlip
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hlip
  linarith

/-- Full-model extremality supplies the regular first-variation identity,
stationary shifted operator, and positive spectral index at most two. -/
theorem exists_full_regular_multiplier [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0) :
    ∃ m ν : ℝ,
      Variation.weightFirstVariation (chargeOperator W) =
        m • Variation.weightFirstVariation (adjacencyOperator W) ∧
      (chargeOperator W - m • adjacencyOperator W) (Lp.const 2 μ (1 : ℝ)) =
        ν • Lp.const 2 μ (1 : ℝ) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace
        (chargeOperator W - m • adjacencyOperator W)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace
        (chargeOperator W - m • adjacencyOperator W)) ≤ 2 := by
  apply Variation.exists_stationary_shift_of_weight_local_max
    (adjacencyOperator W) (chargeOperator W)
    (KernelOperator.operator_isCompact _ _ _ _) (KernelOperator.operator_isCompact _ _ _ _)
    (adjacencyOperator_symmetric W) (chargeOperator_symmetric W)
    (KernelOperator.operator_range_bounded _ _ _ _) (KernelOperator.operator_range_bounded _ _ _ _)
    hregular 1 (by norm_num) le_rfl
  intro f hf hd
  have hd' : Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight f) =
      Variation.weightedPairIntegral (adjacencyKernel W) (Lp.const 2 μ (1 : ℝ)) := by
    simpa only [weighted_adjacency_eq, Variation.vertexWeight] using hd
  have hc := full_weight_local_max W hW hopt f hf hd'
  simpa only [weighted_charge_eq, Variation.vertexWeight] using hc

/-- Constant adjacency degree and full-model optimality force the charge
operator's first vertex-weight variation to vanish. -/
theorem full_singular_charge_firstVariation_zero
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hsingular : ∃ c : ℝ, ∀ᵐ x ∂μ, (∫ y, adjacencyKernel W x y ∂μ) = c) :
    Variation.weightFirstVariation (chargeOperator W) = 0 := by
  apply (Variation.kernel_weightFirstVariation_eq_zero_iff
    (chargeKernel W) (by norm_num) (chargeKernel_measurable W) (chargeKernel_bound W)).mpr
  apply Variation.stationary_kernel_of_constant_degree_comparison
    (adjacencyKernel W) (chargeKernel W) (by norm_num) (by norm_num)
    (adjacencyKernel_measurable W) (chargeKernel_measurable W)
    (adjacencyKernel_bound W) (chargeKernel_bound W)
    (adjacencyKernel_symm W) (chargeKernel_symm W)
    hsingular 3 1 (by norm_num)
  intro f hf
  exact full_weight_lipschitz_max W hW hopt f hf

end Erdos1017.CappedModel
