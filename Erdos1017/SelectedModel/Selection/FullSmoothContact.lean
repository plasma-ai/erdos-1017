module

public import Erdos1017.Models.Selection.FullGlobalExcess
public import Erdos1017.SelectedModel.Selection.QuadraticSmoothContact

/-!
# Smooth benchmark contact of a full optimum

Reweighted density and objective are exact quadratic polynomials in a bounded
mean-zero direction, so global benchmark maximality gives the first variation
and the unhalved curvature bound in every bounded mean-zero direction,
identifying the stationary multiplier with the benchmark derivative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual reweighted density is an exact quadratic polynomial in the
bounded mean-zero direction, with the original model's own operators. -/
theorem density_reweight_smul (W : Model Ω μ) (f : Variation.WeightDirections μ)
    (t : ℝ) (ht : ‖t • f‖ < 1) :
    density (reweight W (t • f) ht) = density W +
      t * (Variation.weightFirstVariation (adjacencyOperator W) f / 2) +
      t ^ 2 * Variation.weightSecondVariation (adjacencyOperator W) f f / 2 := by
  rw [density_reweight]
  change Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight (t • f)) / 2 = _
  rw [weighted_adjacency_eq, Variation.vertexWeight,
    Variation.weighted_quadratic_expansion _ (adjacencyOperator_symmetric W),
    adjacency_constant_inner]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The original charge under the same genuine vertex reweighting has its
exact objective polynomial, including the unhalved second variation. -/
theorem objective_reweight_smul (W : Model Ω μ) (f : Variation.WeightDirections μ)
    (t : ℝ) (ht : ‖t • f‖ < 1) :
    objective (reweight W (t • f) ht) = objective W +
      t * (Variation.weightFirstVariation (chargeOperator W) f / 2) +
      t ^ 2 * Variation.weightSecondVariation (chargeOperator W) f f / 2 := by
  rw [objective_reweight]
  change Variation.weightedPairIntegral (chargeKernel W) (Variation.vertexWeight (t • f)) / 2 = _
  rw [weighted_charge_eq, Variation.vertexWeight,
    Variation.weighted_quadratic_expansion _ (chargeOperator_symmetric W),
    charge_constant_inner]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Global benchmark excess maximality compares the actual reweighted
fully feasible models for both signs of every bounded mean-zero direction. -/
theorem full_benchmark_reweight_local_max (W : Model Ω μ) (hW : FullFeasible W)
    (hmax : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) (f : Variation.WeightDirections μ) :
    IsLocalMax (fun t : ℝ => objective W +
      t * (Variation.weightFirstVariation (chargeOperator W) f / 2) +
      t ^ 2 * Variation.weightSecondVariation (chargeOperator W) f f / 2 -
      benchmark (density W + t * (Variation.weightFirstVariation (adjacencyOperator W) f / 2) +
        t ^ 2 * Variation.weightSecondVariation (adjacencyOperator W) f f / 2)) 0 := by
  have hcont : ContinuousAt (fun t : ℝ => ‖t • f‖) 0 := by fun_prop
  have hsmall : ∀ᶠ t : ℝ in nhds 0, ‖t • f‖ < 1 :=
    hcont.eventually (eventually_lt_nhds (by simp))
  filter_upwards [hsmall] with t ht
  have : IsProbabilityMeasure
      (weightedMeasure (μ := μ) (Variation.vertexWeight (t • f))) :=
    weightedMeasure_probability
      ((Lp.memLp (Variation.vertexWeight (t • f))).integrable (by norm_num))
      (Variation.vertexWeight_nonnegative (t • f) ht) (Variation.vertexWeight_integral (t • f))
  have h := hmax _ (reweight W (t • f) ht) (fullFeasible_reweight W hW (t • f) ht)
  rw [density_reweight_smul, objective_reweight_smul] at h
  simpa only [zero_mul, zero_pow (by omega : 2 ≠ 0), add_zero, zero_div] using h

/-- Smooth global benchmark contact derives the first variation from the
actual model comparison, without differentiating the fractional limit. -/
theorem full_benchmark_first_variation (W : Model Ω μ) (hW : FullFeasible W)
    (hmax : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    {β : ℝ} (hB : HasDerivAt benchmark β (density W)) :
    Variation.weightFirstVariation (chargeOperator W) =
      β • Variation.weightFirstVariation (adjacencyOperator W) := by
  apply LinearMap.ext
  intro f
  have h := SmoothContact.quadratic_first_variation hB
    (full_benchmark_reweight_local_max W hW hmax f)
  simp only [LinearMap.smul_apply, smul_eq_mul]
  linarith

/-- The actual smooth contact controls the unhalved shifted quadratic form
for every bounded mean-zero direction, including density-changing ones. -/
theorem full_benchmark_curvature (W : Model Ω μ) (hW : FullFeasible W)
    (hmax : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hB : ContDiffAt ℝ 2 benchmark (density W)) (f : Variation.WeightDirections μ) :
    ⟪(chargeOperator W - deriv benchmark (density W) • adjacencyOperator W)
        (Variation.directionToL2 f), Variation.directionToL2 f⟫ ≤
      deriv (deriv benchmark) (density W) *
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 f⟫ ^ 2 := by
  have h := SmoothContact.quadratic_curvature hB (full_benchmark_reweight_local_max W hW hmax f)
  change Variation.weightSecondVariation (chargeOperator W) f f -
    deriv benchmark (density W) * Variation.weightSecondVariation (adjacencyOperator W) f f ≤
      deriv (deriv benchmark) (density W) *
        (Variation.weightFirstVariation (adjacencyOperator W) f / 2) ^ 2 at h
  have hfirst : Variation.weightFirstVariation (adjacencyOperator W) f / 2 =
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 f⟫ := by
    change (2 * ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 f⟫) / 2 = _
    ring
  rw [hfirst] at h
  change ⟪chargeOperator W (Variation.directionToL2 f), Variation.directionToL2 f⟫ -
    deriv benchmark (density W) *
      ⟪adjacencyOperator W (Variation.directionToL2 f), Variation.directionToL2 f⟫ ≤ _ at h
  simpa only [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left] using h

/-- Every bounded mean-zero L² class is covered by the actual curvature
inequality; no degree-tangency condition is imposed. -/
theorem full_benchmark_curvature_bounded (W : Model Ω μ) (hW : FullFeasible W)
    (hmax : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hB : ContDiffAt ℝ 2 benchmark (density W)) (f : Lp ℝ 2 μ)
    (hf : f ∈ KernelOperator.boundedL2Submodule μ) (hmean : (∫ x, f x ∂μ) = 0) :
    ⟪(chargeOperator W - deriv benchmark (density W) • adjacencyOperator W) f, f⟫ ≤
      deriv (deriv benchmark) (density W) *
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ ^ 2 := by
  obtain ⟨g, hg⟩ := Variation.exists_direction_of_bounded_mean_zero f hf hmean
  simpa only [hg] using full_benchmark_curvature W hW hmax hB g

/-- Nonconstant original degree identifies this same model's stationary
multiplier with the derivative at the supplied smooth benchmark contact. -/
theorem full_stationary_multiplier_eq_benchmark_deriv (W : Model Ω μ) (hW : FullFeasible W)
    (hmax : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    {β : ℝ} (hB : HasDerivAt benchmark β (density W)) (m ν : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, (∫ y, adjacencyKernel W x y ∂μ) = c) :
    m = β := by
  have hm := firstVariation_identity_of_shifted_zero W m
    (shiftedFirstVariation_zero_of_stationary W m ν hrow)
  have hβ := full_benchmark_first_variation W hW hmax hB
  have hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0 := by
    intro hz
    apply hnonconstant
    exact (Variation.kernel_weightFirstVariation_eq_zero_iff (adjacencyKernel W)
      (by norm_num) (adjacencyKernel_measurable W) (adjacencyKernel_bound W)).mp hz
  have hex : ∃ f : Variation.WeightDirections μ,
      Variation.weightFirstVariation (adjacencyOperator W) f ≠ 0 := by
    by_contra h
    push Not at h
    exact hregular (LinearMap.ext h)
  obtain ⟨f, hf⟩ := hex
  have h := LinearMap.congr_fun (hm.symm.trans hβ) f
  simp only [LinearMap.smul_apply, smul_eq_mul] at h
  exact (mul_eq_mul_right_iff.mp h).resolve_right hf

/-- The unhalved curvature bound belongs to this original model's actual
stationary shifted operator and holds in every bounded mean-zero direction. -/
theorem full_stationary_benchmark_curvature (W : Model Ω μ) (hW : FullFeasible W)
    (hmax : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hB : ContDiffAt ℝ 2 benchmark (density W)) (m ν : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, (∫ y, adjacencyKernel W x y ∂μ) = c)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hmean : (∫ x, f x ∂μ) = 0) :
    ⟪shiftedOperator W m f, f⟫ ≤ deriv (deriv benchmark) (density W) *
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ ^ 2 := by
  have hm := full_stationary_multiplier_eq_benchmark_deriv W hW hmax
    (hB.differentiableAt (by norm_num)).hasDerivAt m ν hrow hnonconstant
  rw [shiftedOperator_eq, hm]
  exact full_benchmark_curvature_bounded W hW hmax hB f hf hmean

/-- Full optimality constructs the original model's own regular multiplier;
smooth global contact identifies it and supplies the all-direction curvature. -/
theorem exists_full_smooth_contact_multiplier [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hmax : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hB : ContDiffAt ℝ 2 benchmark (density W))
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, (∫ y, adjacencyKernel W x y ∂μ) = c) :
    ∃ m ν : ℝ, m = deriv benchmark (density W) ∧
      Variation.weightFirstVariation (chargeOperator W) =
        m • Variation.weightFirstVariation (adjacencyOperator W) ∧
      (chargeOperator W - m • adjacencyOperator W) (Lp.const 2 μ (1 : ℝ)) =
        ν • Lp.const 2 μ (1 : ℝ) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace
        (chargeOperator W - m • adjacencyOperator W)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace
        (chargeOperator W - m • adjacencyOperator W)) ≤ 2 ∧
      ∀ f : Lp ℝ 2 μ, f ∈ KernelOperator.boundedL2Submodule μ → (∫ x, f x ∂μ) = 0 →
        ⟪(chargeOperator W - m • adjacencyOperator W) f, f⟫ ≤
          deriv (deriv benchmark) (density W) *
            ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ ^ 2 := by
  have hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0 := by
    intro hz
    apply hnonconstant
    exact (Variation.kernel_weightFirstVariation_eq_zero_iff (adjacencyKernel W)
      (by norm_num) (adjacencyKernel_measurable W) (adjacencyKernel_bound W)).mp hz
  obtain ⟨m, ν, hm, hrow, hfinite, hindex⟩ := exists_full_regular_multiplier W hW hopt hregular
  have hβ := full_benchmark_first_variation W hW hmax
    (hB.differentiableAt (by norm_num)).hasDerivAt
  have hex : ∃ f : Variation.WeightDirections μ,
      Variation.weightFirstVariation (adjacencyOperator W) f ≠ 0 := by
    by_contra h
    push Not at h
    exact hregular (LinearMap.ext h)
  obtain ⟨f, hf⟩ := hex
  have h := LinearMap.congr_fun (hm.symm.trans hβ) f
  simp only [LinearMap.smul_apply, smul_eq_mul] at h
  have heq : m = deriv benchmark (density W) :=
    (mul_eq_mul_right_iff.mp h).resolve_right hf
  refine ⟨m, ν, heq, hm, hrow, hfinite, hindex, ?_⟩
  intro f hf hmean
  rw [heq]
  exact full_benchmark_curvature_bounded W hW hmax hB f hf hmean

end Erdos1017.CappedModel
