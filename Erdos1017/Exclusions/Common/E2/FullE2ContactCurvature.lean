module

public import Erdos1017.Exclusions.Common.E2.BenchmarkE2Curvature
public import Erdos1017.SelectedModel.Selection.FullSmoothContact
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure

/-!
# Second-order bound at `E₂` benchmark contact

At `E₂` benchmark contact, a full stationary class identifies the recorded
multiplier and bounds its unhalved shifted quadratic form in every bounded
mean-zero direction, with contact coefficient below six for `0 < q ≤ 1/5`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Actual E2 benchmark contact identifies the original model's recorded
multiplier and bounds its unhalved shifted quadratic form in every bounded
mean-zero direction. Benchmark smoothness and activity are derived. -/
theorem FullStationaryClass.e2_contact_curvature
    {d c m q : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Set.Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    m = -LowerE2Scalar.multiplier q ∧
      ∀ f : Lp ℝ 2 μ, f ∈ KernelOperator.boundedL2Submodule μ →
        (∫ x, f x ∂μ) = 0 →
        ⟪shiftedOperator W m f, f⟫ ≤ E2PrivateCurvature.curvature q *
          ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ ^ 2 := by
  have hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  have hstructure := hW.strict_gap_structure hd hgap
  have hWdq : density W = (1 - LowerE2Scalar.missingMass q) / 2 := hW.density_eq.trans hdq
  have hB : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) (density W) := by
    rw [hWdq]
    exact Benchmark.benchmark_hasDerivAt_e2_q hq
  have hC2 : ContDiffAt ℝ 2 benchmark (density W) := by
    rw [hWdq]
    exact Benchmark.benchmark_contDiffAt_e2_q hq
  have hm := full_stationary_multiplier_eq_benchmark_deriv W hW.full hglobal hB
    m _ hW.stationary hstructure.nonconstant_degree
  refine ⟨hm, ?_⟩
  intro f hf hmean
  have hcurvature := full_stationary_benchmark_curvature W hW.full hglobal hC2
    m _ hW.stationary hstructure.nonconstant_degree f hf hmean
  have hsecond := Benchmark.benchmark_second_deriv_e2_q hq
  change deriv (deriv benchmark) ((1 - LowerE2Scalar.missingMass q) / 2) =
    E2PrivateCurvature.curvature q at hsecond
  rwa [hWdq, hsecond] at hcurvature

/-- The exact actual E2 contact coefficient is below six throughout the
legal positive parameter interval. No physical flow hypothesis is used. -/
theorem FullStationaryClass.e2_contact_curvature_le_six
    {d c m q : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Set.Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hmean : (∫ x, f x ∂μ) = 0) :
    ⟪shiftedOperator W m f, f⟫ ≤
      6 * ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ ^ 2 := by
  have hcurvature := (hW.e2_contact_curvature hq hdq hgap hglobal).2 f hf hmean
  have hcap := (E2PrivateCurvature.curvature_pos_lt_six ⟨hq.1.le, hq.2⟩).2
  exact hcurvature.trans (mul_le_mul_of_nonneg_right hcap.le (sq_nonneg _))

end Erdos1017.CappedModel
