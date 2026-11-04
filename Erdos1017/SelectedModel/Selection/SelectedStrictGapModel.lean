module

public import Erdos1017.Models.Selection.FullStationarySelection
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure
public import Erdos1017.SelectedModel.Selection.FullSelectedNullRigidity

/-!
# The selected strict-gap model

A failure of the benchmark bound yields one selected model with its own
strict-gap structure and tangent-null rigidity, the strict gap supplying the
regularity and positive eigenvector that rigidity needs
(`exists_selected_strict_gap_model`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- A genuine strict benchmark gap supplies the original regularity and
positive eigenvector needed for the selected model's tangent-null rigidity. -/
theorem FullStationaryClass.selected_tangent_null_vector_rigidity_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hmean : (∫ x, f x ∂μ) = 0)
    (hdegree : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ = 0)
    (henergy : ⟪shiftedOperator W m f, f⟫ = 0) :
    ⟪adjacencyOperator W f, f⟫ = 0 ∧ shiftedOperator W m f = 0 := by
  have hstructure := hW.strict_gap_structure hd hgap
  obtain ⟨w, σ, hw, hmeanw, hσ, heigen⟩ := hstructure.positive_eigenvector
  exact hW.selected_tangent_null_vector_rigidity_of_positive_eigenvector
    ⟨by linarith [hd.1], hd.2⟩ hmin hstructure.regular
    w hw hmeanw σ hσ heigen f hf hmean hdegree henergy

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- A real failure of the benchmark bound yields one actual selected model
with its own strict-gap structure and tangent-null rigidity. Both scalar
selections and the global comparison remain attached to that same model. -/
theorem exists_selected_strict_gap_model
    (hfailure : ∃ d ∈ Set.Icc (0 : ℝ) (1 / 2),
      benchmark d < FractionalGraph.densityLimit d) :
    ∃ (d : ℝ) (W : Model Ω μ) (m : ℝ), d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧
      FullStationaryClass d (FractionalGraph.densityLimit d) W m ∧
      0 < objective W - benchmark (density W) ∧
      (∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
        FullFeasible V → objective V - benchmark (density V) ≤
          objective W - benchmark (density W)) ∧
      (∀ (V : Model Ω μ) (n : ℝ),
        FullStationaryClass d (FractionalGraph.densityLimit d) V n → m ≤ n) ∧
      (∀ V : Model Ω μ, FullStationaryClass d (FractionalGraph.densityLimit d) V m →
        stationaryEnergy V m ≤ stationaryEnergy W m) ∧
      FullStrictGapStructure W m (2 * (FractionalGraph.densityLimit d - m * d)) ∧
      ∀ f : Lp ℝ 2 μ, f ∈ KernelOperator.boundedL2Submodule μ →
        (∫ x, f x ∂μ) = 0 →
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ = 0 →
        ⟪shiftedOperator W m f, f⟫ = 0 →
        ⟪adjacencyOperator W f, f⟫ = 0 ∧ shiftedOperator W m f = 0 := by
  obtain ⟨d, W, m, hd, hW, hpositive, hglobal, hmin, hmax⟩ :=
    exists_selected_full_positive_global_excess (Ω := Ω) (μ := μ) hfailure
  have hgap : benchmark d < FractionalGraph.densityLimit d := by
    rw [hW.objective_eq, hW.density_eq] at hpositive
    linarith
  refine ⟨d, W, m, hd, hW, hpositive, hglobal, hmin, hmax,
    hW.strict_gap_structure hd hgap, ?_⟩
  exact hW.selected_tangent_null_vector_rigidity_of_strict_gap hd hgap hmin

end Erdos1017.CappedModel
