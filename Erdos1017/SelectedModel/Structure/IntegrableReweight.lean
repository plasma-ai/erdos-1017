module

public import Erdos1017.SelectedModel.Structure.IntegrableDegreeCone

/-!
# Reweighting by an integrable probability weight

The law change `integrableReweight` by an arbitrary integrable nonnegative
probability weight keeps the decorated color kernel, preserves every
finite-order clique test and the color moments, and has density and objective
given by weighted original-kernel integrals, so the full-feasible objective
comparison applies to it.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An arbitrary integrable nonnegative probability weight changes the
physical law while retaining the original decorated color kernel exactly. -/
def integrableReweight (W : Model Ω μ) (w : Ω → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (hw1 : (∫ x, w x ∂μ) = 1) :
    Model Ω (weightedMeasure (μ := μ) w) := by
  have := weightedMeasure_probability hw hw0 hw1
  exact W.changeMeasure (withDensity_absolutelyContinuous _ _)

/-- Every original finite-order clique test survives the actual absolutely
continuous integrable reweighting. No bound on the weight is required. -/
theorem fullFeasible_integrableReweight (W : Model Ω μ) (hW : FullFeasible W)
    (w : Ω → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hw1 : (∫ x, w x ∂μ) = 1) : FullFeasible (integrableReweight W w hw hw0 hw1) := by
  have := weightedMeasure_probability hw hw0 hw1
  intro r
  exact feasible_changeMeasure W (withDensity_absolutelyContinuous _ _) (hW r)

/-- The original color moments are unchanged pointwise by the law change. -/
theorem moment_integrableReweight (W : Model Ω μ) (w : Ω → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (hw1 : (∫ x, w x ∂μ) = 1)
    (f : CappedColor → ℝ) (p : Ω × Ω) :
    (integrableReweight W w hw hw0 hw1).moment f p = W.moment f p := rfl

/-- Density of the actual changed law equals its original-kernel weighted
energy divided by two, also for unbounded integrable weights. -/
theorem density_integrableReweight (W : Model Ω μ) (w : Ω → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (hw1 : (∫ x, w x ∂μ) = 1) :
    density (integrableReweight W w hw hw0 hw1) =
      KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W) w / 2 := by
  unfold density KernelOperator.kernelEnergy
  simpa only [integrableReweight, DecoratedKernel.changeMeasure, DecoratedKernel.moment,
    adjacencyKernel] using congrArg (fun a : ℝ => a / 2)
      (integral_weightedMeasure_prod w hw.aestronglyMeasurable.aemeasurable hw0 (adjacencyKernel W))

/-- Objective of the actual changed law uses the unchanged original charge
kernel and the actual weighted probability product. -/
theorem objective_integrableReweight (W : Model Ω μ) (w : Ω → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (hw1 : (∫ x, w x ∂μ) = 1) :
    objective (integrableReweight W w hw hw0 hw1) =
      KernelOperator.kernelEnergy (μ := μ) (chargeKernel W) w / 2 := by
  unfold objective KernelOperator.kernelEnergy
  simpa only [integrableReweight, DecoratedKernel.changeMeasure, DecoratedKernel.moment,
    chargeKernel] using congrArg (fun a : ℝ => a / 2)
      (integral_weightedMeasure_prod w hw.aestronglyMeasurable.aemeasurable hw0 (chargeKernel W))

/-- The actual full-feasible objective comparison applies to every such
changed probability law; no stationarity or optimality is assigned to it. -/
theorem objective_integrableReweight_le_densityLimit (W : Model Ω μ) (hW : FullFeasible W)
    (w : Ω → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hw1 : (∫ x, w x ∂μ) = 1) :
    objective (integrableReweight W w hw hw0 hw1) ≤
      FractionalGraph.densityLimit (density (integrableReweight W w hw hw0 hw1)) := by
  have := weightedMeasure_probability hw hw0 hw1
  exact fullFeasible_objective_le_densityLimit _ (fullFeasible_integrableReweight W hW w hw hw0 hw1)

end Erdos1017.CappedModel
