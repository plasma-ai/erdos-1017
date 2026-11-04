module

public import Erdos1017.SelectedModel.Selection.FullNullDirectionRigidity

/-!
# Kernel rows under vertex reweighting

Strictly positive small bounded weights give equivalent vertex measures, and the
reweighted adjacency and shifted rows are represented in the original `L2`
space, so stationarity under the changed law gives exact operator equations in
the original space.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Strictly positive small bounded weights give a reweighted measure that dominates `μ`. -/
theorem reweightMeasure_absolutelyContinuous (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) :
    μ ≪ weightedMeasure (μ := μ) (Variation.vertexWeight f) := by
  apply withDensity_absolutelyContinuous' (Lp.aestronglyMeasurable _).aemeasurable.ennreal_ofReal
  filter_upwards [Variation.vertexWeight_positive f hf] with x hx
  exact (ENNReal.ofReal_pos.mpr hx).ne'

omit [IsProbabilityMeasure μ] in
/-- A single reweighted row is exactly the original weighted kernel action. -/
theorem integral_weightedMeasure_eq_applyKernel (w : Ω → ℝ) (hw : AEMeasurable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (K : Ω → Ω → ℝ) (x : Ω) :
    (∫ y, K x y ∂weightedMeasure (μ := μ) w) = KernelOperator.applyKernel (μ := μ) K w x := by
  rw [weightedMeasure, integral_withDensity_eq_integral_toReal_smul₀ hw.ennreal_ofReal]
  · apply integral_congr_ae
    filter_upwards [hw0] with y hy
    simp only [ENNReal.toReal_ofReal hy, smul_eq_mul]
    ring
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

/-- The reweighted adjacency row is represented in the original L2 space. -/
theorem adjacency_row_reweight_eq_operator (W : Model Ω μ)
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) :
    ∀ᵐ x ∂μ, (∫ y, adjacencyKernel (reweight W f hf) x y
      ∂weightedMeasure (μ := μ) (Variation.vertexWeight f)) =
        adjacencyOperator W (Variation.vertexWeight f) x := by
  filter_upwards [KernelOperator.onL2_coe (adjacencyKernel W) (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (Variation.vertexWeight f)] with x hx
  change _ = KernelOperator.onL2 (adjacencyKernel W) (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (Variation.vertexWeight f) x
  rw [hx]
  exact integral_weightedMeasure_eq_applyKernel (Variation.vertexWeight f)
    (Lp.aestronglyMeasurable _).aemeasurable (Variation.vertexWeight_nonnegative f hf)
    (adjacencyKernel W) x

/-- The same row identity holds for any newly selected shifted multiplier. -/
theorem shifted_row_reweight_eq_operator (W : Model Ω μ)
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) (m : ℝ) :
    ∀ᵐ x ∂μ, (∫ y, shiftedKernel (reweight W f hf) m x y
      ∂weightedMeasure (μ := μ) (Variation.vertexWeight f)) =
        shiftedOperator W m (Variation.vertexWeight f) x := by
  filter_upwards [KernelOperator.onL2_coe (shiftedKernel W m) (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) (Variation.vertexWeight f)] with x hx
  change _ = KernelOperator.onL2 (shiftedKernel W m) (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) (Variation.vertexWeight f) x
  rw [hx]
  exact integral_weightedMeasure_eq_applyKernel (Variation.vertexWeight f)
    (Lp.aestronglyMeasurable _).aemeasurable (Variation.vertexWeight_nonnegative f hf)
    (shiftedKernel W m) x

/-- An actual constant row under the changed law gives the exact original-L2
adjacency equation; equivalence of the measures is derived from the weight. -/
theorem adjacency_reweight_stationary_oldL2 (W : Model Ω μ)
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) (a : ℝ)
    (hrow : ∀ᵐ x ∂weightedMeasure (μ := μ) (Variation.vertexWeight f),
      (∫ y, adjacencyKernel (reweight W f hf) x y
        ∂weightedMeasure (μ := μ) (Variation.vertexWeight f)) = a) :
    adjacencyOperator W (Variation.vertexWeight f) = a • Lp.const 2 μ (1 : ℝ) := by
  apply Lp.ext
  filter_upwards [adjacency_row_reweight_eq_operator W f hf,
    (reweightMeasure_absolutelyContinuous f hf).ae_le hrow,
    Lp.coeFn_smul a (Lp.const 2 μ (1 : ℝ)), Lp.coeFn_const 2 μ (1 : ℝ)] with x hx hr hs hc
  simpa only [hs, Pi.smul_apply, smul_eq_mul, hc, Function.const_apply, mul_one] using
    hx.symm.trans hr

/-- A newly selected actual stationary shifted row under the changed law
gives an exact operator equation in the original L2 space. -/
theorem shifted_reweight_stationary_oldL2 (W : Model Ω μ)
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) (m a : ℝ)
    (hrow : ∀ᵐ x ∂weightedMeasure (μ := μ) (Variation.vertexWeight f),
      (∫ y, shiftedKernel (reweight W f hf) m x y
        ∂weightedMeasure (μ := μ) (Variation.vertexWeight f)) = a) :
    shiftedOperator W m (Variation.vertexWeight f) = a • Lp.const 2 μ (1 : ℝ) := by
  apply Lp.ext
  filter_upwards [shifted_row_reweight_eq_operator W f hf m,
    (reweightMeasure_absolutelyContinuous f hf).ae_le hrow,
    Lp.coeFn_smul a (Lp.const 2 μ (1 : ℝ)), Lp.coeFn_const 2 μ (1 : ℝ)] with x hx hr hs hc
  simpa only [hs, Pi.smul_apply, smul_eq_mul, hc, Function.const_apply, mul_one] using
    hx.symm.trans hr

end Erdos1017.CappedModel
