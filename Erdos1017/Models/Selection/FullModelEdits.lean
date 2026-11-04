module

public import Erdos1017.Models.Selection.FullModelVariation
public import Erdos1017.Models.Capped.CappedPositiveDirection
public import Erdos1017.Models.Capped.CappedUniversalValues
public import Erdos1017.Models.Selection.QuadraticUniversalCorrection

/-!
# Full feasibility under edits and averaging

Full feasibility is preserved by edit envelopes, edit mixtures, affine edits,
averaging and `adjoinUniversal`, and full-model extremality compares all fully
feasible competitors, including different latent probability laws, through the
limit's three-Lipschitz estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem fullFeasible_of_pair_absolutelyContinuous (W V : Model Ω μ) (hW : FullFeasible W)
    (hVW : ∀ p, V.kernel p ≪ W.kernel p) : FullFeasible V :=
  fun r => feasible_of_pair_absolutelyContinuous W V (hW r) hVW

theorem fullFeasible_editEnvelope (W : Model Ω μ) (hW : FullFeasible W) :
    FullFeasible (editEnvelope W) := fun r => feasible_editEnvelope W (hW r)

theorem fullFeasible_editMixture [Fintype ι] (W : Model Ω μ) (V : ι → Model Ω μ)
    (w : ι → NNReal) (hw : ∑ i, w i ≤ 1)
    (hV : ∀ i p, (V i).kernel p ≪ (editEnvelope W).kernel p) (hW : FullFeasible W) :
    FullFeasible (editMixture W V w hw) := fun r => feasible_editMixture W V w hw hV (hW r)

theorem fullFeasible_squaredEditMixture [Fintype ι] (W : Model Ω μ) (V : ι → Model Ω μ)
    (a : ι → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (hmass : τ * ∑ i, (a i) ^ 2 ≤ 1)
    (hV : ∀ i p, (V i).kernel p ≪ (editEnvelope W).kernel p) (hW : FullFeasible W) :
    FullFeasible (squaredEditMixture W V a τ hτ hmass) :=
  fun r => feasible_squaredEditMixture W V a τ hτ hmass hV (hW r)

omit [IsProbabilityMeasure μ] in
theorem fullFeasible_affineEdit (W : Model Ω μ) (hW : FullFeasible W) (E : AffineEdit W)
    (t : unitInterval) : FullFeasible (E.model t) := fun r => E.feasible r (hW r) t

omit [IsProbabilityMeasure μ] in
theorem fullFeasible_averaged (W : Model Ω μ) (hW : FullFeasible W) :
    FullFeasible (averaged W) := fun r => feasible_averaged W (hW r)

theorem fullFeasible_adjoinUniversal (W : Model Ω μ) (hW : FullFeasible W) (t : unitInterval) :
    FullFeasible (adjoinUniversal W t) := fun r => feasible_adjoinUniversal W (hW r) t

omit [IsProbabilityMeasure μ] in
/-- Genuine full-model extremality compares all fully feasible competitors,
including different latent probability laws, by the actual limit's
three-Lipschitz estimate. No finite-cutoff maximality is used. -/
theorem full_objective_le_max_add_three_density (W : Model Ω μ)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν) (hV : FullFeasible V) :
    objective V ≤ objective W + 3 * |density V - density W| := by
  have hbound := fullFeasible_objective_le_densityLimit V hV
  have hlip := FractionalGraph.densityLimit_le_add (density V) (density W)
  rw [← hopt] at hlip
  exact hbound.trans hlip

omit [IsProbabilityMeasure μ] in
theorem full_objective_le_of_density_eq (W : Model Ω μ)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν) (hV : FullFeasible V)
    (hd : density V = density W) : objective V ≤ objective W := by
  have h := full_objective_le_max_add_three_density W hopt ν V hV
  simpa only [hd, sub_self, abs_zero, mul_zero, add_zero] using h

/-- The old model's full optimum and an actually edited, then reweighted,
fully feasible competitor give the exact unhalved operator comparison. -/
theorem full_weighted_competitor_lipschitz (W : Model Ω μ)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (V : Model Ω μ) (hV : FullFeasible V) (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) :
    ⟪chargeOperator V (Variation.vertexWeight f), Variation.vertexWeight f⟫ -
        ⟪chargeOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ ≤
      3 * |⟪adjacencyOperator V (Variation.vertexWeight f), Variation.vertexWeight f⟫ -
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫| := by
  have := weightedMeasure_probability ((Lp.memLp (Variation.vertexWeight f)).integrable (by norm_num))
    (Variation.vertexWeight_nonnegative f hf) (Variation.vertexWeight_integral f)
  have he := full_objective_le_max_add_three_density W hopt
    (weightedMeasure (μ := μ) (Variation.vertexWeight f)) (reweight V f hf)
    (fullFeasible_reweight V hV f hf)
  have hd := density_reweight V f hf
  have hc := objective_reweight V f hf
  change density (reweight V f hf) =
    Variation.weightedPairIntegral (adjacencyKernel V) (Variation.vertexWeight f) / 2 at hd
  change objective (reweight V f hf) =
    Variation.weightedPairIntegral (chargeKernel V) (Variation.vertexWeight f) / 2 at hc
  rw [weighted_adjacency_eq] at hd
  rw [weighted_charge_eq] at hc
  rw [hd, hc] at he
  have hden : density W = ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ / 2 := by
    rw [adjacency_constant_inner]
    ring
  have hcost : objective W = ⟪chargeOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ / 2 := by
    rw [charge_constant_inner]
    ring
  rw [hden, hcost, ← sub_div, abs_div] at he
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at he
  linarith

end Erdos1017.CappedModel
