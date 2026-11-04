module

public import Erdos1017.Models.Capped.CappedEditMixture
public import Erdos1017.Models.Capped.CappedEditMultiplier

/-!
# Operators of edit mixtures

Bilinear pair integrals and the adjacency and charge operators of an edit
mixture are computed, and the simultaneously edited and reweighted model is a
feasible competitor whose three-Lipschitz comparison comes from density
restoration.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι]

theorem bilinear_pairIntegral_mixture
    (K₀ : Ω → Ω → ℝ) (K : ι → Ω → Ω → ℝ) (Kt : Ω → Ω → ℝ) {B : ℝ}
    (hK₀ : AEStronglyMeasurable (fun p : Ω × Ω => K₀ p.1 p.2) (μ.prod μ))
    (hK : ∀ i, AEStronglyMeasurable (fun p : Ω × Ω => K i p.1 p.2) (μ.prod μ))
    (hB₀ : ∀ᵐ p ∂μ.prod μ, ‖K₀ p.1 p.2‖ ≤ B)
    (hB : ∀ i, ∀ᵐ p ∂μ.prod μ, ‖K i p.1 p.2‖ ≤ B)
    (c₀ : ℝ) (c : ι → ℝ) (hKt : ∀ x y, Kt x y = c₀ * K₀ x y + ∑ i, c i * K i x y)
    (f g : Lp ℝ 2 μ) :
    (∫ p : Ω × Ω, Kt p.1 p.2 * f p.2 * g p.1 ∂μ.prod μ) =
      c₀ * (∫ p : Ω × Ω, K₀ p.1 p.2 * f p.2 * g p.1 ∂μ.prod μ) +
        ∑ i, c i * (∫ p : Ω × Ω, K i p.1 p.2 * f p.2 * g p.1 ∂μ.prod μ) := by
  have h₀ := KernelOperator.integrable_bilinear hK₀ hB₀ f g
  have hi (i : ι) := KernelOperator.integrable_bilinear (hK i) (hB i) f g
  calc
    _ = ∫ p : Ω × Ω, c₀ * (K₀ p.1 p.2 * f p.2 * g p.1) +
        ∑ i, c i * (K i p.1 p.2 * f p.2 * g p.1) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hKt]
      simp only [add_mul, Finset.sum_mul, mul_assoc]
    _ = _ := by
      rw [integral_add (h₀.const_mul c₀) (integrable_finsetSum _ (fun i _ => (hi i).const_mul _)),
        integral_const_mul, integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
      simp only [integral_const_mul]

theorem adjacencyOperator_editMixture (W : Model Ω μ) (V : ι → Model Ω μ) (w : ι → NNReal)
    (hw : ∑ i, w i ≤ 1) :
    adjacencyOperator (editMixture W V w hw) =
      (1 - ∑ i, (w i : ℝ)) • adjacencyOperator W + ∑ i, (w i : ℝ) • adjacencyOperator (V i) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  simp only [adjacencyOperator, add_apply, sum_apply, smul_apply, inner_add_left,
    sum_inner, real_inner_smul_left, KernelOperator.operator_inner]
  apply bilinear_pairIntegral_mixture (adjacencyKernel W) (fun i => adjacencyKernel (V i))
    (adjacencyKernel (editMixture W V w hw)) (adjacencyKernel_measurable W)
    (fun i => adjacencyKernel_measurable (V i)) (adjacencyKernel_bound W)
    (fun i => adjacencyKernel_bound (V i))
  intro x y
  exact moment_editMixture W V w hw (x, y) _
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)

theorem chargeOperator_editMixture (W : Model Ω μ) (V : ι → Model Ω μ) (w : ι → NNReal)
    (hw : ∑ i, w i ≤ 1) :
    chargeOperator (editMixture W V w hw) =
      (1 - ∑ i, (w i : ℝ)) • chargeOperator W + ∑ i, (w i : ℝ) • chargeOperator (V i) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  simp only [chargeOperator, add_apply, sum_apply, smul_apply, inner_add_left,
    sum_inner, real_inner_smul_left, KernelOperator.operator_inner]
  apply bilinear_pairIntegral_mixture (chargeKernel W) (fun i => chargeKernel (V i))
    (chargeKernel (editMixture W V w hw)) (chargeKernel_measurable W)
    (fun i => chargeKernel_measurable (V i)) (chargeKernel_bound W)
    (fun i => chargeKernel_bound (V i))
  intro x y
  exact moment_editMixture W V w hw (x, y) _
    CappedColor.continuous_charge.measurable.stronglyMeasurable 3 (fun c => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
        (CappedColor.charge_mem c).2.trans (by norm_num)⟩)

/-- The simultaneous edited and reweighted model is an actual feasible
competitor, so density restoration supplies its three-Lipschitz comparison. -/
theorem weighted_competitor_lipschitz (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (V : Model Ω μ) (hV : Feasible r V) (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) :
    ⟪chargeOperator V (Variation.vertexWeight f), Variation.vertexWeight f⟫ -
        ⟪chargeOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ ≤
      3 * |⟪adjacencyOperator V (Variation.vertexWeight f), Variation.vertexWeight f⟫ -
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫| := by
  have := weightedMeasure_probability ((Lp.memLp (Variation.vertexWeight f)).integrable (by norm_num))
    (Variation.vertexWeight_nonnegative f hf) (Variation.vertexWeight_integral f)
  have he := objective_le_max_add_three_density W hW
    (weightedMeasure (μ := μ) (Variation.vertexWeight f)) (withDensity_absolutelyContinuous _ _)
    (reweight V f hf) (feasible_reweight V hV f hf)
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
