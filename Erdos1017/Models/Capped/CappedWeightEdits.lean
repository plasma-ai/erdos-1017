module

public import Erdos1017.Models.Capped.CappedModel
public import Erdos1017.Models.Kernel.KernelWeightVariation
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Vertex reweighting of capped models

Multiplying vertex mass by a nonnegative weight gives a latent probability law
(`weightedMeasure`), a bounded mean-zero direction of norm below one determines
such a law (`reweight`), and capped maximality supplies the local quadratic
comparison needed by the vertex-weight variation theorems.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual latent law obtained by multiplying vertex mass by a real
nonnegative weight. -/
def weightedMeasure (w : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun x => ENNReal.ofReal (w x))

omit [IsProbabilityMeasure μ] in
theorem weightedMeasure_probability {w : Ω → ℝ} (hw : Integrable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (hmean : ∫ x, w x ∂μ = 1) :
    IsProbabilityMeasure (weightedMeasure (μ := μ) w) := by
  constructor
  rw [weightedMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hw hw0, hmean]
  norm_num

/-- Pair integrals under vertex reweighting are exactly the quadratic
weighted pair integrals used by the analytic variation theorem. -/
theorem integral_weightedMeasure_prod (w : Ω → ℝ) (hw : AEMeasurable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (K : Ω → Ω → ℝ) :
    (∫ p : Ω × Ω, K p.1 p.2 ∂(weightedMeasure (μ := μ) w).prod
      (weightedMeasure (μ := μ) w)) =
      ∫ p : Ω × Ω, K p.1 p.2 * w p.2 * w p.1 ∂μ.prod μ := by
  rw [weightedMeasure, prod_withDensity₀ hw.ennreal_ofReal hw.ennreal_ofReal]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (f := fun p : Ω × Ω => ENNReal.ofReal (w p.1) * ENNReal.ofReal (w p.2))
    (hw.ennreal_ofReal.comp_fst.mul hw.ennreal_ofReal.comp_snd)]
  · apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hw0,
      Measure.quasiMeasurePreserving_snd.ae hw0] with p hp1 hp2
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp1,
      ENNReal.toReal_ofReal hp2, smul_eq_mul]
    ring
  · exact Filter.Eventually.of_forall (fun p => ENNReal.mul_lt_top
      ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- A bounded mean-zero direction of norm below one determines an actual
latent probability law, not just a formal L² perturbation. -/
def reweight (W : Model Ω μ) (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) :
    Model Ω (weightedMeasure (μ := μ) (Variation.vertexWeight f)) := by
  haveI := weightedMeasure_probability ((Lp.memLp (Variation.vertexWeight f)).integrable (by norm_num))
    (Variation.vertexWeight_nonnegative f hf) (Variation.vertexWeight_integral f)
  exact W.changeMeasure (withDensity_absolutelyContinuous _ _)

theorem feasible_reweight (W : Model Ω μ) {r : ℕ} (hW : Feasible r W)
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) : Feasible r (reweight W f hf) := by
  have := weightedMeasure_probability ((Lp.memLp (Variation.vertexWeight f)).integrable (by norm_num))
    (Variation.vertexWeight_nonnegative f hf) (Variation.vertexWeight_integral f)
  exact feasible_changeMeasure W (withDensity_absolutelyContinuous _ _) hW

theorem density_reweight (W : Model Ω μ) (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) :
    density (reweight W f hf) = Variation.weightedPairIntegral
      (fun x y => W.moment CappedColor.adjacency (x, y)) (Variation.vertexWeight f) / 2 := by
  unfold density Variation.weightedPairIntegral
  simpa only [reweight, DecoratedKernel.changeMeasure, DecoratedKernel.moment] using
    congrArg (fun a : ℝ => a / 2)
      (integral_weightedMeasure_prod _ (Lp.aestronglyMeasurable _).aemeasurable
        (Variation.vertexWeight_nonnegative f hf)
        (fun x y => W.moment CappedColor.adjacency (x, y)))

theorem objective_reweight (W : Model Ω μ) (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) :
    objective (reweight W f hf) = Variation.weightedPairIntegral
      (fun x y => W.moment CappedColor.charge (x, y)) (Variation.vertexWeight f) / 2 := by
  unfold objective Variation.weightedPairIntegral
  simpa only [reweight, DecoratedKernel.changeMeasure, DecoratedKernel.moment] using
    congrArg (fun a : ℝ => a / 2)
      (integral_weightedMeasure_prod _ (Lp.aestronglyMeasurable _).aemeasurable
        (Variation.vertexWeight_nonnegative f hf)
        (fun x y => W.moment CappedColor.charge (x, y)))

theorem weightedPairIntegral_one (K : Ω → Ω → ℝ) :
    Variation.weightedPairIntegral K (Lp.const 2 μ (1 : ℝ)) =
      ∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ := by
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_const 2 μ (1 : ℝ)),
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_const 2 μ (1 : ℝ))] with p hp1 hp2
  simp

/-- Actual capped maximality supplies the precise local quadratic comparison
required by the regular and singular vertex-weight variation theorems. -/
theorem weight_local_max (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1)
    (hd : Variation.weightedPairIntegral (fun x y => W.moment CappedColor.adjacency (x, y))
        (Variation.vertexWeight f) =
      Variation.weightedPairIntegral (fun x y => W.moment CappedColor.adjacency (x, y))
        (Lp.const 2 μ (1 : ℝ))) :
    Variation.weightedPairIntegral (fun x y => W.moment CappedColor.charge (x, y))
        (Variation.vertexWeight f) ≤
      Variation.weightedPairIntegral (fun x y => W.moment CappedColor.charge (x, y))
        (Lp.const 2 μ (1 : ℝ)) := by
  have := weightedMeasure_probability ((Lp.memLp (Variation.vertexWeight f)).integrable (by norm_num))
    (Variation.vertexWeight_nonnegative f hf) (Variation.vertexWeight_integral f)
  have hd' := density_reweight W f hf
  rw [hd, weightedPairIntegral_one] at hd'
  have ho := hW.2 (weightedMeasure (μ := μ) (Variation.vertexWeight f))
    (withDensity_absolutelyContinuous _ _) (reweight W f hf)
    (feasible_reweight W hW.1 f hf) hd'
  rw [objective_reweight W f hf] at ho
  rw [weightedPairIntegral_one]
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mp ho

end Erdos1017.CappedModel
