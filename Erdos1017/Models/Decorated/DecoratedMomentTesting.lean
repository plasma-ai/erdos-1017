module

public import Erdos1017.Models.Kernel.KernelCutOperator
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Testing graphons against continuous latent weights

A scalar graphon tested against a product of bounded continuous latent weights
(`weightedIntegral`) is controlled by the cut norm, so cut convergence implies
convergence of every continuous product test, and such tests identify a graphon
up to almost-everywhere equality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace Erdos1017.DecoratedKernel

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A scalar graphon tested against a product of continuous latent weights. -/
def weightedIntegral (U : Graphon Ω μ) (g h : Ω →ᵇ ℝ) : ℝ :=
  ∫ p : Ω × Ω, g p.1 * h p.2 * U.toAEEqFun p ∂μ.prod μ

/-- Bounded latent weights preserve graphon integrability. -/
theorem integrable_weighted (U : Graphon Ω μ) (g h : Ω →ᵇ ℝ) :
    Integrable (fun p : Ω × Ω => g p.1 * h p.2 * U.toAEEqFun p) (μ.prod μ) := by
  apply (SymmKernel.graphon_integrable U).bdd_mul (c := ‖g‖ * ‖h‖)
    ((g.continuous.comp continuous_fst).mul
      (h.continuous.comp continuous_snd)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    change ‖g p.1 * h p.2‖ ≤ ‖g‖ * ‖h‖
    rw [norm_mul]
    exact mul_le_mul (g.norm_coe_le_norm p.1) (h.norm_coe_le_norm p.2)
      (norm_nonneg _) (norm_nonneg _))

/-- Cut norm controls arbitrary bounded continuous signed latent weights. -/
theorem abs_weightedIntegral_sub_le (U V : Graphon Ω μ) (g h : Ω →ᵇ ℝ) :
    |weightedIntegral U g h - weightedIntegral V g h| ≤
      4 * (‖g‖ + 1) * (‖h‖ + 1) * Graphon.cutNormDiff U V := by
  let a := ‖g‖ + 1
  let b := ‖h‖ + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  let g' : Ω → ℝ := fun x => g x / a
  let h' : Ω → ℝ := fun x => h x / b
  have hg' : Measurable g' := g.continuous.measurable.div_const a
  have hh' : Measurable h' := h.continuous.measurable.div_const b
  have hgb (x) : |g' x| ≤ 1 := by
    dsimp [g']
    rw [abs_div, abs_of_pos ha, div_le_one ha]
    have hx : |g x| ≤ ‖g‖ := by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x
    exact hx.trans (by dsimp [a]; linarith)
  have hhb (x) : |h' x| ≤ 1 := by
    dsimp [h']
    rw [abs_div, abs_of_pos hb, div_le_one hb]
    have hx : |h x| ≤ ‖h‖ := by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm x
    exact hx.trans (by dsimp [b]; linarith)
  have hcut := KernelOperator.abs_signed_weighted_graphonDifference_le U V g' h' hg' hh' hgb hhb
  have heq : weightedIntegral U g h - weightedIntegral V g h =
      a * b * ∫ p : Ω × Ω, g' p.1 * h' p.2 *
        KernelOperator.graphonDifference U V p.1 p.2 ∂μ.prod μ := by
    rw [weightedIntegral, weightedIntegral, ← integral_sub (integrable_weighted U g h)
      (integrable_weighted V g h), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    dsimp [g', h', KernelOperator.graphonDifference]
    field_simp
  rw [heq, abs_mul, abs_of_pos (mul_pos ha hb)]
  have hmul := mul_le_mul_of_nonneg_left hcut (mul_nonneg ha.le hb.le)
  dsimp [a, b] at hmul ⊢
  nlinarith

/-- Cut convergence implies convergence of every continuous product test. -/
theorem weightedIntegral_tendsto (U : ℕ → Graphon Ω μ) (V : Graphon Ω μ)
    (hcut : ∀ ε > 0, ∃ N, ∀ n ≥ N, Graphon.cutNormDiff (U n) V < ε)
    (g h : Ω →ᵇ ℝ) :
    Tendsto (fun n => weightedIntegral (U n) g h) atTop (𝓝 (weightedIntegral V g h)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let K := 4 * (‖g‖ + 1) * (‖h‖ + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨N, hN⟩ := hcut (ε / K) (div_pos hε hK)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  calc
    _ ≤ K * Graphon.cutNormDiff (U n) V := abs_weightedIntegral_sub_le (U n) V g h
    _ < K * (ε / K) := mul_lt_mul_of_pos_left (hN n hn) hK
    _ = ε := mul_div_cancel₀ ε hK.ne'

/-- Continuous product tests identify a graphon up to its existing a.e. equality. -/
theorem graphon_eq_of_weightedIntegral_eq (U V : Graphon Ω μ)
    (htest : ∀ g h : Ω →ᵇ ℝ, weightedIntegral U g h = weightedIntegral V g h) : U = V := by
  let ρ (W : Graphon Ω μ) : Measure (Ω × Ω) :=
    (μ.prod μ).withDensity (fun p => ENNReal.ofReal (W.toAEEqFun p))
  have hρ (W : Graphon Ω μ) : ρ W ≤ μ.prod μ := by
    calc
      ρ W ≤ (μ.prod μ).withDensity 1 := withDensity_mono (by
        filter_upwards [W.ae_mem_Icc] with p hp
        exact (ENNReal.ofReal_le_ofReal hp.2).trans_eq (by simp))
      _ = μ.prod μ := withDensity_one
  have hfinite (W : Graphon Ω μ) : IsFiniteMeasure (ρ W) :=
    isFiniteMeasure_of_le (μ.prod μ) (hρ W)
  have htestρ (W : Graphon Ω μ) (g h : Ω →ᵇ ℝ) :
      (∫ p : Ω × Ω, g p.1 * h p.2 ∂ρ W) = weightedIntegral W g h := by
    dsimp only [ρ]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      W.toAEEqFun.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards [W.ae_mem_Icc] with p hp
    simp only [ENNReal.toReal_ofReal hp.1, smul_eq_mul]
    ring
  have hmeasure : ρ U = ρ V := by
    let := hfinite U
    let := hfinite V
    apply Measure.ext_of_integral_mul_boundedContinuousFunction
    intro g h
    rw [htestρ, htestρ]
    exact htest g h
  have hae := (withDensity_eq_iff_of_sigmaFinite
    U.toAEEqFun.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    V.toAEEqFun.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp hmeasure
  apply Graphon.ext
  apply SymmKernel.ext
  apply AEEqFun.ext
  filter_upwards [hae, U.ae_mem_Icc, V.ae_mem_Icc] with p hp hu hv
  have hp' := congrArg ENNReal.toReal hp
  simpa only [ENNReal.toReal_ofReal hu.1, ENNReal.toReal_ofReal hv.1] using hp'

end Erdos1017.DecoratedKernel
