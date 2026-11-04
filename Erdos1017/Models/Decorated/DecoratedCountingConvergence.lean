module

public import Erdos1017.Models.Decorated.DecoratedCounting
public import Erdos1017.Models.Decorated.DecoratedTestConvergence

/-!
# Convergence of sampled tests under moment cut convergence

The colored graphon density is the expected tensor test under independent
conditional color sampling, so common-frame cut convergence of all normalized
color moments implies convergence of every tensor expectation and every
continuous test of the finite color sample.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The colored graphon density is the actual expected tensor test under
independent conditional color sampling. -/
theorem coloredDensity_momentGraphon_eq_tensorTestIntegral
    (W : Model Ω μ) (n : ℕ) (f : CliquePair n → C(CappedColor, ℝ))
    (hf : ∀ e c, f e c ∈ Set.Icc 0 1) :
    DecoratedCounting.coloredDensity n (fun e => W.momentGraphon (f e)
      (f e).continuous.stronglyMeasurable (hf e)) =
      tensorTestIntegral W n (fun e => f e) := by
  rw [DecoratedCounting.coloredDensity_eq_integral,
    tensorTestIntegral_eq_momentIntegral]
  apply integral_congr_ae
  have h : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ), ∀ e : CliquePair n,
      (W.momentGraphon (f e) (f e).continuous.stronglyMeasurable (hf e)).toAEEqFun
        (z e.val.1, z e.val.2) = W.moment (f e) (z e.val.1, z e.val.2) := by
    apply (ae_all_iff).mpr
    intro e
    have hpair := DecoratedCounting.measurePreserving_pairProjection (μ := μ)
      e.val.1 e.val.2 (ne_of_lt e.property)
    have h0 : ∀ᵐ p ∂μ.prod μ,
        (W.momentGraphon (f e) (f e).continuous.stronglyMeasurable (hf e)).toAEEqFun p =
          W.moment (f e) p := AEEqFun.coeFn_mk _ _
    exact hpair.quasiMeasurePreserving.ae h0
  filter_upwards [h] with z hz
  exact Finset.prod_congr rfl (fun e _ => hz e)

/-- Common-frame cut convergence of every normalized color moment implies
convergence of each actual sampled tensor expectation. -/
theorem tensorTestIntegral_tendsto_of_momentGraphonCut
    (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (hcut : ∀ (f : C(CappedColor, ℝ))
      (hf : ∀ c, f c ∈ Set.Icc 0 1) ε, 0 < ε → ∃ N, ∀ k ≥ N,
        Graphon.cutNormDiff
          ((W k).momentGraphon f f.continuous.stronglyMeasurable hf)
          (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε)
    (n : ℕ) (f : CliquePair n → C(CappedColor, ℝ))
    (hf : ∀ e c, f e c ∈ Set.Icc 0 1) :
    Filter.Tendsto (fun k => tensorTestIntegral (W k) n (fun e => f e))
      Filter.atTop (nhds (tensorTestIntegral V n (fun e => f e))) := by
  let U (k : ℕ) (e : CliquePair n) : Graphon Ω μ :=
    (W k).momentGraphon (f e) (f e).continuous.stronglyMeasurable (hf e)
  let A (e : CliquePair n) : Graphon Ω μ :=
    V.momentGraphon (f e) (f e).continuous.stronglyMeasurable (hf e)
  have hterm (e : CliquePair n) : Filter.Tendsto
      (fun k => Graphon.cutNormDiff (U k e) (A e)) Filter.atTop (nhds (0 : ℝ)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hcut (f e) (hf e) ε hε
    refine ⟨N, fun k hk => ?_⟩
    simpa [Real.dist_eq, abs_of_nonneg (Graphon.cutNormDiff_nonneg (U k e) (A e))]
      using hN k hk
  have hsum : Filter.Tendsto
      (fun k => ∑ e : CliquePair n, Graphon.cutNormDiff (U k e) (A e))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (CliquePair n))
      (fun e _ => hterm e)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsum ε hε
  refine ⟨N, fun k hk => ?_⟩
  have hnonneg : 0 ≤ ∑ e : CliquePair n, Graphon.cutNormDiff (U k e) (A e) := by
    exact Finset.sum_nonneg (fun e _ => Graphon.cutNormDiff_nonneg (U k e) (A e))
  rw [Real.dist_eq,
    ← coloredDensity_momentGraphon_eq_tensorTestIntegral (W k) n f hf,
    ← coloredDensity_momentGraphon_eq_tensorTestIntegral V n f hf]
  calc
    |DecoratedCounting.coloredDensity n (U k) - DecoratedCounting.coloredDensity n A| ≤
        ∑ e : CliquePair n, Graphon.cutNormDiff (U k e) (A e) :=
      DecoratedCounting.abs_coloredDensity_sub_le n (U k) A
    _ < ε := by
      simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hN k hk

/-- Common-frame cut convergence of all normalized color moments implies
convergence of every continuous test of the finite color sample. -/
theorem continuousTestIntegral_tendsto_of_momentGraphonCut
    (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (hcut : ∀ (f : C(CappedColor, ℝ))
      (hf : ∀ c, f c ∈ Set.Icc 0 1) ε, 0 < ε → ∃ N, ∀ k ≥ N,
        Graphon.cutNormDiff
          ((W k).momentGraphon f f.continuous.stronglyMeasurable hf)
          (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε)
    (n : ℕ) (F : C(CliquePair n → CappedColor, ℝ)) :
    Filter.Tendsto (fun k => continuousTestIntegral (W k) n F)
      Filter.atTop (nhds (continuousTestIntegral V n F)) := by
  apply continuousTestIntegral_tendsto_of_normalizedTensor W V n
  intro f hf
  exact tensorTestIntegral_tendsto_of_momentGraphonCut W V hcut n f hf

end Erdos1017.CappedModel
