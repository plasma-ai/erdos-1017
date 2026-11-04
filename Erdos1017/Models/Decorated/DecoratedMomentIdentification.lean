module

public import Erdos1017.Models.Decorated.DecoratedMomentTesting
public import Erdos1017.Models.Decorated.DecoratedCompactnessLaw

/-!
# Identifying moment limits with the limiting kernel

Conditional moments equal the joint-law continuous product integrals, so weak
convergence of joint laws identifies every cut-convergent continuous color
moment with the conditional moment of the limiting kernel, almost everywhere and
without changing the frame.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Erdos1017.DecoratedKernel

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
  [MetricSpace Ω] [MetricSpace C] [CompactSpace Ω] [CompactSpace C]
  [BorelSpace Ω] [BorelSpace C] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A continuous test of the actual joint latent-pair and color law. -/
def jointMomentTest (g h : Ω →ᵇ ℝ) (f : C(C, ℝ)) : ((Ω × Ω) × C) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => g z.1.1 * h z.1.2 * f z.2,
      ((g.continuous.comp (continuous_fst.comp continuous_fst)).mul
        (h.continuous.comp (continuous_snd.comp continuous_fst))).mul
          (f.continuous.comp continuous_snd)⟩

/-- Conditional moments give exactly the joint-law continuous product integrals. -/
theorem weightedIntegral_eq_jointMomentTest (W : DecoratedKernel Ω C μ)
    (f : C(C, ℝ)) (hbound : ∀ c, f c ∈ Set.Icc 0 1) (g h : Ω →ᵇ ℝ) :
    weightedIntegral (W.momentGraphon f f.continuous.stronglyMeasurable hbound) g h =
      ∫ z, jointMomentTest g h f z ∂(W.jointLaw : Measure _) := by
  rw [W.integral_jointLaw ((jointMomentTest g h f).integrable _)]
  simp only [jointMomentTest, BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk, integral_const_mul]
  unfold weightedIntegral
  apply integral_congr_ae
  filter_upwards [AEEqFun.coeFn_mk (W.moment f)
    (W.stronglyMeasurable_moment f.continuous.stronglyMeasurable).aestronglyMeasurable]
    with p hp
  simpa only [momentGraphon, moment] using congrArg (fun r : ℝ => g p.1 * h p.2 * r) hp

/-- Weak convergence of actual joint laws identifies every cut-convergent
continuous color moment with the conditional moment of the limiting kernel. -/
theorem momentGraphon_eq_of_jointLaw_tendsto
    (W : ℕ → DecoratedKernel Ω C μ) (V : DecoratedKernel Ω C μ)
    (f : C(C, ℝ)) (hbound : ∀ c, f c ∈ Set.Icc 0 1) (L : Graphon Ω μ)
    (hweak : Tendsto (fun n => (W n).jointLaw) atTop (𝓝 V.jointLaw))
    (hcut : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      Graphon.cutNormDiff ((W n).momentGraphon f f.continuous.stronglyMeasurable hbound) L < ε) :
    L = V.momentGraphon f f.continuous.stronglyMeasurable hbound := by
  apply graphon_eq_of_weightedIntegral_eq
  intro g h
  have hscalar := weightedIntegral_tendsto
    (fun n => (W n).momentGraphon f f.continuous.stronglyMeasurable hbound) L hcut g h
  have hjoint := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak)
    (jointMomentTest g h f)
  simp_rw [← weightedIntegral_eq_jointMomentTest _ f hbound g h] at hjoint
  exact tendsto_nhds_unique hscalar hjoint

/-- The identified scalar limit is the actual conditional moment almost everywhere. -/
theorem moment_ae_eq_of_jointLaw_tendsto
    (W : ℕ → DecoratedKernel Ω C μ) (V : DecoratedKernel Ω C μ)
    (f : C(C, ℝ)) (hbound : ∀ c, f c ∈ Set.Icc 0 1) (L : Graphon Ω μ)
    (hweak : Tendsto (fun n => (W n).jointLaw) atTop (𝓝 V.jointLaw))
    (hcut : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      Graphon.cutNormDiff ((W n).momentGraphon f f.continuous.stronglyMeasurable hbound) L < ε) :
    ∀ᵐ p ∂μ.prod μ, L.toAEEqFun p = V.moment f p := by
  rw [momentGraphon_eq_of_jointLaw_tendsto W V f hbound L hweak hcut]
  exact AEEqFun.coeFn_mk (V.moment f)
    (V.stronglyMeasurable_moment f.continuous.stronglyMeasurable).aestronglyMeasurable

/-- Cut convergence to the actual moment graphon follows from joint-law
convergence and the existing scalar cut limit, without changing any frame. -/
theorem momentGraphon_converges_of_jointLaw_tendsto
    (W : ℕ → DecoratedKernel Ω C μ) (V : DecoratedKernel Ω C μ)
    (f : C(C, ℝ)) (hbound : ∀ c, f c ∈ Set.Icc 0 1) (L : Graphon Ω μ)
    (hweak : Tendsto (fun n => (W n).jointLaw) atTop (𝓝 V.jointLaw))
    (hcut : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      Graphon.cutNormDiff ((W n).momentGraphon f f.continuous.stronglyMeasurable hbound) L < ε) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N,
      Graphon.cutNormDiff ((W n).momentGraphon f f.continuous.stronglyMeasurable hbound)
        (V.momentGraphon f f.continuous.stronglyMeasurable hbound) < ε := by
  rw [← momentGraphon_eq_of_jointLaw_tendsto W V f hbound L hweak hcut]
  exact hcut

end Erdos1017.DecoratedKernel
