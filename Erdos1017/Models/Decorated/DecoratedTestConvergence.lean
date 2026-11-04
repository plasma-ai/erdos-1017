module

public import Erdos1017.Models.Capped.CappedModel
public import Erdos1017.Models.Decorated.DecoratedTensorApproximation
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Continuous tests of the finite color sample

Conditional independence turns a tensor color test into the product of its
one-pair moments; the expected tensor and continuous tests under the two-stage
clique sampling law (`tensorTestIntegral`, `continuousTestIntegral`) are
defined, and convergence of all tensor sample moments implies convergence of
every continuous test.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos1017.DecoratedKernel

variable {Ω C ι : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
  {μ : Measure Ω} [Fintype ι]

/-- Conditional independence turns a tensor color test into the product of
its one-pair moments. Each index denotes one sampled pair. -/
theorem sampleLaw_integral_tensor (W : DecoratedKernel Ω C μ)
    (pairs : ι → Ω × Ω) (f : ι → C → ℝ) :
    (∫ c, ∏ i, f i (c i) ∂W.sampleLaw pairs) =
      ∏ i, W.moment (f i) (pairs i) := by
  simpa only [sampleLaw, moment] using
    (integral_fintype_prod_eq_prod (μ := fun i => W.kernel (pairs i)) f)

end Erdos1017.DecoratedKernel

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The expected tensor test under the actual two-stage clique sampling law. -/
def tensorTestIntegral (W : Model Ω μ) (n : ℕ)
    (f : CliquePair n → CappedColor → ℝ) : ℝ :=
  ∫ x : Fin n → Ω, ∫ c, ∏ e, f e (c e) ∂cliqueLaw W x
    ∂Measure.pi (fun _ : Fin n => μ)

/-- Integrating independent pair colors leaves one moment per clique pair. -/
theorem tensorTestIntegral_eq_momentIntegral (W : Model Ω μ) (n : ℕ)
    (f : CliquePair n → CappedColor → ℝ) :
    tensorTestIntegral W n f =
      ∫ x : Fin n → Ω,
        ∏ e, W.moment (f e) (x e.val.1, x e.val.2)
          ∂Measure.pi (fun _ : Fin n => μ) := by
  unfold tensorTestIntegral cliqueLaw
  congr 1
  funext x
  exact W.sampleLaw_integral_tensor _ f

end Erdos1017.CappedModel

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Real expectation of a continuous test under the existing two-stage law. -/
def continuousTestIntegral (W : Model Ω μ) (n : ℕ)
    (F : C(CliquePair n → CappedColor, ℝ)) : ℝ :=
  ∫ x : Fin n → Ω, ∫ c, F c ∂cliqueLaw W x
    ∂Measure.pi (fun _ : Fin n => μ)

theorem integrable_continuousTest (W : Model Ω μ) (n : ℕ)
    (F : C(CliquePair n → CappedColor, ℝ)) (x : Fin n → Ω) :
    Integrable (fun c => F c) (cliqueLaw W x) :=
  Integrable.of_bound F.continuous.aestronglyMeasurable ‖F‖
    (Filter.Eventually.of_forall fun c => F.norm_coe_le_norm c)

end Erdos1017.CappedModel

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- For a nonnegative continuous test, the existing `lintegral` is the
`ofReal` of its real-valued expected value. -/
theorem ofReal_continuousTestIntegral (W : Model Ω μ) (n : ℕ)
    (F : C(CliquePair n → CappedColor, ℝ)) (hF : ∀ c, 0 ≤ F c) :
    ENNReal.ofReal (continuousTestIntegral W n F) =
      ∫⁻ x : Fin n → Ω, ∫⁻ c, ENNReal.ofReal (F c) ∂cliqueLaw W x
        ∂Measure.pi (fun _ : Fin n => μ) := by
  have hsm : StronglyMeasurable (fun c : CliquePair n → CappedColor => F c) :=
    F.continuous.stronglyMeasurable
  have houtsm : StronglyMeasurable (fun x : Fin n → Ω =>
      ∫ c, F c ∂cliqueLaw W x) := by
    change StronglyMeasurable (fun x => ∫ c, F c ∂cliqueKernel W n x)
    exact hsm.integral_kernel
  have hbound : ∀ x : Fin n → Ω, ‖∫ c, F c ∂cliqueLaw W x‖ ≤ ‖F‖ := by
    intro x
    have h := norm_integral_le_of_norm_le_const
      (μ := cliqueLaw W x) (Filter.Eventually.of_forall fun c => F.norm_coe_le_norm c)
    simpa using h
  have houter : Integrable (fun x : Fin n → Ω => ∫ c, F c ∂cliqueLaw W x)
      (Measure.pi (fun _ : Fin n => μ)) :=
    Integrable.of_bound houtsm.aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall hbound)
  have houter_nonneg : 0 ≤ᵐ[Measure.pi (fun _ : Fin n => μ)]
      fun x : Fin n → Ω => ∫ c, F c ∂cliqueLaw W x :=
    Filter.Eventually.of_forall (fun x => integral_nonneg hF)
  rw [continuousTestIntegral]
  rw [ofReal_integral_eq_lintegral_ofReal houter houter_nonneg]
  apply lintegral_congr
  intro x
  exact ofReal_integral_eq_lintegral_ofReal (integrable_continuousTest W n F x)
    (Filter.Eventually.of_forall hF)

/-- The capped violation integral is the real expectation of its continuous test. -/
theorem testIntegral_eq_ofReal_continuousTestIntegral (W : Model Ω μ) (n : ℕ) :
    testIntegral W n = ENNReal.ofReal
      (continuousTestIntegral W n ⟨violation, continuous_violation n⟩) := by
  exact (ofReal_continuousTestIntegral W n
    ⟨violation, continuous_violation n⟩ (fun c => violation_nonneg c)).symm

/-- The unconditional finite color law after sampling latent clique vertices. -/
def sampledColorLaw (W : Model Ω μ) (n : ℕ) :
    ProbabilityMeasure (CliquePair n → CappedColor) :=
  ⟨cliqueKernel W n ∘ₘ Measure.pi (fun _ : Fin n => μ), inferInstance⟩

/-- Continuous-test expectation against the unconditional law equals the
original latent-then-color iterated integral. -/
theorem integral_sampledColorLaw (W : Model Ω μ) (n : ℕ)
    (F : C(CliquePair n → CappedColor, ℝ)) :
    (∫ c, F c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) =
      continuousTestIntegral W n F := by
  change (∫ c, F c ∂(cliqueKernel W n ∘ₘ Measure.pi (fun _ : Fin n => μ))) = _
  rw [Measure.comp_eq_comp_const_apply]
  have hF : Integrable (fun c => F c)
      ((cliqueKernel W n ∘ₖ Kernel.const Unit (Measure.pi (fun _ : Fin n => μ))) ()) := by
    exact Integrable.of_bound F.continuous.aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall fun c => F.norm_coe_le_norm c)
  simpa [continuousTestIntegral, cliqueKernel, cliqueLaw, DecoratedKernel.sampleKernel]
    using Kernel.integral_comp hF

private theorem expectation_pureTensor_eq_tensorTestIntegral (W : Model Ω μ) (n : ℕ)
    (f : CliquePair n → C(CappedColor, ℝ)) :
    DecoratedTensor.expectationLinear (sampledColorLaw W n) (DecoratedTensor.pureTensor f) =
      tensorTestIntegral W n (fun e => f e) := by
  change (∫ c, DecoratedTensor.pureTensor f c
    ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) = _
  rw [integral_sampledColorLaw]
  rfl

/-- Convergence of all actual tensor sample moments implies convergence of
every continuous test of the finite color sample. -/
theorem continuousTestIntegral_tendsto_of_tensorTestIntegral
    (W : ℕ → Model Ω μ) (V : Model Ω μ) (n : ℕ)
    (h : ∀ f : CliquePair n → C(CappedColor, ℝ), Filter.Tendsto
      (fun k => tensorTestIntegral (W k) n (fun e => f e)) Filter.atTop
      (nhds (tensorTestIntegral V n (fun e => f e))))
    (F : C(CliquePair n → CappedColor, ℝ)) :
    Filter.Tendsto (fun k => continuousTestIntegral (W k) n F) Filter.atTop
      (nhds (continuousTestIntegral V n F)) := by
  have h' := DecoratedTensor.tendsto_integral_of_tendsto_tensor
    (fun k => sampledColorLaw (W k) n) (sampledColorLaw V n)
    (fun f => by simpa only [expectation_pureTensor_eq_tensorTestIntegral] using h f) F
  change Filter.Tendsto (fun k => ∫ c, F c
    ∂(sampledColorLaw (W k) n : Measure (CliquePair n → CappedColor))) Filter.atTop
    (nhds (∫ c, F c ∂(sampledColorLaw V n : Measure (CliquePair n → CappedColor)))) at h'
  simpa only [integral_sampledColorLaw] using h'

/-- Convergence of all `[0,1]`-valued tensor sample moments implies
convergence of every continuous test of the finite color sample. -/
theorem continuousTestIntegral_tendsto_of_normalizedTensor
    (W : ℕ → Model Ω μ) (V : Model Ω μ) (n : ℕ)
    (h : ∀ f : CliquePair n → C(CappedColor, ℝ),
      (∀ e c, f e c ∈ Set.Icc 0 1) → Filter.Tendsto
      (fun k => tensorTestIntegral (W k) n (fun e => f e)) Filter.atTop
      (nhds (tensorTestIntegral V n (fun e => f e))))
    (F : C(CliquePair n → CappedColor, ℝ)) :
    Filter.Tendsto (fun k => continuousTestIntegral (W k) n F) Filter.atTop
      (nhds (continuousTestIntegral V n F)) := by
  have h' := DecoratedTensor.tendsto_integral_of_tendsto_normalizedTensor
    (fun k => sampledColorLaw (W k) n) (sampledColorLaw V n)
    (fun f hf => by simpa only [expectation_pureTensor_eq_tensorTestIntegral] using h f hf) F
  change Filter.Tendsto (fun k => ∫ c, F c
    ∂(sampledColorLaw (W k) n : Measure (CliquePair n → CappedColor))) Filter.atTop
    (nhds (∫ c, F c ∂(sampledColorLaw V n : Measure (CliquePair n → CappedColor)))) at h'
  simpa only [integral_sampledColorLaw] using h'

end Erdos1017.CappedModel
