module

public import Erdos1017.Models.Decorated.DecoratedPullback
public import Erdos1017.Models.Decorated.DecoratedTestConvergence
public import Graphon.Pullback

/-!
# Moments and tests under latent pullback

Forming a bounded scalar color moment commutes with latent pullback, and
expected continuous color tests are unchanged by a common measure-preserving
pullback.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.DecoratedKernel

variable {Ω Λ C : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace C]
  {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Forming a bounded scalar color moment commutes with latent pullback. -/
theorem momentGraphon_pullback (W : DecoratedKernel Λ C ν) (h : Ω → Λ)
    (hh : MeasurePreserving h μ ν) (f : C → ℝ) (hf : StronglyMeasurable f)
    (hbound : ∀ c, f c ∈ Set.Icc 0 1) :
    (W.pullback h hh).momentGraphon f hf hbound =
      Graphon.pullback (W.momentGraphon f hf hbound) h hh := by
  apply Graphon.ext
  apply SymmKernel.ext
  rw [Graphon.pullback_toAEEqFun]
  rfl

end Erdos1017.DecoratedKernel

namespace Erdos1017.CappedModel

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
  {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Expected continuous color tests are unchanged by a common
measure-preserving latent pullback. -/
theorem continuousTestIntegral_pullback (W : Model Λ ν) (h : Ω → Λ)
    (hh : MeasurePreserving h μ ν) (n : ℕ)
    (F : C(CliquePair n → CappedColor, ℝ)) :
    continuousTestIntegral (W.pullback h hh) n F = continuousTestIntegral W n F := by
  have hpi : MeasurePreserving (fun x : Fin n → Ω => h ∘ x)
      (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν)) :=
    measurePreserving_pi (fun _ : Fin n => μ) (fun _ : Fin n => ν) (fun _ => hh)
  have hsm : StronglyMeasurable (fun x : Fin n → Λ =>
      ∫ c, F c ∂cliqueLaw W x) := by
    change StronglyMeasurable (fun x => ∫ c, F c ∂cliqueKernel W n x)
    exact F.continuous.stronglyMeasurable.integral_kernel
  have he := integral_map_of_stronglyMeasurable (μ := Measure.pi (fun _ : Fin n => μ))
    hpi.measurable hsm
  rw [hpi.map_eq] at he
  unfold continuousTestIntegral
  simpa only [cliqueLaw, DecoratedKernel.sampleLaw_pullback, Function.comp_apply] using he.symm

end Erdos1017.CappedModel
