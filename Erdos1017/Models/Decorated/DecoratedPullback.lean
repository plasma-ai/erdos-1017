module

public import Erdos1017.Models.Decorated.DecoratedKernel
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Pullback of decorated kernels

Pulling a decorated kernel back along a measure-preserving map of latent spaces
(`pullback`) keeps conditional color laws exactly, commutes with every finite
independent sample law, and leaves all integrable scalar moment averages
unchanged.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.DecoratedKernel

variable {Ω Λ C : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace C]
  {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ]

/-- Pull a decorated kernel back along an actual measure-preserving map of
latent probability spaces. Conditional color laws are retained exactly. -/
def pullback (W : DecoratedKernel Λ C ν) (h : Ω → Λ) (hh : MeasurePreserving h μ ν) :
    DecoratedKernel Ω C μ where
  kernel := W.kernel.comap (Prod.map h h) (hh.measurable.prodMap hh.measurable)
  markov := by infer_instance
  symm := by
    have hsym := (hh.prod hh).quasiMeasurePreserving.ae W.symm
    filter_upwards [hsym] with p hp
    exact hp

@[simp] theorem pullback_kernel (W : DecoratedKernel Λ C ν) (h : Ω → Λ)
    (hh : MeasurePreserving h μ ν) (p : Ω × Ω) :
    (W.pullback h hh).kernel p = W.kernel (h p.1, h p.2) := rfl

@[simp] theorem moment_pullback (W : DecoratedKernel Λ C ν) (h : Ω → Λ)
    (hh : MeasurePreserving h μ ν) (f : C → ℝ) (p : Ω × Ω) :
    (W.pullback h hh).moment f p = W.moment f (h p.1, h p.2) := rfl

/-- Every finite independent conditional color law commutes exactly with
the common latent pullback. -/
theorem sampleLaw_pullback {ι : Type*} [Fintype ι] (W : DecoratedKernel Λ C ν)
    (h : Ω → Λ) (hh : MeasurePreserving h μ ν) (pairs : ι → Ω × Ω) :
    (W.pullback h hh).sampleLaw pairs =
      W.sampleLaw (fun i => (h (pairs i).1, h (pairs i).2)) := rfl

/-- All integrable scalar color-moment averages are unchanged by latent
pullback. The proof uses the actual product pushforward identity. -/
theorem integral_moment_pullback (W : DecoratedKernel Λ C ν) (h : Ω → Λ)
    (hh : MeasurePreserving h μ ν) (f : C → ℝ) (hf : StronglyMeasurable f) :
    (∫ p, (W.pullback h hh).moment f p ∂μ.prod μ) =
      ∫ p, W.moment f p ∂ν.prod ν := by
  have he := integral_map_of_stronglyMeasurable (μ := μ.prod μ) (hh.prod hh).measurable
    (W.stronglyMeasurable_moment hf)
  rw [(hh.prod hh).map_eq] at he
  exact he.symm

end Erdos1017.DecoratedKernel
