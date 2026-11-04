module

public import Graphon.Basic
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Decorated kernels

A decorated kernel (`DecoratedKernel`) gives independent pair colors conditional
on the latent vertices, symmetric almost everywhere, with a color law, changes
of latent measure and finite independent sample laws (`sampleLaw`) forming a
Markov kernel; absolute continuity of latent laws passes to every finite vertex
sample.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Erdos1017

/-- Independent pair colors conditional on the latent vertices. Symmetry is
required only almost everywhere for the latent product measure. -/
structure DecoratedKernel (Ω C : Type*) [MeasurableSpace Ω] [MeasurableSpace C]
    (μ : Measure Ω) where
  kernel : Kernel (Ω × Ω) C
  markov : IsMarkovKernel kernel
  symm : ∀ᵐ p ∂μ.prod μ, kernel p.swap = kernel p

namespace DecoratedKernel

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
  {μ ν : Measure Ω}

instance (W : DecoratedKernel Ω C μ) : IsMarkovKernel W.kernel := W.markov

/-- The probability law of the color at one latent pair. -/
def law (W : DecoratedKernel Ω C μ) (p : Ω × Ω) : ProbabilityMeasure C :=
  ⟨W.kernel p, inferInstance⟩

/-- The real scalar moment associated to a color test. -/
def moment (W : DecoratedKernel Ω C μ) (f : C → ℝ) (p : Ω × Ω) : ℝ :=
  ∫ c, f c ∂W.kernel p

theorem stronglyMeasurable_moment (W : DecoratedKernel Ω C μ)
    {f : C → ℝ} (hf : StronglyMeasurable f) : StronglyMeasurable (W.moment f) :=
  hf.integral_kernel

theorem moment_symm (W : DecoratedKernel Ω C μ) (f : C → ℝ) :
    ∀ᵐ p ∂μ.prod μ, W.moment f p.swap = W.moment f p := by
  filter_upwards [W.symm] with p hp
  simp only [moment, hp]

theorem moment_mem_Icc (W : DecoratedKernel Ω C μ) {f : C → ℝ}
    (hf : StronglyMeasurable f) (hbound : ∀ c, f c ∈ Icc 0 1) (p : Ω × Ω) :
    W.moment f p ∈ Icc 0 1 := by
  have hint : Integrable f (W.kernel p) :=
    Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound c).1]
      exact (hbound c).2)
  exact ⟨integral_nonneg (fun c => (hbound c).1),
    (integral_mono hint (integrable_const 1) (fun c => (hbound c).2)).trans_eq (by simp)⟩

/-- A bounded color moment is an actual scalar Graphon. -/
def momentGraphon [SFinite μ] (W : DecoratedKernel Ω C μ) (f : C → ℝ)
    (hf : StronglyMeasurable f) (hbound : ∀ c, f c ∈ Icc 0 1) : Graphon Ω μ where
  toAEEqFun := AEEqFun.mk (W.moment f) (W.stronglyMeasurable_moment hf).aestronglyMeasurable
  symm' := by
    have h := AEEqFun.coeFn_mk (μ := μ.prod μ) (W.moment f)
      (W.stronglyMeasurable_moment hf).aestronglyMeasurable
    filter_upwards [h, ae_prod_swap h, W.moment_symm f] with p hp hps hsymm
    rw [hp, hps, hsymm]
  ae_mem_Icc := by
    filter_upwards [AEEqFun.coeFn_mk (W.moment f)
      (W.stronglyMeasurable_moment hf).aestronglyMeasurable] with p hp
    rw [hp]
    exact W.moment_mem_Icc hf hbound p

/-- Changing the latent law absolutely continuously preserves symmetry. -/
def changeMeasure [SFinite μ] [SFinite ν] (W : DecoratedKernel Ω C μ) (hν : ν ≪ μ) :
    DecoratedKernel Ω C ν where
  kernel := W.kernel
  markov := W.markov
  symm := (hν.prod hν).ae_le W.symm

/-- Finite independent samples of colors indexed by any specified list of
latent pairs. In particular each unordered clique pair is sampled once. -/
def sampleLaw {ι : Type*} [Fintype ι] (W : DecoratedKernel Ω C μ)
    (pairs : ι → Ω × Ω) : Measure (ι → C) :=
  Measure.pi (fun i => W.kernel (pairs i))

instance {ι : Type*} [Fintype ι] (W : DecoratedKernel Ω C μ)
    (pairs : ι → Ω × Ω) : IsProbabilityMeasure (W.sampleLaw pairs) := by
  unfold sampleLaw
  infer_instance

theorem sampleLaw_rectangle {ι : Type*} [Fintype ι] (W : DecoratedKernel Ω C μ)
    (pairs : ι → Ω × Ω) (s : ι → Set C) :
    W.sampleLaw pairs (Set.univ.pi s) = ∏ i, W.kernel (pairs i) (s i) :=
  Measure.pi_pi _ _

/-- Conditional finite independent sampling itself forms a Markov kernel.
The measurability proof uses actual product measures on rectangles. -/
def sampleKernel {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (W : DecoratedKernel Ω C μ) (pairs : X → ι → Ω × Ω)
    (hpairs : ∀ i, Measurable (fun x => pairs x i)) : Kernel X (ι → C) where
  toFun x := W.sampleLaw (pairs x)
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_pi.symm isPiSystem_pi
    rintro s ⟨t, ht, rfl⟩
    simp only [sampleLaw_rectangle]
    exact Finset.measurable_prod _ (fun i _ =>
      (W.kernel.measurable_coe (ht i (Set.mem_univ i))).comp (hpairs i))

instance {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (W : DecoratedKernel Ω C μ) (pairs : X → ι → Ω × Ω)
    (hpairs : ∀ i, Measurable (fun x => pairs x i)) :
    IsMarkovKernel (W.sampleKernel pairs hpairs) := by
  constructor
  intro x
  change IsProbabilityMeasure (W.sampleLaw (pairs x))
  infer_instance

/-- Applying a measurable map to each independently sampled color. -/
def map {D : Type*} [MeasurableSpace D] (W : DecoratedKernel Ω C μ)
    (f : C → D) (hf : Measurable f) : DecoratedKernel Ω D μ where
  kernel := W.kernel.map f
  markov := Kernel.IsMarkovKernel.map W.kernel hf
  symm := by
    filter_upwards [W.symm] with p hp
    simp only [Kernel.map_apply _ hf, hp]

theorem sampleLaw_map {ι D : Type*} [Fintype ι] [MeasurableSpace D]
    (W : DecoratedKernel Ω C μ) (pairs : ι → Ω × Ω)
    (f : C → D) (hf : Measurable f) :
    (W.map f hf).sampleLaw pairs =
      (W.sampleLaw pairs).map (fun c i => f (c i)) := by
  unfold sampleLaw
  simp only [map, Kernel.map_apply _ hf]
  exact (Measure.pi_map_pi (fun _ => hf.aemeasurable)).symm

/-- Absolute continuity of latent laws passes to every finite independent
vertex sample. This is the measure-theoretic basis of vertex reweighting. -/
theorem pi_absolutelyContinuous [SigmaFinite μ] [SigmaFinite ν] (hν : ν ≪ μ) (n : ℕ) :
    Measure.pi (fun _ : Fin n => ν) ≪ Measure.pi (fun _ : Fin n => μ) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty _ (fun i : Fin 0 => Fin.elim0 i),
      Measure.pi_of_empty _ (fun i : Fin 0 => Fin.elim0 i)]
  | succ n ih =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0).symm
    have h := e.measurableEmbedding.absolutelyContinuous_map (hν.prod ih)
    have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    have hν' := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).symm
    rw [← hμ.map_eq, ← hν'.map_eq]
    exact h

end DecoratedKernel

end Erdos1017
