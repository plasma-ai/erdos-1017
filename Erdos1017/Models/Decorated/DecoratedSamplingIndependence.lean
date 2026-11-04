module

public import Erdos1017.Models.Decorated.DecoratedTestConvergence
public import Erdos1017.Models.Decorated.DecoratedCountingIntegration
public import Mathlib.Probability.Independence.Integration

/-!
# Independence of colors on disjoint clique pairs

The sampled color at one clique pair has the averaged conditional color law, and
color tests on disjoint clique pairs are independent under the unconditional
latent-then-color sampling law.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The sampled color at one clique pair has the averaged conditional color law. -/
theorem integral_sampledColorLaw_pair (W : Model Ω μ) (n : ℕ)
    (e : CliquePair n) (f : C(CappedColor, ℝ)) :
    (∫ c, f (c e) ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) =
      ∫ p, W.moment f p ∂μ.prod μ := by
  let F : C(CliquePair n → CappedColor, ℝ) :=
    ⟨fun c => f (c e), f.continuous.comp (continuous_apply e)⟩
  change (∫ c, F c ∂(sampledColorLaw W n : Measure _)) = _
  rw [integral_sampledColorLaw]
  have hinner (x : Fin n → Ω) :
      (∫ c, f (c e) ∂cliqueLaw W x) = W.moment f (x e.val.1, x e.val.2) := by
    change (∫ c : CliquePair n → CappedColor, f (c e)
      ∂W.sampleLaw (fun i => (x i.val.1, x i.val.2))) = _
    exact integral_comp_eval f.continuous.aestronglyMeasurable
  change (∫ x : Fin n → Ω, ∫ c, f (c e) ∂cliqueLaw W x
    ∂Measure.pi (fun _ : Fin n => μ)) = _
  simp_rw [hinner]
  have hpair := DecoratedCounting.measurePreserving_pairProjection (μ := μ)
    e.val.1 e.val.2 (ne_of_lt e.property)
  have he := integral_map_of_stronglyMeasurable (μ := Measure.pi (fun _ : Fin n => μ))
    hpair.measurable (W.stronglyMeasurable_moment f.continuous.stronglyMeasurable)
  rw [hpair.map_eq] at he
  exact he.symm

/-- Color tests on disjoint clique pairs are independent under the actual
unconditional latent-then-color sampling law. -/
theorem integral_sampledColorLaw_disjoint_pairs (W : Model Ω μ) (n : ℕ)
    (e f : CliquePair n)
    (h11 : e.val.1 ≠ f.val.1) (h12 : e.val.1 ≠ f.val.2)
    (h21 : e.val.2 ≠ f.val.1) (h22 : e.val.2 ≠ f.val.2)
    (a b : C(CappedColor, ℝ)) :
    (∫ c, a (c e) * b (c f)
      ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) =
      (∫ p, W.moment a p ∂μ.prod μ) * (∫ p, W.moment b p ∂μ.prod μ) := by
  let F : C(CliquePair n → CappedColor, ℝ) :=
    ⟨fun c => a (c e) * b (c f),
      (a.continuous.comp (continuous_apply e)).mul
        (b.continuous.comp (continuous_apply f))⟩
  change (∫ c, F c ∂(sampledColorLaw W n : Measure _)) = _
  rw [integral_sampledColorLaw]
  have hef : e ≠ f := by
    intro h
    exact h11 (congrArg (fun q : CliquePair n => q.val.1) h)
  have hinner (x : Fin n → Ω) :
      (∫ c, a (c e) * b (c f) ∂cliqueLaw W x) =
        W.moment a (x e.val.1, x e.val.2) *
          W.moment b (x f.val.1, x f.val.2) := by
    let ν : CliquePair n → Measure CappedColor :=
      fun i => W.kernel (x i.val.1, x i.val.2)
    have hcolor : iIndepFun (fun i (c : CliquePair n → CappedColor) => c i)
        (Measure.pi ν) :=
      iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
    have hind : (fun c : CliquePair n → CappedColor => a (c e)) ⟂ᵢ[Measure.pi ν]
        (fun c => b (c f)) := by
      simpa only [Function.comp_def] using
        (hcolor.indepFun hef).comp a.continuous.measurable b.continuous.measurable
    have hprod := hind.integral_fun_mul_eq_mul_integral
      (a.continuous.stronglyMeasurable.comp_measurable (measurable_pi_apply e)).aestronglyMeasurable
      (b.continuous.stronglyMeasurable.comp_measurable (measurable_pi_apply f)).aestronglyMeasurable
    have heval := integral_comp_eval (μ := ν) (i := e)
      a.continuous.aestronglyMeasurable
    have hfval := integral_comp_eval (μ := ν) (i := f)
      b.continuous.aestronglyMeasurable
    simpa only [cliqueLaw, DecoratedKernel.sampleLaw, DecoratedKernel.moment, ν,
      heval, hfval] using hprod
  change (∫ x : Fin n → Ω, ∫ c, a (c e) * b (c f) ∂cliqueLaw W x
    ∂Measure.pi (fun _ : Fin n => μ)) = _
  simp_rw [hinner]
  have hlatent : iIndepFun (fun i (x : Fin n → Ω) => x i)
      (Measure.pi (fun _ : Fin n => μ)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h4 := hlatent.indepFun_prodMk_prodMk (fun i => measurable_pi_apply i)
    e.val.1 e.val.2 f.val.1 f.val.2 h11 h12 h21 h22
  have hma : Measurable (W.moment a) :=
    (W.stronglyMeasurable_moment a.continuous.stronglyMeasurable).measurable
  have hmb : Measurable (W.moment b) :=
    (W.stronglyMeasurable_moment b.continuous.stronglyMeasurable).measurable
  have h4' : (fun x : Fin n → Ω => W.moment a (x e.val.1, x e.val.2)) ⟂ᵢ[Measure.pi (fun _ : Fin n => μ)]
      (fun x => W.moment b (x f.val.1, x f.val.2)) := by
    simpa only [Function.comp_def] using h4.comp hma hmb
  have hprod := h4'.integral_fun_mul_eq_mul_integral
    (hma.comp ((measurable_pi_apply e.val.1).prodMk (measurable_pi_apply e.val.2))).aestronglyMeasurable
    (hmb.comp ((measurable_pi_apply f.val.1).prodMk (measurable_pi_apply f.val.2))).aestronglyMeasurable
  have hepair := DecoratedCounting.measurePreserving_pairProjection (μ := μ)
    e.val.1 e.val.2 (ne_of_lt e.property)
  have hfpair := DecoratedCounting.measurePreserving_pairProjection (μ := μ)
    f.val.1 f.val.2 (ne_of_lt f.property)
  have heavg := integral_map_of_stronglyMeasurable (μ := Measure.pi (fun _ : Fin n => μ))
    hepair.measurable (W.stronglyMeasurable_moment a.continuous.stronglyMeasurable)
  have hfavg := integral_map_of_stronglyMeasurable (μ := Measure.pi (fun _ : Fin n => μ))
    hfpair.measurable (W.stronglyMeasurable_moment b.continuous.stronglyMeasurable)
  rw [hepair.map_eq] at heavg
  rw [hfpair.map_eq] at hfavg
  simpa only [heavg, hfavg] using hprod

end Erdos1017.CappedModel
