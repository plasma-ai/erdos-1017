module

public import Erdos1017.Models.Capped.CappedModel
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Measurable pair-dependent color edits

A measurable pair-dependent color edit (`editKernel`, `edit`) gives a symmetric
decorated kernel without new latent or pair-color randomness, and deletions
depending measurably on both latent endpoints and the sampled color remain
feasible.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Erdos1017.DecoratedKernel

variable {Ω C D : Type*} [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace D]
  {μ : Measure Ω}

/-- A measurable pair-dependent color edit, constructed by retaining the
latent pair in the product kernel before applying the edit. -/
def editKernel (W : DecoratedKernel Ω C μ) (f : (Ω × Ω) × C → D) : Kernel (Ω × Ω) D :=
  (Kernel.id ×ₖ W.kernel).map f

theorem editKernel_apply (W : DecoratedKernel Ω C μ) (f : (Ω × Ω) × C → D)
    (hf : Measurable f) (p : Ω × Ω) :
    W.editKernel f p = (W.kernel p).map (fun c => f (p, c)) := by
  rw [editKernel, Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
  rfl

theorem editKernel_markov (W : DecoratedKernel Ω C μ) (f : (Ω × Ω) × C → D) (hf : Measurable f) :
    IsMarkovKernel (W.editKernel f) :=
  Kernel.IsMarkovKernel.map _ hf

/-- Symmetric measurable color edits give actual symmetric decorated
kernels. No new latent or pair-color randomness is assumed. -/
def edit (W : DecoratedKernel Ω C μ) (f : (Ω × Ω) × C → D) (hf : Measurable f)
    (hsym : ∀ᵐ p ∂μ.prod μ, ∀ c, f (p.swap, c) = f (p, c)) : DecoratedKernel Ω D μ where
  kernel := W.editKernel f
  markov := editKernel_markov W f hf
  symm := by
    filter_upwards [W.symm, hsym] with p hp hfp
    rw [editKernel_apply W f hf, editKernel_apply W f hf, hp]
    exact Measure.map_congr (Filter.Eventually.of_forall hfp)

theorem sampleLaw_edit {ι : Type*} [Fintype ι] (W : DecoratedKernel Ω C μ)
    (f : (Ω × Ω) × C → D) (hf : Measurable f)
    (hsym : ∀ᵐ p ∂μ.prod μ, ∀ c, f (p.swap, c) = f (p, c)) (pairs : ι → Ω × Ω) :
    (W.edit f hf hsym).sampleLaw pairs =
      (W.sampleLaw pairs).map (fun c i => f (pairs i, c i)) := by
  unfold sampleLaw
  simp only [edit, editKernel_apply W f hf]
  exact (Measure.pi_map_pi (fun i =>
    (hf.comp measurable_prodMk_left).aemeasurable)).symm

end Erdos1017.DecoratedKernel

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Deletions may depend measurably on both latent endpoints and on the
sampled color. The whole finite collection of pair deletions is feasible. -/
theorem feasible_edit_deletion (W : Model Ω μ) {r : ℕ} (hW : Feasible r W)
    (f : (Ω × Ω) × CappedColor → CappedColor) (hf : Measurable f)
    (hsym : ∀ᵐ p ∂μ.prod μ, ∀ c, f (p.swap, c) = f (p, c))
    (hdelete : ∀ p c, f (p, c) = CappedColor.absent ∨ f (p, c) = c) :
    Feasible r (W.edit f hf hsym) := by
  intro n hn hnr
  filter_upwards [hW n hn hnr] with x hx
  unfold cliqueLaw
  rw [DecoratedKernel.sampleLaw_edit]
  have hm : Measurable (fun c : CliquePair n → CappedColor =>
      fun e => f ((x e.val.1, x e.val.2), c e)) :=
    measurable_pi_iff.mpr (fun e =>
      hf.comp (measurable_const.prodMk (measurable_pi_apply e)))
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun (continuous_violation n).measurable measurable_const)).2
  filter_upwards [hx] with c hc
  classical
  by_cases h : ∃ e, f ((x e.val.1, x e.val.2), c e) = CappedColor.absent
  · obtain ⟨e, he⟩ := h
    have hprod : (∏ i, CappedColor.adjacency (f ((x i.val.1, x i.val.2), c i))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) (by rw [he]; rfl)
    simp only [violation, hprod, mul_zero]
  · have heq : ∀ e, f ((x e.val.1, x e.val.2), c e) = c e := by
      intro e
      exact (hdelete _ _).resolve_left (fun he => h ⟨e, he⟩)
    simpa only [heq] using hc

end Erdos1017.CappedModel
