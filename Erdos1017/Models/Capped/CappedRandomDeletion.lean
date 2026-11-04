module

public import Erdos1017.Models.Capped.CappedPairEdits
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Randomized deletion in capped models

Coupling an independent auxiliary choice to each pair color (`couple`) recovers
the original color law when forgotten, randomized deletions preserve capped
feasibility, and independent deletion of a fraction `t` of all outcomes (`thin`)
has an exact linear effect on every bounded color moment vanishing on absent
pairs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Erdos1017.DecoratedKernel

variable {Ω C U : Type*} [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace U]
  {μ : Measure Ω}

/-- Adjoin an independent auxiliary random choice to each pair color. -/
def couple (W : DecoratedKernel Ω C μ) (η : Measure U) [IsProbabilityMeasure η] :
    DecoratedKernel Ω (C × U) μ where
  kernel := W.kernel ×ₖ Kernel.const (Ω × Ω) η
  markov := by infer_instance
  symm := by
    filter_upwards [W.symm] with p hp
    simp only [Kernel.prod_apply, Kernel.const_apply, hp]

/-- Forgetting the auxiliary choices recovers exactly the old independent
color law, simultaneously at every sampled pair. -/
theorem sampleLaw_couple_fst {ι : Type*} [Fintype ι] (W : DecoratedKernel Ω C μ)
    (η : Measure U) [IsProbabilityMeasure η] (pairs : ι → Ω × Ω) :
    ((W.couple η).sampleLaw pairs).map (fun c i => (c i).1) = W.sampleLaw pairs := by
  unfold sampleLaw
  rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
  simp only [couple, Kernel.prod_apply, Kernel.const_apply, Measure.map_fst_prod,
    measure_univ, one_smul]

end Erdos1017.DecoratedKernel

namespace Erdos1017.CappedModel

variable {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U] {μ : Measure Ω}

/-- Actual randomized deletions preserve capped feasibility. Auxiliary
choices are sampled independently conditional on each latent pair. -/
theorem feasible_random_deletion (W : Model Ω μ) {r : ℕ} (hW : Feasible r W)
    (η : Measure U) [IsProbabilityMeasure η]
    (f : (Ω × Ω) × (CappedColor × U) → CappedColor) (hf : Measurable f)
    (hsym : ∀ᵐ p ∂μ.prod μ, ∀ c, f (p.swap, c) = f (p, c))
    (hdelete : ∀ p c u, f (p, (c, u)) = CappedColor.absent ∨ f (p, (c, u)) = c) :
    Feasible r ((W.couple η).edit f hf hsym) := by
  intro n hn hnr
  filter_upwards [hW n hn hnr] with x hx
  let pairs : CliquePair n → Ω × Ω := fun e => (x e.val.1, x e.val.2)
  have hproj : ∀ᵐ c ∂(W.couple η).sampleLaw pairs,
      violation (fun e => (c e).1) = 0 := by
    have hm : Measurable (fun c : CliquePair n → CappedColor × U => fun e => (c e).1) :=
      measurable_pi_iff.mpr (fun e => measurable_fst.comp (measurable_pi_apply e))
    change ∀ᵐ c ∂W.sampleLaw pairs, violation c = 0 at hx
    rw [← DecoratedKernel.sampleLaw_couple_fst W η pairs] at hx
    exact ae_of_ae_map hm.aemeasurable hx
  unfold cliqueLaw
  rw [DecoratedKernel.sampleLaw_edit]
  have hm : Measurable (fun c : CliquePair n → CappedColor × U =>
      fun e => f (pairs e, c e)) :=
    measurable_pi_iff.mpr (fun e =>
      hf.comp (measurable_const.prodMk (measurable_pi_apply e)))
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun (continuous_violation n).measurable measurable_const)).2
  filter_upwards [hproj] with c hc
  classical
  by_cases h : ∃ e, f (pairs e, c e) = CappedColor.absent
  · obtain ⟨e, he⟩ := h
    have hprod : (∏ i, CappedColor.adjacency (f (pairs i, c i))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) (by rw [he]; rfl)
    simp only [violation, hprod, mul_zero]
  · have heq : ∀ e, f (pairs e, c e) = (c e).1 := by
      intro e
      exact (hdelete _ _ _).resolve_left (fun he => h ⟨e, he⟩)
    simpa only [heq] using hc

/-- The independent deletion coin retains or deletes the old outcome. -/
def coinDelete (z : (Ω × Ω) × (CappedColor × Bool)) : CappedColor :=
  if z.2.2 = true then CappedColor.absent else z.2.1

theorem measurable_coinDelete : Measurable (coinDelete (Ω := Ω)) := by
  have hs : MeasurableSet {z : (Ω × Ω) × (CappedColor × Bool) | z.2.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  exact measurable_const.ite hs (measurable_fst.comp measurable_snd)

/-- Delete an arbitrary fraction `t` of all pair outcomes, independently at
each pair, as an actual probability-valued decorated kernel. -/
def thin (W : Model Ω μ) (t : unitInterval) : Model Ω μ :=
  (W.couple (bernoulliMeasure true false t)).edit coinDelete measurable_coinDelete
    (Filter.Eventually.of_forall (fun _ _ => rfl))

theorem feasible_thin (W : Model Ω μ) {r : ℕ} (hW : Feasible r W) (t : unitInterval) :
    Feasible r (thin W t) := by
  apply feasible_random_deletion W hW
  intro p c u
  cases u <;> simp [coinDelete]

/-- Independent deletion has the exact linear effect on every bounded
color moment that vanishes on absent pairs. -/
theorem moment_thin (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω)
    (h : CappedColor → ℝ) (hh : StronglyMeasurable h) (hzero : h CappedColor.absent = 0)
    (B : ℝ) (hB : ∀ c, ‖h c‖ ≤ B) :
    (thin W t).moment h p = (1 - (t : ℝ)) * W.moment h p := by
  change (∫ c, h c ∂(W.couple (bernoulliMeasure true false t)).editKernel coinDelete p) = _
  rw [DecoratedKernel.editKernel_apply _ _ measurable_coinDelete,
    integral_map_of_stronglyMeasurable
      (φ := fun c : CappedColor × Bool => coinDelete (p, c))
      (measurable_coinDelete.comp measurable_prodMk_left) hh]
  simp only [DecoratedKernel.couple, Kernel.prod_apply, Kernel.const_apply]
  have hint : Integrable (fun q : CappedColor × Bool => h (coinDelete (p, q)))
      ((W.kernel p).prod (bernoulliMeasure true false t)) :=
    Integrable.of_bound (hh.comp_measurable
      (measurable_coinDelete.comp measurable_prodMk_left)).aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun q => hB _))
  rw [integral_prod _ hint]
  simp only [integral_bernoulliMeasure, coinDelete,
    ↓reduceIte, hzero, smul_eq_mul, mul_zero, zero_add]
  exact integral_const_mul _ _

theorem density_thin (W : Model Ω μ) (t : unitInterval) :
    density (thin W t) = (1 - (t : ℝ)) * density W := by
  have hm (p : Ω × Ω) := moment_thin W t p CappedColor.adjacency
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable
    CappedColor.adjacency_absent 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)
  unfold density
  simp_rw [hm]
  rw [integral_const_mul]
  ring

theorem objective_thin (W : Model Ω μ) (t : unitInterval) :
    objective (thin W t) = (1 - (t : ℝ)) * objective W := by
  have hm (p : Ω × Ω) := moment_thin W t p CappedColor.charge
    CappedColor.continuous_charge.measurable.stronglyMeasurable
    CappedColor.charge_absent 3 (fun c => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
        (CappedColor.charge_mem c).2.trans (by norm_num)⟩)
  unfold objective
  simp_rw [hm]
  rw [integral_const_mul]
  ring

end Erdos1017.CappedModel
