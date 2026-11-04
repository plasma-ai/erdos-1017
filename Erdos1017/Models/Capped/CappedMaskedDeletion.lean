module

public import Erdos1017.Models.Capped.CappedRandomDeletion

/-!
# Masked independent deletion

Masked thinning (`maskedThin`) independently deletes a fraction `t` of outcomes
only on a measurable symmetric latent pair set; it is feasible and its moments
vary affinely in `t`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

open scoped Classical in
def maskedCoinDelete (s : Set (Ω × Ω)) (z : (Ω × Ω) × (CappedColor × Bool)) : CappedColor :=
  if z.1 ∈ s ∧ z.2.2 = true then CappedColor.absent else z.2.1

theorem measurable_maskedCoinDelete (s : Set (Ω × Ω)) (hs : MeasurableSet s) :
    Measurable (maskedCoinDelete s) :=
  measurable_const.ite ((hs.preimage measurable_fst).inter
    (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const))
    (measurable_fst.comp measurable_snd)

/-- Independently delete fraction `t` of outcomes only on a measurable
symmetric latent pair set. -/
def maskedThin (W : Model Ω μ) (t : unitInterval) (s : Set (Ω × Ω)) (hs : MeasurableSet s)
    (hsym : ∀ᵐ p ∂μ.prod μ, p.swap ∈ s ↔ p ∈ s) : Model Ω μ :=
  (W.couple (bernoulliMeasure true false t)).edit (maskedCoinDelete s) (measurable_maskedCoinDelete s hs)
    (by
      classical
      filter_upwards [hsym] with p hp
      intro c
      by_cases hps : p ∈ s
      · have hswap : p.swap ∈ s := hp.mpr hps
        simp only [maskedCoinDelete, hps, hswap, true_and]
      · have hswap : p.swap ∉ s := fun h => hps (hp.mp h)
        simp only [maskedCoinDelete, hps, hswap, false_and, ↓reduceIte])

theorem feasible_maskedThin (W : Model Ω μ) {r : ℕ} (hW : Feasible r W) (t : unitInterval)
    (s : Set (Ω × Ω)) (hs : MeasurableSet s)
    (hsym : ∀ᵐ p ∂μ.prod μ, p.swap ∈ s ↔ p ∈ s) : Feasible r (maskedThin W t s hs hsym) := by
  apply feasible_random_deletion W hW
  intro p c u
  classical
  by_cases h : p ∈ s ∧ u = true <;> simp [maskedCoinDelete, h]

open scoped Classical in
theorem moment_maskedThin (W : Model Ω μ) (t : unitInterval) (s : Set (Ω × Ω))
    (hs : MeasurableSet s) (hsym : ∀ᵐ p ∂μ.prod μ, p.swap ∈ s ↔ p ∈ s)
    (p : Ω × Ω) (h : CappedColor → ℝ) (hh : StronglyMeasurable h)
    (hzero : h CappedColor.absent = 0) (B : ℝ) (hB : ∀ c, ‖h c‖ ≤ B) :
    (maskedThin W t s hs hsym).moment h p =
      if p ∈ s then (1 - (t : ℝ)) * W.moment h p else W.moment h p := by
  change (∫ c, h c ∂(W.couple (bernoulliMeasure true false t)).editKernel (maskedCoinDelete s) p) = _
  rw [DecoratedKernel.editKernel_apply _ _ (measurable_maskedCoinDelete s hs),
    integral_map_of_stronglyMeasurable (φ := fun c : CappedColor × Bool => maskedCoinDelete s (p, c))
      ((measurable_maskedCoinDelete s hs).comp measurable_prodMk_left) hh]
  simp only [DecoratedKernel.couple, ProbabilityTheory.Kernel.prod_apply,
    ProbabilityTheory.Kernel.const_apply]
  have hint : Integrable (fun q : CappedColor × Bool => h (maskedCoinDelete s (p, q)))
      ((W.kernel p).prod (bernoulliMeasure true false t)) :=
    Integrable.of_bound (hh.comp_measurable
      ((measurable_maskedCoinDelete s hs).comp measurable_prodMk_left)).aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun q => hB _))
  rw [integral_prod _ hint]
  by_cases hp : p ∈ s
  · simp only [maskedCoinDelete, hp, true_and, integral_bernoulliMeasure,
      ↓reduceIte, hzero, smul_eq_mul, mul_zero, zero_add]
    exact integral_const_mul _ _
  · simp only [maskedCoinDelete, hp, false_and, ↓reduceIte, integral_const,
      probReal_univ, one_smul]
    rfl

theorem moment_maskedThin_affine (W : Model Ω μ) (t : unitInterval) (s : Set (Ω × Ω))
    (hs : MeasurableSet s) (hsym : ∀ᵐ p ∂μ.prod μ, p.swap ∈ s ↔ p ∈ s)
    (p : Ω × Ω) (h : CappedColor → ℝ) (hh : StronglyMeasurable h)
    (hzero : h CappedColor.absent = 0) (B : ℝ) (hB : ∀ c, ‖h c‖ ≤ B) :
    (maskedThin W t s hs hsym).moment h p = W.moment h p +
      (t : ℝ) * ((maskedThin W 1 s hs hsym).moment h p - W.moment h p) := by
  classical
  rw [moment_maskedThin W t s hs hsym p h hh hzero B hB,
    moment_maskedThin W 1 s hs hsym p h hh hzero B hB]
  split_ifs
  · norm_num
    ring
  · ring

end Erdos1017.CappedModel
