module

public import Erdos1017.Models.Capped.CappedUniversalVertices
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrals after adjoining universal vertices

Regrouping the two original labels with two independent universal marks gives
the exact average of any bounded scalar kernel after universal vertices receive
a constant incident value.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Regroup the two old labels and two independent universal marks. -/
theorem universal_pair_shuffle (t : unitInterval) :
    MeasurePreserving
      (fun p : (Ω × Bool) × (Ω × Bool) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((universalMeasure μ t).prod (universalMeasure μ t))
      ((μ.prod μ).prod ((bernoulliMeasure true false t).prod (bernoulliMeasure true false t))) := by
  let η := bernoulliMeasure true false t
  have hstart := (measurePreserving_prodAssoc (μ.prod η) μ η).symm
  have hinner := (measurePreserving_prodAssoc μ μ η).symm.comp
    (((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := η) (ν := μ))).comp
      (measurePreserving_prodAssoc μ η μ))
  have hfinish := (measurePreserving_prodAssoc (μ.prod μ) η η).comp
    ((hinner.prod (MeasurePreserving.id η)).comp hstart)
  exact hfinish

theorem integral_universalCoins (t : unitInterval) (k v : ℝ) :
    (∫ b : Bool × Bool, if b.1 = true ∨ b.2 = true then k else v
      ∂(bernoulliMeasure true false t).prod (bernoulliMeasure true false t)) =
      (2 * (t : ℝ) - (t : ℝ) ^ 2) * k + (1 - (t : ℝ)) ^ 2 * v := by
  rw [integral_prod _ Integrable.of_finite]
  simp only [integral_bernoulliMeasure, Bool.false_eq_true, or_self, or_true, true_or,
    ↓reduceIte, smul_eq_mul]
  ring

/-- Exact average of any bounded scalar kernel after universal vertices
are assigned a constant incident value. -/
theorem integral_universal_kernel (t : unitInterval) (K : Ω × Ω → ℝ)
    (hK : StronglyMeasurable K) (B : ℝ) (hB : ∀ p, ‖K p‖ ≤ B) (k : ℝ) :
    (∫ p : (Ω × Bool) × (Ω × Bool),
      if p.1.2 = true ∨ p.2.2 = true then k else K (p.1.1, p.2.1)
      ∂(universalMeasure μ t).prod (universalMeasure μ t)) =
      (2 * (t : ℝ) - (t : ℝ) ^ 2) * k +
        (1 - (t : ℝ)) ^ 2 * ∫ p, K p ∂μ.prod μ := by
  let J : (Ω × Ω) × (Bool × Bool) → ℝ := fun p =>
    if p.2.1 = true ∨ p.2.2 = true then k else K p.1
  have hbool : MeasurableSet {p : (Ω × Ω) × (Bool × Bool) |
      p.2.1 = true ∨ p.2.2 = true} := by
    exact (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).union
      (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const)
  have hJ : StronglyMeasurable J :=
    (measurable_const.ite hbool (hK.measurable.comp measurable_fst)).stronglyMeasurable
  have hint : Integrable J
      ((μ.prod μ).prod ((bernoulliMeasure true false t).prod (bernoulliMeasure true false t))) := by
    apply Integrable.of_bound hJ.aestronglyMeasurable (max ‖k‖ B)
    filter_upwards with p
    dsimp only [J]
    split_ifs
    · exact le_max_left _ _
    · exact (hB p.1).trans (le_max_right _ _)
  have hmap := integral_map_of_stronglyMeasurable
    (μ := (universalMeasure μ t).prod (universalMeasure μ t)) (universal_pair_shuffle (μ := μ) t).measurable hJ
  rw [(universal_pair_shuffle (μ := μ) t).map_eq] at hmap
  change (∫ p, J (((p.1.1, p.2.1), (p.1.2, p.2.2)))
    ∂(universalMeasure μ t).prod (universalMeasure μ t)) = _
  rw [← hmap, integral_prod _ hint]
  change (∫ x : Ω × Ω, ∫ b : Bool × Bool,
    if b.1 = true ∨ b.2 = true then k else K x
      ∂(bernoulliMeasure true false t).prod (bernoulliMeasure true false t) ∂μ.prod μ) = _
  simp_rw [integral_universalCoins]
  have hi : Integrable K (μ.prod μ) :=
    Integrable.of_bound hK.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul]
  simp [integral_const_mul]

end Erdos1017.CappedModel
