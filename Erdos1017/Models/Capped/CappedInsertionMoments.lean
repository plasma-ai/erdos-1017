module

public import Erdos1017.Models.Capped.CappedInsertion

/-!
# Moments of insertion and sprinkling

Sprinkling is the exact convex interpolation between retaining an outcome and
inserting it at the repair charge; it inserts exactly fraction `t` of the absent
pair mass, and its objective cost is three times the inserted density.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem moment_insertAbsent (W : Model Ω μ) (p : Ω × Ω)
    (h : CappedColor → ℝ) (hh : StronglyMeasurable h) :
    (insertAbsent W).moment h p = ∫ c, h (insertColor c) ∂W.kernel p := by
  change (∫ c, h c ∂(W.kernel.map insertColor) p) = _
  rw [ProbabilityTheory.Kernel.map_apply _ measurable_insertColor,
    integral_map_of_stronglyMeasurable measurable_insertColor hh]

/-- Sprinkling is the exact convex interpolation between retaining an old
outcome and inserting it at the repair charge. -/
theorem moment_sprinkle (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω)
    (h : CappedColor → ℝ) (hh : StronglyMeasurable h) (B : ℝ) (hB : ∀ c, ‖h c‖ ≤ B) :
    (sprinkle W t).moment h p = (t : ℝ) * (insertAbsent W).moment h p +
      (1 - (t : ℝ)) * W.moment h p := by
  change (∫ c, h c ∂(W.couple (bernoulliMeasure true false t)).editKernel insertCoin p) = _
  rw [DecoratedKernel.editKernel_apply _ _ measurable_insertCoin,
    integral_map_of_stronglyMeasurable
      (φ := fun c : CappedColor × Bool => insertCoin (p, c))
      (measurable_insertCoin.comp measurable_prodMk_left) hh]
  simp only [DecoratedKernel.couple, ProbabilityTheory.Kernel.prod_apply,
    ProbabilityTheory.Kernel.const_apply]
  have hint : Integrable (fun q : CappedColor × Bool => h (insertCoin (p, q)))
      ((W.kernel p).prod (bernoulliMeasure true false t)) :=
    Integrable.of_bound (hh.comp_measurable
      (measurable_insertCoin.comp measurable_prodMk_left)).aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun q => hB _))
  rw [integral_prod _ hint]
  have hcoin (c : CappedColor) : (∫ u, h (insertCoin (p, (c, u)))
      ∂bernoulliMeasure true false t) =
      (t : ℝ) * h (insertColor c) + (1 - (t : ℝ)) * h c := by
    rw [integral_bernoulliMeasure]
    by_cases hc : CappedColor.adjacency c = 1 <;> simp [insertCoin, insertColor, hc, smul_eq_mul]
  simp_rw [hcoin]
  have hold : Integrable h (W.kernel p) :=
    Integrable.of_bound hh.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hnew : Integrable (fun c => h (insertColor c)) (W.kernel p) :=
    Integrable.of_bound (hh.comp_measurable measurable_insertColor).aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun c => hB _))
  rw [integral_add (hnew.const_mul _) (hold.const_mul _), integral_const_mul, integral_const_mul,
    moment_insertAbsent W p h hh]
  rfl

@[simp] theorem adjacency_insertColor (c : CappedColor) :
    CappedColor.adjacency (insertColor c) = 1 := by
  by_cases hc : CappedColor.adjacency c = 1 <;> simp [insertColor, hc]

theorem charge_insertColor (c : CappedColor) :
    CappedColor.charge (insertColor c) =
      CappedColor.charge c - 3 * (1 - CappedColor.adjacency c) := by
  by_cases hc : CappedColor.adjacency c = 1
  · simp [insertColor, hc]
  · rw [color_eq_absent_of_not_present c hc]
    norm_num [insertColor]

theorem adjacency_moment_insertAbsent (W : Model Ω μ) (p : Ω × Ω) :
    (insertAbsent W).moment CappedColor.adjacency p = 1 := by
  rw [moment_insertAbsent W p _ CappedColor.continuous_adjacency.measurable.stronglyMeasurable]
  simp

theorem charge_moment_insertAbsent (W : Model Ω μ) (p : Ω × Ω) :
    (insertAbsent W).moment CappedColor.charge p = W.moment CappedColor.charge p -
      3 * (1 - W.moment CappedColor.adjacency p) := by
  have ha : Integrable CappedColor.adjacency (W.kernel p) :=
    Integrable.of_bound CappedColor.continuous_adjacency.measurable.stronglyMeasurable.aestronglyMeasurable
      1 (Filter.Eventually.of_forall (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2))
  have hy : Integrable CappedColor.charge (W.kernel p) :=
    Integrable.of_bound CappedColor.continuous_charge.measurable.stronglyMeasurable.aestronglyMeasurable
      3 (Filter.Eventually.of_forall (fun c => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
          (CappedColor.charge_mem c).2.trans (by norm_num)⟩))
  rw [moment_insertAbsent W p _ CappedColor.continuous_charge.measurable.stronglyMeasurable]
  simp_rw [charge_insertColor]
  rw [integral_sub (f := CappedColor.charge)
    (g := fun c => 3 * (1 - CappedColor.adjacency c)) hy
    (((integrable_const 1).sub ha).const_mul 3), integral_const_mul,
    integral_sub (f := fun _ => (1 : ℝ)) (g := CappedColor.adjacency) (integrable_const 1) ha]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, DecoratedKernel.moment]

theorem adjacency_moment_sprinkle (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (sprinkle W t).moment CappedColor.adjacency p =
      (t : ℝ) + (1 - (t : ℝ)) * W.moment CappedColor.adjacency p := by
  rw [moment_sprinkle W t p _ CappedColor.continuous_adjacency.measurable.stronglyMeasurable
    1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2), adjacency_moment_insertAbsent, mul_one]

theorem charge_moment_sprinkle (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (sprinkle W t).moment CappedColor.charge p = W.moment CappedColor.charge p -
      3 * (t : ℝ) * (1 - W.moment CappedColor.adjacency p) := by
  rw [moment_sprinkle W t p _ CappedColor.continuous_charge.measurable.stronglyMeasurable
    3 (fun c => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
        (CappedColor.charge_mem c).2.trans (by norm_num)⟩), charge_moment_insertAbsent]
  ring

variable [IsProbabilityMeasure μ]

theorem integrable_bounded_moment (W : Model Ω μ) (h : CappedColor → ℝ)
    (hh : StronglyMeasurable h) (B : ℝ) (hB : ∀ c, ‖h c‖ ≤ B) :
    Integrable (W.moment h) (μ.prod μ) := by
  apply Integrable.of_bound (W.stronglyMeasurable_moment hh).aestronglyMeasurable B
  filter_upwards with p
  have he := norm_integral_le_of_norm_le_const (μ := W.kernel p)
    (Filter.Eventually.of_forall hB)
  simpa only [DecoratedKernel.moment, probReal_univ, mul_one] using he

/-- Sprinkling inserts exactly fraction `t` of the absent pair mass. -/
theorem density_sprinkle (W : Model Ω μ) (t : unitInterval) :
    density (sprinkle W t) = density W + (t : ℝ) * (1 / 2 - density W) := by
  have ha := integrable_bounded_moment W CappedColor.adjacency
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)
  unfold density
  simp_rw [adjacency_moment_sprinkle]
  rw [integral_add (integrable_const _) (ha.const_mul _), integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The exact objective cost of insertion is three times the inserted
density, using the actual feasible Bernoulli competitor. -/
theorem objective_sprinkle (W : Model Ω μ) (t : unitInterval) :
    objective (sprinkle W t) = objective W - 3 * (t : ℝ) * (1 / 2 - density W) := by
  have ha := integrable_bounded_moment W CappedColor.adjacency
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)
  have hy := integrable_bounded_moment W CappedColor.charge
    CappedColor.continuous_charge.measurable.stronglyMeasurable 3 (fun c => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
        (CappedColor.charge_mem c).2.trans (by norm_num)⟩)
  unfold objective density
  simp_rw [charge_moment_sprinkle]
  rw [integral_sub (f := W.moment CappedColor.charge)
    (g := fun p => 3 * (t : ℝ) * (1 - W.moment CappedColor.adjacency p)) hy
    (((integrable_const 1).sub ha).const_mul (3 * (t : ℝ))), integral_const_mul,
    integral_sub (f := fun _ => (1 : ℝ)) (g := W.moment CappedColor.adjacency)
      (integrable_const 1) ha]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

end Erdos1017.CappedModel
