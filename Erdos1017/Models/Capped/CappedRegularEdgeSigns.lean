module

public import Erdos1017.Models.Capped.CappedShiftedMoment

/-!
# Edge signs for the regular multiplier

For the vertex multiplier already chosen, masked deletion forces the regular
shifted mean kernel to be nonnegative almost everywhere, same-support insertion
supplies complementarity, and global deletion and charge-minus-three insertion
bound the multiplier.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual masked deletion forces the regular shifted mean kernel to be
nonnegative almost everywhere, for the vertex multiplier already chosen. -/
theorem regular_shiftedMoment_nonnegative (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (m : ℝ) (hm : Variation.weightFirstVariation (chargeOperator W) =
      m • Variation.weightFirstVariation (adjacencyOperator W))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0) :
    ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p := by
  classical
  let s := {p : Ω × Ω | shiftedMoment W m p < 0}
  have hs : MeasurableSet s := measurableSet_lt
    (W.stronglyMeasurable_moment (continuous_shiftedColor m).measurable.stronglyMeasurable).measurable
    measurable_const
  have hsym : ∀ᵐ p ∂μ.prod μ, p.swap ∈ s ↔ p ∈ s := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    change shiftedMoment W m p.swap < 0 ↔ shiftedMoment W m p < 0
    rw [hp]
  have hg := affine_edit_sign W hW (maskedThinningEdit W s hs hsym) m hm hregular
  change objective (maskedThin W 1 s hs hsym) - objective W -
    m * (density (maskedThin W 1 s hs hsym) - density W) ≤ 0 at hg
  rw [shifted_gain_eq_integral] at hg
  have hdiff (p : Ω × Ω) :
      shiftedMoment (maskedThin W 1 s hs hsym) m p - shiftedMoment W m p =
        -s.indicator (shiftedMoment W m) p := by
    rw [shiftedMoment_maskedThin]
    by_cases hp : p ∈ s <;> simp [hp]
  have heq : (∫ p, shiftedMoment (maskedThin W 1 s hs hsym) m p - shiftedMoment W m p ∂μ.prod μ) =
      -(∫ p, s.indicator (shiftedMoment W m) p ∂μ.prod μ) := by
    simp_rw [hdiff]
    exact integral_neg _
  rw [heq] at hg
  have hnonneg : 0 ≤ ∫ p, s.indicator (shiftedMoment W m) p ∂μ.prod μ := by linarith
  have hpoint (p : Ω × Ω) : s.indicator (shiftedMoment W m) p ≤ 0 := by
    by_cases hp : p ∈ s
    · rw [Set.indicator_of_mem hp]
      exact le_of_lt hp
    · rw [Set.indicator_of_notMem hp]
  have hzint : (∫ p, s.indicator (shiftedMoment W m) p ∂μ.prod μ) = 0 :=
    le_antisymm (integral_nonpos hpoint) hnonneg
  have hz : ∀ᵐ p ∂μ.prod μ, -s.indicator (shiftedMoment W m) p = 0 := by
    apply (integral_eq_zero_iff_of_nonneg (fun p => neg_nonneg.mpr (hpoint p))
      ((integrable_shiftedMoment W m).indicator hs).neg).mp
    rw [integral_neg, hzint, neg_zero]
  filter_upwards [hz] with p hp
  by_contra hneg
  have hmem : p ∈ s := lt_of_not_ge hneg
  rw [Set.indicator_of_mem hmem] at hp
  linarith

theorem presentFactor_one_ge_one (a : ℝ) (ha : a ∈ Icc 0 1) : 1 ≤ presentFactor a 1 := by
  unfold presentFactor
  split_ifs with h
  · norm_num
    simpa only [one_div] using (one_le_div h).mpr ha.2
  · norm_num

/-- Same-support insertion supplies complementarity for that same regular
multiplier. The actual edit increment is integrable and nonnegative. -/
theorem regular_shiftedMoment_complementary (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (m : ℝ) (hm : Variation.weightFirstVariation (chargeOperator W) =
      m • Variation.weightFirstVariation (adjacencyOperator W))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0) :
    ∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0 := by
  have hg := affine_edit_sign W hW (supportInsertionEdit W) m hm hregular
  change objective (supportInsert W 1) - objective W -
    m * (density (supportInsert W 1) - density W) ≤ 0 at hg
  rw [shifted_gain_eq_integral] at hg
  have hnonpos : (∫ p, shiftedMoment (supportInsert W 1) m p - shiftedMoment W m p ∂μ.prod μ) ≤ 0 := by
    linarith
  have hdelta : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment (supportInsert W 1) m p - shiftedMoment W m p := by
    filter_upwards [regular_shiftedMoment_nonnegative W hW m hm hregular] with p hp
    rw [shiftedMoment_supportInsert]
    have hf := presentFactor_one_ge_one _ (adjacency_moment_mem W p)
    nlinarith
  have hzint : (∫ p, shiftedMoment (supportInsert W 1) m p - shiftedMoment W m p ∂μ.prod μ) = 0 :=
    le_antisymm hnonpos (integral_nonneg_of_ae hdelta)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hdelta
    ((integrable_shiftedMoment (supportInsert W 1) m).sub (integrable_shiftedMoment W m))).mp hzint
  filter_upwards [hz] with p hp
  change shiftedMoment (supportInsert W 1) m p - shiftedMoment W m p = 0 at hp
  rw [shiftedMoment_supportInsert] at hp
  by_cases hA : 0 < W.moment CappedColor.adjacency p
  · have hf : presentFactor (W.moment CappedColor.adjacency p) 1 *
        W.moment CappedColor.adjacency p = 1 := by
      simp only [presentFactor, hA, ↓reduceIte]
      change ((W.moment CappedColor.adjacency p + 1 * (1 - W.moment CappedColor.adjacency p)) /
        W.moment CappedColor.adjacency p) * W.moment CappedColor.adjacency p = 1
      rw [div_mul_cancel₀ _ hA.ne']
      ring
    calc
      _ = W.moment CappedColor.adjacency p *
          (presentFactor (W.moment CappedColor.adjacency p) 1 * shiftedMoment W m p - shiftedMoment W m p) := by
        rw [mul_sub]
        have heq : W.moment CappedColor.adjacency p *
            (presentFactor (W.moment CappedColor.adjacency p) 1 * shiftedMoment W m p) = shiftedMoment W m p := by
          calc
            _ = (presentFactor (W.moment CappedColor.adjacency p) 1 * W.moment CappedColor.adjacency p) *
                shiftedMoment W m p := by ring
            _ = _ := by rw [hf, one_mul]
        rw [heq]
        ring
      _ = 0 := by rw [hp, mul_zero]
  · have hzero := le_antisymm (not_lt.mp hA) (adjacency_moment_mem W p).1
    rw [shiftedMoment_eq, charge_moment_of_adjacency_zero W p hzero, hzero]
    ring

/-- Global deletion and charge-minus-three insertion bound the same regular
multiplier. With `ell=-m`, this is `-1≤ell≤3`. -/
theorem regular_multiplier_bounds (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (m : ℝ) (hm : Variation.weightFirstVariation (chargeOperator W) =
      m • Variation.weightFirstVariation (adjacencyOperator W))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (hd0 : 0 < density W) (hdhalf : density W < 1 / 2) : -3 ≤ m ∧ m ≤ 1 := by
  have hdel := affine_edit_sign W hW (thinningEdit W) m hm hregular
  change objective (thin W 1) - objective W - m * (density (thin W 1) - density W) ≤ 0 at hdel
  rw [objective_thin, density_thin] at hdel
  norm_num at hdel
  have hins := affine_edit_sign W hW (sprinklingEdit W) m hm hregular
  change objective (sprinkle W 1) - objective W - m * (density (sprinkle W 1) - density W) ≤ 0 at hins
  rw [objective_sprinkle, density_sprinkle] at hins
  norm_num at hins
  constructor
  · by_contra h
    have hmneg : m + 3 < 0 := by linarith
    have hp := mul_neg_of_neg_of_pos hmneg (sub_pos.mpr hdhalf)
    nlinarith
  · by_contra h
    have hmpos : 0 < m - 1 := by linarith
    have hp := mul_pos hmpos hd0
    nlinarith [objective_le_density W]

end Erdos1017.CappedModel
