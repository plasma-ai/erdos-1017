module

public import Erdos1017.Models.Capped.CappedRegularEdgeSigns
public import Erdos1017.Models.Capped.CappedAveraging

/-!
# Deterministic shifted colors of the averaged optimizer

For the averaged optimizer, regular edge complementarity turns the shifted
sampled color into its deterministic shifted mean kernel, and that regular
shifted mean is bounded in `[0,4]` by the multiplier bounds from deletion and
insertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_adjacency_zero_of_moment_zero (W : Model Ω μ) (p : Ω × Ω)
    (hA : W.moment CappedColor.adjacency p = 0) :
    ∀ᵐ c ∂W.kernel p, CappedColor.adjacency c = 0 := by
  exact (integral_eq_zero_iff_of_nonneg (fun c => (CappedColor.adjacency_mem c).1)
    (integrable_color_adjacency W p)).mp hA

theorem ae_adjacency_one_of_moment_one (W : Model Ω μ) (p : Ω × Ω)
    (hA : W.moment CappedColor.adjacency p = 1) :
    ∀ᵐ c ∂W.kernel p, CappedColor.adjacency c = 1 := by
  have ha := integrable_color_adjacency W p
  have hz : (∫ c, 1 - CappedColor.adjacency c ∂W.kernel p) = 0 := by
    rw [integral_sub (f := fun _ => (1 : ℝ)) (g := CappedColor.adjacency) (integrable_const 1) ha]
    change (∫ _c, (1 : ℝ) ∂W.kernel p) - W.moment CappedColor.adjacency p = 0
    simp [hA]
  have he := (integral_eq_zero_iff_of_nonneg
    (fun c => sub_nonneg.mpr (CappedColor.adjacency_mem c).2) ((integrable_const 1).sub ha)).mp hz
  filter_upwards [he] with c hc
  change 1 - CappedColor.adjacency c = 0 at hc
  linarith

theorem shiftedMoment_eq_conditional (W : Model Ω μ) (m : ℝ) (p : Ω × Ω) :
    shiftedMoment W m p = W.moment CappedColor.adjacency p * (conditionalCharge W p - m) := by
  rw [shiftedMoment_eq, charge_eq_conditionalCharge_mul]
  ring

variable [IsProbabilityMeasure μ]

/-- For the actual averaged optimizer, regular edge complementarity turns
the shifted sampled color into its deterministic shifted mean kernel. -/
theorem regular_shiftedColor_deterministic (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (m : ℝ) (hm : Variation.weightFirstVariation (chargeOperator W) =
      m • Variation.weightFirstVariation (adjacencyOperator W))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (hdet : ∀ p, ∀ᵐ c ∂W.kernel p,
      CappedColor.charge c = conditionalCharge W p * CappedColor.adjacency c) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p := by
  filter_upwards [regular_shiftedMoment_complementary W hW m hm hregular] with p hp
  have hM := shiftedMoment_eq_conditional W m p
  by_cases hz : conditionalCharge W p - m = 0
  · have heq : conditionalCharge W p = m := sub_eq_zero.mp hz
    filter_upwards [hdet p] with c hc
    rw [shiftedColor, hc, heq, hM, hz, mul_zero, sub_self]
  · rw [hM] at hp
    have hprod : ((1 - W.moment CappedColor.adjacency p) * W.moment CappedColor.adjacency p) *
        (conditionalCharge W p - m) = 0 := by
      convert hp using 1
      ring
    have hA := (mul_eq_zero.mp hprod).resolve_right hz
    rcases mul_eq_zero.mp hA with hone | hzero
    · have hAone : W.moment CappedColor.adjacency p = 1 := by linarith
      filter_upwards [hdet p, ae_adjacency_one_of_moment_one W p hAone] with c hc ha
      rw [shiftedColor, hc, ha, hM, hAone]
      ring
    · filter_upwards [hdet p, ae_adjacency_zero_of_moment_zero W p hzero] with c hc ha
      rw [shiftedColor, hc, ha, hM, hzero]
      ring

/-- The actual regular shifted mean is bounded in `[0,4]`, using the
multiplier bounds obtained from actual deletion and insertion. -/
theorem regular_shiftedMoment_mem (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (m : ℝ) (hm : Variation.weightFirstVariation (chargeOperator W) =
      m • Variation.weightFirstVariation (adjacencyOperator W))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (hd0 : 0 < density W) (hdhalf : density W < 1 / 2) :
    ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Set.Icc 0 4 := by
  have hmlo := (regular_multiplier_bounds W hW m hm hregular hd0 hdhalf).1
  filter_upwards [regular_shiftedMoment_nonnegative W hW m hm hregular] with p hp
  refine ⟨hp, ?_⟩
  rw [shiftedMoment_eq]
  have ha := adjacency_moment_mem W p
  have hy := charge_moment_le_adjacency W p
  have hprod := mul_nonneg (by linarith : 0 ≤ m + 3) ha.1
  nlinarith [ha.2]

end Erdos1017.CappedModel
