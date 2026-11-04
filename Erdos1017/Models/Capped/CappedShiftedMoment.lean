module

public import Erdos1017.Models.Capped.CappedEditMultiplier

/-!
# Shifted colors and shifted moments

The shifted color (`shiftedColor`) and its conditional mean (`shiftedMoment`)
are continuous, symmetric and integrable, and the objective-over-density edit
gain is half the integral of the shifted mean-kernel increment
(`shifted_gain_eq_integral`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def shiftedColor (m : ℝ) (c : CappedColor) : ℝ :=
  CappedColor.charge c - m * CappedColor.adjacency c

theorem continuous_shiftedColor (m : ℝ) : Continuous (shiftedColor m) := by
  unfold shiftedColor
  fun_prop

@[simp] theorem shiftedColor_absent (m : ℝ) : shiftedColor m CappedColor.absent = 0 := by
  simp [shiftedColor]

theorem shiftedColor_norm_le (m : ℝ) (c : CappedColor) : ‖shiftedColor m c‖ ≤ 3 + ‖m‖ := by
  have hy : ‖CappedColor.charge c‖ ≤ 3 := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(CappedColor.charge_mem c).1, (CappedColor.charge_mem c).2.trans (by norm_num)⟩
  have ha : ‖CappedColor.adjacency c‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
    exact (CappedColor.adjacency_mem c).2
  exact (norm_sub_le _ _).trans (by
    rw [norm_mul]
    nlinarith [norm_nonneg m])

def shiftedMoment (W : Model Ω μ) (m : ℝ) : Ω × Ω → ℝ := W.moment (shiftedColor m)

theorem shiftedMoment_eq (W : Model Ω μ) (m : ℝ) (p : Ω × Ω) :
    shiftedMoment W m p = W.moment CappedColor.charge p - m * W.moment CappedColor.adjacency p := by
  unfold shiftedMoment DecoratedKernel.moment shiftedColor
  rw [integral_sub (f := CappedColor.charge) (g := fun c => m * CappedColor.adjacency c)
    (integrable_color_charge W p) ((integrable_color_adjacency W p).const_mul m), integral_const_mul]

theorem shiftedMoment_symm (W : Model Ω μ) (m : ℝ) :
    ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p.swap = shiftedMoment W m p :=
  W.moment_symm (shiftedColor m)

theorem shiftedMoment_supportInsert (W : Model Ω μ) (m : ℝ) (t : unitInterval) (p : Ω × Ω) :
    shiftedMoment (supportInsert W t) m p =
      presentFactor (W.moment CappedColor.adjacency p) t * shiftedMoment W m p :=
  moment_supportInsert_of_absent_zero W t p _ (shiftedColor_absent m)

open scoped Classical in
theorem shiftedMoment_maskedThin (W : Model Ω μ) (m : ℝ) (t : unitInterval) (s : Set (Ω × Ω))
    (hs : MeasurableSet s) (hsym : ∀ᵐ p ∂μ.prod μ, p.swap ∈ s ↔ p ∈ s) (p : Ω × Ω) :
    shiftedMoment (maskedThin W t s hs hsym) m p =
      if p ∈ s then (1 - (t : ℝ)) * shiftedMoment W m p else shiftedMoment W m p :=
  moment_maskedThin W t s hs hsym p _ (continuous_shiftedColor m).measurable.stronglyMeasurable
    (shiftedColor_absent m) (3 + ‖m‖) (shiftedColor_norm_le m)

variable [IsProbabilityMeasure μ]

theorem integrable_shiftedMoment (W : Model Ω μ) (m : ℝ) :
    Integrable (shiftedMoment W m) (μ.prod μ) :=
  integrable_bounded_moment W _ (continuous_shiftedColor m).measurable.stronglyMeasurable
    (3 + ‖m‖) (shiftedColor_norm_le m)

theorem integral_shiftedMoment (W : Model Ω μ) (m : ℝ) :
    (∫ p, shiftedMoment W m p ∂μ.prod μ) = 2 * (objective W - m * density W) := by
  have hy := integrable_bounded_moment W CappedColor.charge
    CappedColor.continuous_charge.measurable.stronglyMeasurable 3 (fun c => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1, (CappedColor.charge_mem c).2.trans (by norm_num)⟩)
  have ha := integrable_bounded_moment W CappedColor.adjacency
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)
  simp_rw [shiftedMoment_eq]
  rw [integral_sub (f := W.moment CappedColor.charge)
    (g := fun p => m * W.moment CappedColor.adjacency p) hy (ha.const_mul m), integral_const_mul]
  unfold objective density
  ring

/-- The actual objective/density edit gain is half the integral of its
actual shifted mean-kernel increment. -/
theorem shifted_gain_eq_integral (W V : Model Ω μ) (m : ℝ) :
    objective V - objective W - m * (density V - density W) =
      (∫ p, shiftedMoment V m p - shiftedMoment W m p ∂μ.prod μ) / 2 := by
  rw [integral_sub (integrable_shiftedMoment V m) (integrable_shiftedMoment W m),
    integral_shiftedMoment, integral_shiftedMoment]
  ring

end Erdos1017.CappedModel
