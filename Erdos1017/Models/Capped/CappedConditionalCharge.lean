module

public import Erdos1017.Models.Capped.CappedSupportInsertion

/-!
# Conditional charge of present outcomes

The conditional charge (`conditionalCharge`) is the mean charge on present
outcomes, zero at zero presence; it is measurable, bounded and symmetric, and
same-support insertion has an exact linear charge increment expressed through
it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_color_charge (W : Model Ω μ) (p : Ω × Ω) :
    Integrable CappedColor.charge (W.kernel p) :=
  Integrable.of_bound CappedColor.continuous_charge.measurable.stronglyMeasurable.aestronglyMeasurable
    3 (Filter.Eventually.of_forall (fun c => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
        (CappedColor.charge_mem c).2.trans (by norm_num)⟩))

theorem neg_three_adjacency_le_charge (c : CappedColor) :
    -3 * CappedColor.adjacency c ≤ CappedColor.charge c := by
  change -3 * c.val.1 ≤ c.val.2
  rcases c.property with h | h
  · have h0 : c.val.1 = 0 := h.1
    have hy0 : c.val.2 = 0 := h.2
    simp [h0, hy0]
  · have h1 : c.val.1 = 1 := h.1
    simpa [h1] using h.2.1

theorem neg_three_adjacency_moment_le_charge (W : Model Ω μ) (p : Ω × Ω) :
    -3 * W.moment CappedColor.adjacency p ≤ W.moment CappedColor.charge p := by
  have h := integral_mono ((integrable_color_adjacency W p).const_mul (-3))
    (integrable_color_charge W p) neg_three_adjacency_le_charge
  rw [integral_const_mul] at h
  exact h

theorem charge_moment_of_adjacency_zero (W : Model Ω μ) (p : Ω × Ω)
    (hA : W.moment CappedColor.adjacency p = 0) : W.moment CappedColor.charge p = 0 := by
  have hlo := neg_three_adjacency_moment_le_charge W p
  have hhi := charge_moment_le_adjacency W p
  rw [hA] at hlo hhi
  linarith

/-- Conditional mean charge on present outcomes. At zero presence its
value is zero, using the real division convention. -/
def conditionalCharge (W : Model Ω μ) (p : Ω × Ω) : ℝ :=
  W.moment CappedColor.charge p / W.moment CappedColor.adjacency p

theorem measurable_conditionalCharge (W : Model Ω μ) : Measurable (conditionalCharge W) :=
  (W.stronglyMeasurable_moment CappedColor.continuous_charge.measurable.stronglyMeasurable).measurable.div
    (W.stronglyMeasurable_moment CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable

theorem conditionalCharge_mem (W : Model Ω μ) (p : Ω × Ω) :
    conditionalCharge W p ∈ Icc (-3) 1 := by
  by_cases hA : W.moment CappedColor.adjacency p = 0
  · simp [conditionalCharge, hA]
  · have hpos : 0 < W.moment CappedColor.adjacency p :=
      lt_of_le_of_ne (adjacency_moment_mem W p).1 (Ne.symm hA)
    exact ⟨(le_div_iff₀ hpos).mpr (neg_three_adjacency_moment_le_charge W p),
      (div_le_iff₀ hpos).mpr (by simpa using charge_moment_le_adjacency W p)⟩

theorem charge_eq_conditionalCharge_mul (W : Model Ω μ) (p : Ω × Ω) :
    W.moment CappedColor.charge p =
      conditionalCharge W p * W.moment CappedColor.adjacency p := by
  by_cases hA : W.moment CappedColor.adjacency p = 0
  · simp [hA, charge_moment_of_adjacency_zero W p hA]
  · exact (div_mul_cancel₀ _ hA).symm

theorem conditionalCharge_symm (W : Model Ω μ) :
    ∀ᵐ p ∂μ.prod μ, conditionalCharge W p.swap = conditionalCharge W p := by
  filter_upwards [W.moment_symm CappedColor.charge, W.moment_symm CappedColor.adjacency] with p hY hA
  simp only [conditionalCharge, hY, hA]

/-- Same-support insertion has an exact linear charge increment, expressed
using the bounded conditional mean rather than an unbounded ratio. -/
theorem charge_moment_supportInsert_linear (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (supportInsert W t).moment CappedColor.charge p = W.moment CappedColor.charge p +
      (t : ℝ) * (1 - W.moment CappedColor.adjacency p) * conditionalCharge W p := by
  rw [charge_moment_supportInsert]
  by_cases hA : 0 < W.moment CappedColor.adjacency p
  · simp only [presentFactor, hA, ↓reduceIte, conditionalCharge]
    field_simp
  · have hzero := le_antisymm (not_lt.mp hA) (adjacency_moment_mem W p).1
    simp [presentFactor, conditionalCharge, hzero]

end Erdos1017.CappedModel
