module

public import Erdos1017.Models.Capped.CappedStrictEdit

/-!
# Strict binary support of capped kernels

The maximizing comparison rules out adjacency mass on the zero shifted set
(`zeroShiftSet`) whenever a bounded positive transverse direction exists, so
nonnegative complementary capped kernels have strict binary support almost
everywhere, with either transverse sign allowed under stationary rows.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem shiftedOperator_congr (W V : Model Ω μ) (m : ℝ)
    (hM : ∀ p, shiftedMoment W m p = shiftedMoment V m p) : shiftedOperator W m = shiftedOperator V m := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  simp only [shiftedOperator, KernelOperator.operator_inner]
  apply integral_congr_ae
  filter_upwards with p
  rw [shiftedKernel, shiftedKernel, hM]

def zeroShiftSet (W : Model Ω μ) (m : ℝ) : Set (Ω × Ω) := {p | shiftedMoment W m p = 0}

omit [IsProbabilityMeasure μ] in
theorem measurableSet_zeroShiftSet (W : Model Ω μ) (m : ℝ) : MeasurableSet (zeroShiftSet W m) :=
  measurableSet_eq_fun
    (W.stronglyMeasurable_moment (continuous_shiftedColor m).measurable.stronglyMeasurable).measurable
    measurable_const

omit [IsProbabilityMeasure μ] in
theorem zeroShiftSet_symm (W : Model Ω μ) (m : ℝ) :
    ∀ᵐ p ∂μ.prod μ, p.swap ∈ zeroShiftSet W m ↔ p ∈ zeroShiftSet W m := by
  filter_upwards [shiftedMoment_symm W m] with p hp
  change shiftedMoment W m p.swap = 0 ↔ shiftedMoment W m p = 0
  rw [hp]

theorem shiftedOperator_maskedThin_zero (W : Model Ω μ) (m : ℝ) (t : unitInterval) :
    shiftedOperator (maskedThin W t (zeroShiftSet W m) (measurableSet_zeroShiftSet W m)
      (zeroShiftSet_symm W m)) m = shiftedOperator W m := by
  apply shiftedOperator_congr
  intro p
  rw [shiftedMoment_maskedThin]
  split_ifs with hp
  · change shiftedMoment W m p = 0 at hp
    rw [hp, mul_zero]
  · rfl

/-- The actual maximizing comparison rules out any adjacency mass on the
zero shifted set whenever the stated bounded positive transverse direction
exists. -/
theorem adjacency_zero_on_zeroShiftSet (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (m : ℝ) (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (u : Variation.WeightDirections μ)
    (hu : 0 < Variation.weightFirstVariation (adjacencyOperator W) u)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u) :
    ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = 0 → W.moment CappedColor.adjacency p = 0 := by
  classical
  let s := zeroShiftSet W m
  have hs := measurableSet_zeroShiftSet W m
  have hsym := zeroShiftSet_symm W m
  have hd := density_eq_of_shift_preserving_edit W hW (maskedThinningEdit W s hs hsym) m
    (shiftedOperator_maskedThin_zero W m) hfirst u hu hq
  change density (maskedThin W 1 s hs hsym) = density W at hd
  have hA : Integrable (W.moment CappedColor.adjacency) (μ.prod μ) :=
    integrable_bounded_moment W _ CappedColor.continuous_adjacency.measurable.stronglyMeasurable
      1 (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2)
  have hpoint (p : Ω × Ω) : (maskedThin W 1 s hs hsym).moment CappedColor.adjacency p =
      W.moment CappedColor.adjacency p - s.indicator (W.moment CappedColor.adjacency) p := by
    rw [moment_maskedThin W 1 s hs hsym p _
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable CappedColor.adjacency_absent
      1 (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2)]
    by_cases hp : p ∈ s <;> simp [hp]
  have hzint : (∫ p, s.indicator (W.moment CappedColor.adjacency) p ∂μ.prod μ) = 0 := by
    unfold density at hd
    simp_rw [hpoint] at hd
    rw [integral_sub hA (hA.indicator hs)] at hd
    linarith
  have hnonneg (p : Ω × Ω) : 0 ≤ s.indicator (W.moment CappedColor.adjacency) p := by
    exact Set.indicator_nonneg (fun p _ => (adjacency_moment_mem W p).1) p
  have hz := (integral_eq_zero_iff_of_nonneg hnonneg (hA.indicator hs)).mp hzint
  filter_upwards [hz] with p hp
  intro hzero
  have hmem : p ∈ s := hzero
  simpa only [Set.indicator_of_mem hmem, Pi.zero_apply] using hp

/-- Nonnegative complementary capped kernels with the actual positive
transverse direction have strict binary support almost everywhere. -/
theorem adjacency_eq_positive_shift_indicator (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (m : ℝ) (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (u : Variation.WeightDirections μ)
    (hu : 0 < Variation.weightFirstVariation (adjacencyOperator W) u)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      (if 0 < shiftedMoment W m p then 1 else 0) := by
  classical
  filter_upwards [adjacency_zero_on_zeroShiftSet W hW m hfirst u hu hq, hnonneg, hcomp]
    with p hz hn hc
  by_cases hp : 0 < shiftedMoment W m p
  · rw [ite_eq_left hp]
    have h := (mul_eq_zero.mp hc).resolve_right hp.ne'
    linarith
  · rw [ite_eq_right hp]
    exact hz (le_antisymm (not_lt.mp hp) hn)

theorem shiftedFirstVariation_zero_of_stationary (W : Model Ω μ) (m ν : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν) :
    Variation.weightFirstVariation (shiftedOperator W m) = 0 := by
  apply (Variation.weightFirstVariation_eq_zero_iff _
    (KernelOperator.operator_range_bounded _ _ _ _ (Lp.const 2 μ (1 : ℝ)))).mpr
  exact ⟨ν, KernelOperator.constant_one_eigenvector_of_stationary _ _ _ _ ν hrow⟩

/-- The positive direction may have either transverse sign. Stationary
rows supply the zero shifted first variation, and changing the sign of the
direction preserves its positive shifted second variation. -/
theorem strict_support_of_stationary_positive_direction (W : Model Ω μ) {r : ℕ}
    (hW : IsMaximizer r W) (m ν : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hpositive : ∃ u : Variation.WeightDirections μ,
      Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0 ∧
        0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      (if 0 < shiftedMoment W m p then 1 else 0) := by
  have hfirst := shiftedFirstVariation_zero_of_stationary W m ν hrow
  obtain ⟨u, hu, hq⟩ := hpositive
  rcases lt_or_gt_of_ne hu with hu | hu
  · apply adjacency_eq_positive_shift_indicator W hW m hfirst (-u)
    · simpa only [map_neg] using neg_pos.mpr hu
    · simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hq
    · exact hnonneg
    · exact hcomp
  · exact adjacency_eq_positive_shift_indicator W hW m hfirst u hu hq hnonneg hcomp

end Erdos1017.CappedModel
