module

public import Erdos1017.Models.Selection.FullModelEdits
public import Erdos1017.Models.Selection.QuadraticStrictEdit

/-!
# Strict support from a positive transverse direction

With a bounded positive transverse direction of positive shifted second
variation, a shift-preserving feasible edit cannot change density, no adjacency
mass lies on the zero shifted set, and nonnegative complementary capped kernels
have strict binary support almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A feasible affine edit preserving the actual shifted operator cannot
change density when an actual bounded transverse direction has positive
shifted second variation. The contradiction uses an exactly restored
feasible competitor. -/
theorem full_density_eq_of_shift_preserving_edit (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (E : AffineEdit W) (m : ℝ)
    (hE : ∀ t, shiftedOperator (E.model t) m = shiftedOperator W m)
    (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (u : Variation.WeightDirections μ)
    (hu : 0 < Variation.weightFirstVariation (adjacencyOperator W) u)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u) :
    density (E.model 1) = density W := by
  let T₀ := adjacencyOperator W
  let T₁ := adjacencyOperator (E.model 1)
  let one := Lp.const 2 μ (1 : ℝ)
  let a := ⟪T₁ one, one⟫ - ⟪T₀ one, one⟫
  let b := Variation.weightFirstVariation T₀ u
  let c := Variation.weightFirstVariation T₁ u - Variation.weightFirstVariation T₀ u
  let d := Variation.weightSecondVariation T₀ u u
  let e := Variation.weightSecondVariation T₁ u u - Variation.weightSecondVariation T₀ u u
  let q := Variation.weightSecondVariation (shiftedOperator W m) u u
  let ε := 1 / (‖u‖ + 1)
  have hε : 0 < ε := div_pos (by norm_num) (by positivity)
  have hεone : ε ≤ 1 := (div_le_one (by positivity : 0 < ‖u‖ + 1)).mpr (by linarith [norm_nonneg u])
  have hεeq : ε * (‖u‖ + 1) = 1 := div_mul_cancel₀ _ (by positivity : ‖u‖ + 1 ≠ 0)
  have hMsym : (shiftedOperator W m).toLinearMap.IsSymmetric := by
    apply KernelOperator.operator_symmetric _ _ _ _
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have ha : a = 0 := by
    apply Variation.edit_density_zero_of_positive_shift a b c d e q hu hq ε hε
    intro τ s hτ hτε hs hroot
    let t : unitInterval := ⟨τ, hτ, (hτε.trans_le hεone).le⟩
    have hnorm : ‖s • u‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hmul := mul_le_mul_of_nonneg_right hs.le (norm_nonneg u)
      nlinarith
    have hden := Variation.affine_weight_curve_expansion T₀ T₁
      (adjacencyOperator_symmetric W) (adjacencyOperator_symmetric (E.model 1)) u τ s
    have hden0 : ⟪adjacencyOperator (E.model t) (Variation.vertexWeight (s • u)),
        Variation.vertexWeight (s • u)⟫ = ⟪T₀ one, one⟫ := by
      rw [adjacencyOperator_affine]
      change ⟪(T₀ + τ • (T₁ - T₀)) (Variation.vertexWeight (s • u)),
        Variation.vertexWeight (s • u)⟫ = _
      change a * τ + (b + c * τ) * s + (d + e * τ) * s ^ 2 = 0 at hroot
      change _ = a * τ + (b + c * τ) * s + (d + e * τ) * s ^ 2 at hden
      linarith
    have hcomp := full_weighted_competitor_lipschitz W hopt (E.model t) (fullFeasible_affineEdit W hW E t) (s • u) hnorm
    rw [hden0] at hcomp
    simp only [T₀, one, sub_self, abs_zero, mul_zero] at hcomp
    have hshift : ⟪shiftedOperator W m (Variation.vertexWeight (s • u)),
        Variation.vertexWeight (s • u)⟫ - ⟪shiftedOperator W m one, one⟫ ≤ 0 := by
      have heq : ⟪shiftedOperator (E.model t) m (Variation.vertexWeight (s • u)),
          Variation.vertexWeight (s • u)⟫ - ⟪shiftedOperator W m one, one⟫ =
          (⟪chargeOperator (E.model t) (Variation.vertexWeight (s • u)),
            Variation.vertexWeight (s • u)⟫ - ⟪chargeOperator W one, one⟫) -
          m * (⟪adjacencyOperator (E.model t) (Variation.vertexWeight (s • u)),
            Variation.vertexWeight (s • u)⟫ - ⟪T₀ one, one⟫) := by
        simp only [shiftedOperator_eq, sub_apply, smul_apply, inner_sub_left, real_inner_smul_left]
        dsimp only [T₀]
        ring
      rw [hE t, hden0, sub_self, mul_zero, sub_zero] at heq
      exact heq.le.trans hcomp
    have hcost := Variation.weight_curve_expansion (shiftedOperator W m) hMsym u s
    rw [hfirst, LinearMap.zero_apply, zero_mul, add_zero] at hcost
    change _ = ⟪shiftedOperator W m one, one⟫ + q * s ^ 2 at hcost
    linarith
  change ⟪adjacencyOperator (E.model 1) (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ -
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ = 0 at ha
  rw [adjacency_constant_inner, adjacency_constant_inner] at ha
  linarith

/-- The actual maximizing comparison rules out any adjacency mass on the
zero shifted set whenever the stated bounded positive transverse direction
exists. -/
theorem full_adjacency_zero_on_zeroShiftSet (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m : ℝ) (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (u : Variation.WeightDirections μ)
    (hu : 0 < Variation.weightFirstVariation (adjacencyOperator W) u)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u) :
    ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = 0 → W.moment CappedColor.adjacency p = 0 := by
  classical
  let s := zeroShiftSet W m
  have hs := measurableSet_zeroShiftSet W m
  have hsym := zeroShiftSet_symm W m
  have hd := full_density_eq_of_shift_preserving_edit W hW hopt (maskedThinningEdit W s hs hsym) m
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
theorem full_adjacency_eq_positive_shift_indicator (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m : ℝ) (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (u : Variation.WeightDirections μ)
    (hu : 0 < Variation.weightFirstVariation (adjacencyOperator W) u)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      (if 0 < shiftedMoment W m p then 1 else 0) := by
  classical
  filter_upwards [full_adjacency_zero_on_zeroShiftSet W hW hopt m hfirst u hu hq, hnonneg, hcomp]
    with p hz hn hc
  by_cases hp : 0 < shiftedMoment W m p
  · rw [ite_eq_left hp]
    have h := (mul_eq_zero.mp hc).resolve_right hp.ne'
    linarith
  · rw [ite_eq_right hp]
    exact hz (le_antisymm (not_lt.mp hp) hn)

/-- The positive direction may have either transverse sign. Stationary
rows supply the zero shifted first variation, and changing the sign of the
direction preserves its positive shifted second variation. -/
theorem full_strict_support_of_stationary_positive_direction (W : Model Ω μ)
    (hW : FullFeasible W) (hopt : objective W = FractionalGraph.densityLimit (density W)) (m ν : ℝ)
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
  · apply full_adjacency_eq_positive_shift_indicator W hW hopt m hfirst (-u)
    · simpa only [map_neg] using neg_pos.mpr hu
    · simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hq
    · exact hnonneg
    · exact hcomp
  · exact full_adjacency_eq_positive_shift_indicator W hW hopt m hfirst u hu hq hnonneg hcomp

end Erdos1017.CappedModel
