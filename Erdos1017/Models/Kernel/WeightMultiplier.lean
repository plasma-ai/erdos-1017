module

public import Erdos1017.Models.Kernel.BoundedWeightSpace
public import Erdos1017.Models.Selection.QuadraticLagrange

/-!
# Multiplier from local maximality under vertex weights

The first and second variations of the unhalved pair integral under vertex
weighting are defined, with the exact expansion for the weight `1 + f`, and
local constrained maximality under bounded mean-zero vertex weights supplies the
regular-case multiplier and tangent quadratic bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace Erdos1017.Variation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A mean-zero bounded direction, regarded as its actual L² class. -/
def directionToL2 : WeightDirections μ →L[ℝ] Lp ℝ 2 μ :=
  boundedToL2.comp (WeightDirections μ).subtypeL

theorem direction_integral_zero (f : WeightDirections μ) :
    (∫ x, directionToL2 f x ∂μ) = 0 := by
  exact (boundedMean_eq_integral f.val).symm.trans f.property

/-- The linear change in the unhalved pair integral under vertex weighting. -/
def weightFirstVariation (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : WeightDirections μ →ₗ[ℝ] ℝ :=
  (2 : ℝ) • ((innerSL ℝ (T (Lp.const 2 μ (1 : ℝ)))).comp directionToL2).toLinearMap

/-- The quadratic pair integral of two bounded mean-zero directions. -/
def weightSecondVariation (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    LinearMap.BilinForm ℝ (WeightDirections μ) where
  toFun f :=
    { toFun := fun g => ⟪T (directionToL2 f), directionToL2 g⟫
      map_add' := by intro g h; simp [inner_add_right]
      map_smul' := by intro c g; simp [real_inner_smul_right] }
  map_add' := by intro f g; ext h; simp [inner_add_left]
  map_smul' := by intro c f; ext h; simp [real_inner_smul_left]

theorem weightSecondVariation_symm (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hsym : T.toLinearMap.IsSymmetric) (f g : WeightDirections μ) :
    weightSecondVariation T f g = weightSecondVariation T g f := by
  change ⟪T (directionToL2 f), directionToL2 g⟫ = ⟪T (directionToL2 g), directionToL2 f⟫
  exact (hsym _ _).trans (real_inner_comm _ _)

/-- The exact pair-integral expansion for the actual vertex weight `1 + f`. -/
theorem weighted_quadratic_expansion (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hsym : T.toLinearMap.IsSymmetric) (f : WeightDirections μ) :
    ⟪T (Lp.const 2 μ (1 : ℝ) + directionToL2 f), Lp.const 2 μ (1 : ℝ) + directionToL2 f⟫ =
      ⟪T (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ +
        weightFirstVariation T f + weightSecondVariation T f f := by
  have hs : ⟪T (directionToL2 f), Lp.const 2 μ (1 : ℝ)⟫ =
      ⟪T (Lp.const 2 μ (1 : ℝ)), directionToL2 f⟫ :=
    (hsym _ _).trans (real_inner_comm _ _)
  simp only [map_add, inner_add_left, inner_add_right, hs]
  change _ = _ + 2 * ⟪T (Lp.const 2 μ (1 : ℝ)), directionToL2 f⟫ +
    ⟪T (directionToL2 f), directionToL2 f⟫
  ring

/-- Local constrained maximality under actual bounded mean-zero vertex
weights supplies the regular-case multiplier and tangent quadratic bound.
No first-variation or second-variation conclusion is assumed. -/
theorem exists_multiplier_of_weight_local_max
    (A Y : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hA : A.toLinearMap.IsSymmetric) (hY : Y.toLinearMap.IsSymmetric)
    (hregular : weightFirstVariation A ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hmax : ∀ f : WeightDirections μ, ‖f‖ < ε →
      ⟪A (Lp.const 2 μ (1 : ℝ) + directionToL2 f), Lp.const 2 μ (1 : ℝ) + directionToL2 f⟫ =
        ⟪A (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ →
      ⟪Y (Lp.const 2 μ (1 : ℝ) + directionToL2 f), Lp.const 2 μ (1 : ℝ) + directionToL2 f⟫ ≤
        ⟪Y (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫) :
    ∃ m : ℝ, weightFirstVariation Y = m • weightFirstVariation A ∧
      (∀ f : WeightDirections μ, weightFirstVariation A f = 0 →
        ⟪(Y - m • A) (directionToL2 f), directionToL2 f⟫ ≤ 0) ∧
      ∀ f : WeightDirections μ, ‖f‖ < ε → ∀ᵐ x ∂μ, 0 ≤ 1 + directionToL2 f x := by
  obtain ⟨m, hm, hquad⟩ := exists_multiplier_of_quadratic_local_max
    (weightFirstVariation A) (weightFirstVariation Y)
    (weightSecondVariation A) (weightSecondVariation Y)
    (weightSecondVariation_symm A hA) (weightSecondVariation_symm Y hY)
    hregular ε hε (by
      intro f hf hconstraint
      have h := hmax f hf (by rw [weighted_quadratic_expansion A hA]; linarith)
      rw [weighted_quadratic_expansion Y hY] at h
      linarith)
  refine ⟨m, hm, ?_, ?_⟩
  · intro f hf
    have h := hquad f hf
    change ⟪Y (directionToL2 f), directionToL2 f⟫ - m * ⟪A (directionToL2 f), directionToL2 f⟫ ≤ 0 at h
    simpa only [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left] using h
  · intro f hf
    exact weight_nonnegative_of_norm_lt_one f.val (hf.trans_le hεone)

end Erdos1017.Variation
