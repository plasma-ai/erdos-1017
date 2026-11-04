module

public import Erdos1017.Models.Capped.CappedKernelOperator
public import Erdos1017.Models.Capped.CappedInsertionMoments
public import Erdos1017.Models.Capped.CappedConditionalCharge
public import Erdos1017.Models.Capped.CappedMaskedDeletion

/-!
# Affine edit families of capped models

An affine edit (`AffineEdit`) is a feasible edit family whose density and
objective moments vary affinely, with thinning, sprinkling, support insertion
and masked thinning as instances; affine kernel moments give affine bilinear
pair integrals and affine adjacency and charge operators.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An actual feasible edit family whose two relevant moments vary affinely.
The endpoint moments determine the increments; no abstract edit coefficient
or feasibility assumption replaces the concrete family constructors. -/
structure AffineEdit (W : Model Ω μ) where
  model : unitInterval → Model Ω μ
  feasible : ∀ r, Feasible r W → ∀ t, Feasible r (model t)
  adjacency : ∀ t p, (model t).moment CappedColor.adjacency p =
    W.moment CappedColor.adjacency p + (t : ℝ) *
      ((model 1).moment CappedColor.adjacency p - W.moment CappedColor.adjacency p)
  charge : ∀ t p, (model t).moment CappedColor.charge p =
    W.moment CappedColor.charge p + (t : ℝ) *
      ((model 1).moment CappedColor.charge p - W.moment CappedColor.charge p)

def thinningEdit (W : Model Ω μ) : AffineEdit W where
  model := thin W
  feasible := fun _ hW t => feasible_thin W hW t
  adjacency := by
    intro t p
    rw [moment_thin W t p _ CappedColor.continuous_adjacency.measurable.stronglyMeasurable
      CappedColor.adjacency_absent 1 (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2),
      moment_thin W 1 p _ CappedColor.continuous_adjacency.measurable.stronglyMeasurable
        CappedColor.adjacency_absent 1 (fun c => by
          rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
          exact (CappedColor.adjacency_mem c).2)]
    norm_num
    ring
  charge := by
    intro t p
    have hb (c : CappedColor) : ‖CappedColor.charge c‖ ≤ 3 := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1, (CappedColor.charge_mem c).2.trans (by norm_num)⟩
    rw [moment_thin W t p _ CappedColor.continuous_charge.measurable.stronglyMeasurable
      CappedColor.charge_absent 3 hb,
      moment_thin W 1 p _ CappedColor.continuous_charge.measurable.stronglyMeasurable
        CappedColor.charge_absent 3 hb]
    norm_num
    ring

def sprinklingEdit (W : Model Ω μ) : AffineEdit W where
  model := sprinkle W
  feasible := fun _ hW t => feasible_sprinkle W hW t
  adjacency := by
    intro t p
    rw [adjacency_moment_sprinkle, adjacency_moment_sprinkle]
    norm_num
    ring
  charge := by
    intro t p
    rw [charge_moment_sprinkle, charge_moment_sprinkle]
    norm_num
    ring

theorem presentFactor_affine (a : ℝ) (t : unitInterval) :
    presentFactor a t = 1 + (t : ℝ) * (presentFactor a 1 - 1) := by
  unfold presentFactor
  split_ifs with h
  · norm_num
    field_simp
  · simp

def supportInsertionEdit (W : Model Ω μ) : AffineEdit W where
  model := supportInsert W
  feasible := fun _ hW t => feasible_supportInsert W hW t
  adjacency := by
    intro t p
    rw [moment_supportInsert_of_absent_zero W t p _ CappedColor.adjacency_absent,
      moment_supportInsert_of_absent_zero W 1 p _ CappedColor.adjacency_absent, presentFactor_affine]
    ring
  charge := by
    intro t p
    rw [moment_supportInsert_of_absent_zero W t p _ CappedColor.charge_absent,
      moment_supportInsert_of_absent_zero W 1 p _ CappedColor.charge_absent, presentFactor_affine]
    ring

def maskedThinningEdit (W : Model Ω μ) (s : Set (Ω × Ω)) (hs : MeasurableSet s)
    (hsym : ∀ᵐ p ∂μ.prod μ, p.swap ∈ s ↔ p ∈ s) : AffineEdit W where
  model := fun t => maskedThin W t s hs hsym
  feasible := fun _ hW t => feasible_maskedThin W hW t s hs hsym
  adjacency := by
    intro t p
    exact moment_maskedThin_affine W t s hs hsym p _
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable CappedColor.adjacency_absent 1
      (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2)
  charge := by
    intro t p
    exact moment_maskedThin_affine W t s hs hsym p _
      CappedColor.continuous_charge.measurable.stronglyMeasurable CappedColor.charge_absent 3
      (fun c => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
          (CappedColor.charge_mem c).2.trans (by norm_num)⟩)

/-- Affine kernel moments give affine bilinear pair integrals under every
actual L² vertex weight. -/
theorem bilinear_pairIntegral_affine
    (K₀ K₁ Kt : Ω → Ω → ℝ) {B C : ℝ}
    (hK₀ : AEStronglyMeasurable (fun p : Ω × Ω => K₀ p.1 p.2) (μ.prod μ))
    (hK₁ : AEStronglyMeasurable (fun p : Ω × Ω => K₁ p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K₀ p.1 p.2‖ ≤ B)
    (hC : ∀ᵐ p ∂μ.prod μ, ‖K₁ p.1 p.2‖ ≤ C)
    (t : ℝ) (hKt : ∀ x y, Kt x y = K₀ x y + t * (K₁ x y - K₀ x y))
    (f g : Lp ℝ 2 μ) :
    (∫ p : Ω × Ω, Kt p.1 p.2 * f p.2 * g p.1 ∂μ.prod μ) =
      (∫ p : Ω × Ω, K₀ p.1 p.2 * f p.2 * g p.1 ∂μ.prod μ) +
        t * ((∫ p : Ω × Ω, K₁ p.1 p.2 * f p.2 * g p.1 ∂μ.prod μ) -
          ∫ p : Ω × Ω, K₀ p.1 p.2 * f p.2 * g p.1 ∂μ.prod μ) := by
  have h₀ := KernelOperator.integrable_bilinear hK₀ hB f g
  have h₁ := KernelOperator.integrable_bilinear hK₁ hC f g
  calc
    _ = ∫ p : Ω × Ω, K₀ p.1 p.2 * f p.2 * g p.1 +
        t * (K₁ p.1 p.2 * f p.2 * g p.1 - K₀ p.1 p.2 * f p.2 * g p.1) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hKt]
      ring
    _ = _ := by
      rw [integral_add (f := fun p : Ω × Ω => K₀ p.1 p.2 * f p.2 * g p.1)
        (g := fun p : Ω × Ω => t * (K₁ p.1 p.2 * f p.2 * g p.1 - K₀ p.1 p.2 * f p.2 * g p.1))
        h₀ ((h₁.sub h₀).const_mul t), integral_const_mul, integral_sub h₁ h₀]

theorem adjacencyOperator_affine (W : Model Ω μ) (E : AffineEdit W) (t : unitInterval) :
    adjacencyOperator (E.model t) = adjacencyOperator W +
      (t : ℝ) • (adjacencyOperator (E.model 1) - adjacencyOperator W) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  simp only [adjacencyOperator, add_apply, smul_apply,
    sub_apply, inner_add_left, inner_sub_left, real_inner_smul_left,
    KernelOperator.operator_inner]
  exact bilinear_pairIntegral_affine (adjacencyKernel W) (adjacencyKernel (E.model 1))
    (adjacencyKernel (E.model t)) (adjacencyKernel_measurable W) (adjacencyKernel_measurable (E.model 1))
    (adjacencyKernel_bound W) (adjacencyKernel_bound (E.model 1)) t (fun x y => E.adjacency t (x, y)) f g

theorem chargeOperator_affine (W : Model Ω μ) (E : AffineEdit W) (t : unitInterval) :
    chargeOperator (E.model t) = chargeOperator W +
      (t : ℝ) • (chargeOperator (E.model 1) - chargeOperator W) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  simp only [chargeOperator, add_apply, smul_apply,
    sub_apply, inner_add_left, inner_sub_left, real_inner_smul_left,
    KernelOperator.operator_inner]
  exact bilinear_pairIntegral_affine (chargeKernel W) (chargeKernel (E.model 1))
    (chargeKernel (E.model t)) (chargeKernel_measurable W) (chargeKernel_measurable (E.model 1))
    (chargeKernel_bound W) (chargeKernel_bound (E.model 1)) t (fun x y => E.charge t (x, y)) f g

end Erdos1017.CappedModel
