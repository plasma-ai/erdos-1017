module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Receipt, supply and direction of a product flow

A product flow density has receipt and supply marginals of equal mass; its
direction, receipt minus supply, preserves mass, is bounded below by minus one
when supply is dominated by the original measure, and has positive degree
pairing through strictly ordered degree pairs.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The first-coordinate receipt of an actual product flow density. -/
def receipt (μ : Measure Ω) (q : Ω × Ω → ℝ) (x : Ω) : ℝ :=
  ∫ y, q (x, y) ∂μ

/-- The second-coordinate supply of the same actual product flow density. -/
def supply (μ : Measure Ω) (q : Ω × Ω → ℝ) (y : Ω) : ℝ :=
  ∫ x, q (x, y) ∂μ

/-- Forward mass transport subtracts supply and adds receipt on the original law. -/
def direction (μ : Measure Ω) (q : Ω × Ω → ℝ) (x : Ω) : ℝ :=
  receipt μ q x - supply μ q x

/-- Both actual marginals of an integrable product density are integrable. -/
theorem integrable_marginals {q : Ω × Ω → ℝ} (hq : Integrable q (μ.prod μ)) :
    Integrable (receipt μ q) μ ∧ Integrable (supply μ q) μ :=
  ⟨hq.integral_prod_left, hq.integral_prod_right⟩

/-- A finite absolutely continuous flow has an actual L¹ direction. -/
theorem integrable_direction {q : Ω × Ω → ℝ} (hq : Integrable q (μ.prod μ)) :
    Integrable (direction μ q) μ :=
  (integrable_marginals hq).1.sub (integrable_marginals hq).2

/-- The two marginals have exactly the same original total mass. -/
theorem integral_marginals {q : Ω × Ω → ℝ} (hq : Integrable q (μ.prod μ)) :
    (∫ x, receipt μ q x ∂μ) = (∫ p, q p ∂μ.prod μ) ∧
      (∫ x, supply μ q x ∂μ) = (∫ p, q p ∂μ.prod μ) :=
  ⟨(integral_prod q hq).symm, (integral_prod_symm q hq).symm⟩

/-- Transport preserves total mass, even when a marginal density is unbounded. -/
theorem integral_direction {q : Ω × Ω → ℝ} (hq : Integrable q (μ.prod μ)) :
    (∫ x, direction μ q x ∂μ) = 0 := by
  change (∫ x, receipt μ q x - supply μ q x ∂μ) = 0
  rw [integral_sub (integrable_marginals hq).1 (integrable_marginals hq).2,
    (integral_marginals hq).1, (integral_marginals hq).2, sub_self]

/-- Nonnegative product densities give nonnegative actual marginal densities. -/
theorem nonnegative_marginals {q : Ω × Ω → ℝ}
    (hq : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) :
    (∀ᵐ x ∂μ, 0 ≤ receipt μ q x) ∧ (∀ᵐ x ∂μ, 0 ≤ supply μ q x) := by
  constructor
  · filter_upwards [Measure.ae_ae_of_ae_prod hq] with x hx
    exact integral_nonneg_of_ae hx
  · have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hq
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with x hx
    exact integral_nonneg_of_ae hx

/-- Supply dominated by the old measure makes the endpoint weight nonnegative. -/
theorem direction_ge_neg_one {q : Ω × Ω → ℝ}
    (hq : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, supply μ q x ≤ 1) :
    ∀ᵐ x ∂μ, -1 ≤ direction μ q x := by
  filter_upwards [(nonnegative_marginals hq).1, hsupply] with x hx hs
  dsimp only [direction]
  linarith

/-- The original degree pairing equals the actual transported degree difference. -/
theorem degree_pairing {q : Ω × Ω → ℝ} (hq : Integrable q (μ.prod μ))
    (g : Ω → ℝ) (hg : AEStronglyMeasurable g μ)
    {B : ℝ} (hgBound : ∀ᵐ x ∂μ, ‖g x‖ ≤ B) :
    (∫ x, g x * direction μ q x ∂μ) =
      ∫ p : Ω × Ω, (g p.1 - g p.2) * q p ∂μ.prod μ := by
  have hfirst : Integrable (fun p : Ω × Ω => g p.1 * q p) (μ.prod μ) :=
    hq.bdd_mul hg.comp_fst (Measure.quasiMeasurePreserving_fst.ae hgBound)
  have hsecond : Integrable (fun p : Ω × Ω => g p.2 * q p) (μ.prod μ) :=
    hq.bdd_mul hg.comp_snd (Measure.quasiMeasurePreserving_snd.ae hgBound)
  have hr : Integrable (fun x => g x * receipt μ q x) μ :=
    (integrable_marginals hq).1.bdd_mul hg hgBound
  have hs : Integrable (fun x => g x * supply μ q x) μ :=
    (integrable_marginals hq).2.bdd_mul hg hgBound
  have her : (∫ x, g x * receipt μ q x ∂μ) =
      ∫ p : Ω × Ω, g p.1 * q p ∂μ.prod μ := by
    rw [integral_prod _ hfirst]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => (integral_const_mul _ _).symm)
  have hes : (∫ x, g x * supply μ q x ∂μ) =
      ∫ p : Ω × Ω, g p.2 * q p ∂μ.prod μ := by
    rw [integral_prod_symm _ hsecond]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => (integral_const_mul _ _).symm)
  have heq : (fun x => g x * direction μ q x) =
      (fun x => g x * receipt μ q x - g x * supply μ q x) := by
    funext x
    exact mul_sub _ _ _
  rw [heq, integral_sub hr hs, her, hes, ← integral_sub hfirst hsecond]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => (sub_mul _ _ _).symm)

/-- Every nonzero flow through strictly ordered degree pairs has positive
original degree slope. No uniform positive degree gap is assumed. -/
theorem degree_pairing_pos {q : Ω × Ω → ℝ} (hq : Integrable q (μ.prod μ))
    (hqNonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hqMass : 0 < ∫ p, q p ∂μ.prod μ)
    (g : Ω → ℝ) (hg : AEStronglyMeasurable g μ)
    {B : ℝ} (hgBound : ∀ᵐ x ∂μ, ‖g x‖ ≤ B)
    (horder : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → g p.2 < g p.1) :
    0 < ∫ x, g x * direction μ q x ∂μ := by
  rw [degree_pairing hq g hg hgBound]
  have hi : Integrable (fun p : Ω × Ω => (g p.1 - g p.2) * q p) (μ.prod μ) :=
    hq.bdd_mul (hg.comp_fst.sub hg.comp_snd) (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgBound,
        Measure.quasiMeasurePreserving_snd.ae hgBound] with p hp hq
      exact (norm_sub_le _ _).trans (add_le_add hp hq))
  have hn : ∀ᵐ p ∂μ.prod μ, 0 ≤ (g p.1 - g p.2) * q p := by
    filter_upwards [hqNonneg, horder] with p hp ho
    by_cases hz : q p = 0
    · simp only [hz, mul_zero, le_refl]
    · exact mul_nonneg (sub_pos.mpr (ho hz)).le hp
  by_contra hnot
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
    (le_antisymm (le_of_not_gt hnot) (integral_nonneg_of_ae hn))
  have hqZero : q =ᵐ[μ.prod μ] 0 := by
    filter_upwards [hz, horder] with p hp ho
    by_contra hne
    exact (mul_ne_zero (sub_pos.mpr (ho hne)).ne' hne) hp
  have : (∫ p, q p ∂μ.prod μ) = 0 := by
    simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hqZero
  linarith

/-- Actual flow directions add almost everywhere by Fubini integrability. -/
theorem direction_add {q r : Ω × Ω → ℝ}
    (hq : Integrable q (μ.prod μ)) (hr : Integrable r (μ.prod μ)) :
    direction μ (q + r) =ᵐ[μ] direction μ q + direction μ r := by
  filter_upwards [hq.prod_right_ae, hr.prod_right_ae, hq.prod_left_ae, hr.prod_left_ae]
    with x hqx hrx hqy hry
  dsimp only [direction, receipt, supply, Pi.add_apply]
  rw [integral_add hqx hrx, integral_add hqy hry]
  ring

omit [IsFiniteMeasure μ] in
/-- Scaling a genuine product density scales its actual direction. -/
theorem direction_const_mul (q : Ω × Ω → ℝ) (a : ℝ) :
    direction μ (fun p => a * q p) = fun x => a * direction μ q x := by
  funext x
  dsimp only [direction, receipt, supply]
  rw [integral_const_mul, integral_const_mul]
  ring

end Erdos1017.MissingFlow
