module

public import Erdos1017.Models.Kernel.KernelOperator
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Clipping of integrable real functions

Symmetric clipping at natural-number radius (`realClip`) preserves measurability
and integrability, is eventually the identity at every value, and its means and
bounded-degree pairings converge to those of the integrable input.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.KernelOperator

/-- Symmetric real clipping at the natural-number radius. -/
def realClip (n : ℕ) (a : ℝ) : ℝ := max (-(n : ℝ)) (min a n)

theorem realClip_norm_le (n : ℕ) (a : ℝ) : ‖realClip n a‖ ≤ n := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_right _ _)

theorem realClip_norm_le_self (n : ℕ) (a : ℝ) : ‖realClip n a‖ ≤ ‖a‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_le]
  constructor
  · exact (le_min (neg_abs_le a)
      (by linarith [abs_nonneg a, Nat.cast_nonneg (α := ℝ) n])).trans (le_max_right _ _)
  · exact max_le (by linarith [abs_nonneg a, Nat.cast_nonneg (α := ℝ) n])
      ((min_le_left _ _).trans (le_abs_self a))

/-- Every real value is eventually unchanged by the actual clips. -/
theorem realClip_eventually_eq (a : ℝ) : ∀ᶠ n : ℕ in atTop, realClip n a = a := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖a‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hbound : ‖a‖ ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have h := abs_le.mp (show |a| ≤ (n : ℝ) from hbound)
  simp only [realClip, min_eq_left h.2, max_eq_right h.1]

theorem realClip_tendsto (a : ℝ) : Tendsto (fun n => realClip n a) atTop (𝓝 a) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [realClip_eventually_eq a] with n hn
  exact hn.symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Clipping preserves actual AE strong measurability. -/
theorem realClip_aestronglyMeasurable (n : ℕ) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => realClip n (f x)) μ := by
  exact (continuous_const.max (continuous_id.min continuous_const)).comp_aestronglyMeasurable hf

theorem realClip_integrable (n : ℕ) {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => realClip n (f x)) μ :=
  hf.norm.mono' (realClip_aestronglyMeasurable n hf.aestronglyMeasurable)
    (Eventually.of_forall (fun x => realClip_norm_le_self n (f x)))

/-- The actual clipped means converge to the mean of the integrable input. -/
theorem integral_realClip_tendsto {f : Ω → ℝ} (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x, realClip n (f x) ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  exact tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => realClip_aestronglyMeasurable n hf.aestronglyMeasurable) hf.norm
    (fun n => Eventually.of_forall (fun x => realClip_norm_le_self n (f x)))
    (Eventually.of_forall (fun x => realClip_tendsto (f x)))

/-- A bounded physical degree row can be paired with every integrable input. -/
theorem integrable_bounded_mul {g f : Ω → ℝ} (hg : AEStronglyMeasurable g μ)
    {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (hf : Integrable f μ) :
    Integrable (fun x => g x * f x) μ := by
  apply (hf.norm.const_mul C).mono' (hg.mul hf.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

/-- Bounded-degree pairings converge along the actual clips. -/
theorem integral_mul_realClip_tendsto {g f : Ω → ℝ} (hg : AEStronglyMeasurable g μ)
    {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x, g x * realClip n (f x) ∂μ) atTop (𝓝 (∫ x, g x * f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖ * ‖f x‖)
    (fun n => hg.mul (realClip_aestronglyMeasurable n hf.aestronglyMeasurable))
    (integrable_bounded_mul hg.norm (hbound.mono (fun _ hx => by simpa using hx)) hf.norm)
  · intro n
    apply Eventually.of_forall
    intro x
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_left (realClip_norm_le_self n (f x)) (norm_nonneg _)
  · exact Eventually.of_forall (fun x => tendsto_const_nhds.mul (realClip_tendsto (f x)))

end Erdos1017.KernelOperator
