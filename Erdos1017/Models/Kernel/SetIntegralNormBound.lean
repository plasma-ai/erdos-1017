module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Essential bounds from set integrals

A uniform bound on every set integral of a function implies the corresponding
essential pointwise bound, using only countably many Hilbert tests and no
differentiation basis.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

/-- A uniform bound on every set integral implies the corresponding essential
pointwise bound. Countably many Hilbert tests suffice; no differentiation
basis on the underlying measure space is required. -/
theorem ae_norm_le_of_setIntegral_norm_le
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    {f : Ω → E} (hf : Integrable f μ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s, MeasurableSet s → ‖∫ x in s, f x ∂μ‖ ≤ C * μ.real s) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
  have hv (v : E) : ∀ᵐ x ∂μ, ⟪v, f x⟫ ≤ C * ‖v‖ := by
    apply ae_le_of_forall_setIntegral_le (hf.const_inner v) (integrable_const _)
    intro s hs _
    rw [integral_inner hf.integrableOn, setIntegral_const, smul_eq_mul]
    calc
      ⟪v, ∫ x in s, f x ∂μ⟫ ≤ ‖v‖ * ‖∫ x in s, f x ∂μ‖ := real_inner_le_norm _ _
      _ ≤ ‖v‖ * (C * μ.real s) := mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg _)
      _ = μ.real s * (C * ‖v‖) := by ring
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, ⟪denseSeq E n, f x⟫ ≤ C * ‖denseSeq E n‖ :=
    ae_all_iff.mpr (fun n => hv (denseSeq E n))
  filter_upwards [hall] with x hx
  have hevery (v : E) : ⟪v, f x⟫ ≤ C * ‖v‖ := by
    exact (denseRange_denseSeq E).induction_on v
      (isClosed_le (continuous_id.inner continuous_const) (continuous_const.mul continuous_norm)) hx
  have hself := hevery (f x)
  rw [real_inner_self_eq_norm_sq] at hself
  nlinarith [norm_nonneg (f x)]

end Erdos1017.KernelOperator
