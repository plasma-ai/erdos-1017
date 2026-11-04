module

public import Erdos1017.Models.Kernel.KernelCutOperator
public import Erdos1017.Models.Kernel.KernelSpectralPart

/-!
# Operator convergence from cut-norm convergence

The operator difference of two kernels obeys the cubic cut estimate for the
signed difference kernel, so rectangle cut convergence of uniformly bounded
symmetric kernels implies convergence of their integral operators in norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The actual operator difference obeys the cubic cut estimate for the
actual signed difference kernel. -/
theorem operator_sub_norm_cube_le_cutNorm
    (K L : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 < B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hL : AEStronglyMeasurable (fun z : Ω × Ω => L z.1 z.2) (μ.prod μ))
    (hKB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hLB : ∀ᵐ z ∂μ.prod μ, ‖L z.1 z.2‖ ≤ B)
    (hKsym : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (hLsym : ∀ᵐ z ∂μ.prod μ, L z.1 z.2 = L z.2 z.1) :
    ‖operator K hB0.le hK hKB - operator L hB0.le hL hLB‖ ^ 3 ≤
      4 * (B + B) ^ 2 * kernelCutNorm (μ := μ) (fun x y => K x y - L x y) := by
  have hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      K z.1 z.2 - L z.1 z.2 = K z.2 z.1 - L z.2 z.1 := by
    filter_upwards [hKsym, hLsym] with z hKz hLz
    rw [hKz, hLz]
  have h := operator_norm_cube_le_cutNorm (fun x y => K x y - L x y)
    (add_pos hB0 hB0) (hK.sub hL) (kernel_sub_bound hKB hLB) hsym
  rw [operator_sub K L hB0.le hB0.le hK hL hKB hLB] at h
  exact h

/-- Actual rectangle cut convergence of uniformly bounded symmetric kernels
implies convergence of the norm of their actual operator differences. -/
theorem tendsto_operator_norm_of_cutNorm
    (K : ℕ → Ω → Ω → ℝ) (L : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 < B)
    (hK : ∀ n, AEStronglyMeasurable (fun z : Ω × Ω => K n z.1 z.2) (μ.prod μ))
    (hL : AEStronglyMeasurable (fun z : Ω × Ω => L z.1 z.2) (μ.prod μ))
    (hKB : ∀ n, ∀ᵐ z ∂μ.prod μ, ‖K n z.1 z.2‖ ≤ B)
    (hLB : ∀ᵐ z ∂μ.prod μ, ‖L z.1 z.2‖ ≤ B)
    (hKsym : ∀ n, ∀ᵐ z ∂μ.prod μ, K n z.1 z.2 = K n z.2 z.1)
    (hLsym : ∀ᵐ z ∂μ.prod μ, L z.1 z.2 = L z.2 z.1)
    (hcut : Tendsto (fun n => kernelCutNorm (μ := μ) (fun x y => K n x y - L x y)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖operator (K n) hB0.le (hK n) (hKB n) - operator L hB0.le hL hLB‖)
      atTop (𝓝 0) := by
  have hscaled : Tendsto
      (fun n => 4 * (B + B) ^ 2 * kernelCutNorm (μ := μ) (fun x y => K n x y - L x y))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hcut
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le (norm_nonneg _))
  · intro a ha
    have hevent := hscaled.eventually (eventually_lt_nhds (pow_pos ha 3))
    filter_upwards [hevent] with n hn
    exact lt_of_pow_lt_pow_left₀ 3 ha.le
      ((operator_sub_norm_cube_le_cutNorm (K n) L hB0 (hK n) hL (hKB n) hLB (hKsym n) hLsym).trans_lt hn)

/-- The actual integral operators converge in their norm topology. -/
theorem tendsto_operator_of_cutNorm
    (K : ℕ → Ω → Ω → ℝ) (L : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 < B)
    (hK : ∀ n, AEStronglyMeasurable (fun z : Ω × Ω => K n z.1 z.2) (μ.prod μ))
    (hL : AEStronglyMeasurable (fun z : Ω × Ω => L z.1 z.2) (μ.prod μ))
    (hKB : ∀ n, ∀ᵐ z ∂μ.prod μ, ‖K n z.1 z.2‖ ≤ B)
    (hLB : ∀ᵐ z ∂μ.prod μ, ‖L z.1 z.2‖ ≤ B)
    (hKsym : ∀ n, ∀ᵐ z ∂μ.prod μ, K n z.1 z.2 = K n z.2 z.1)
    (hLsym : ∀ᵐ z ∂μ.prod μ, L z.1 z.2 = L z.2 z.1)
    (hcut : Tendsto (fun n => kernelCutNorm (μ := μ) (fun x y => K n x y - L x y)) atTop (𝓝 0)) :
    Tendsto (fun n => operator (K n) hB0.le (hK n) (hKB n)) atTop
      (𝓝 (operator L hB0.le hL hLB)) := by
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (tendsto_operator_norm_of_cutNorm K L hB0 hK hL hKB hLB hKsym hLsym hcut)

end Erdos1017.KernelOperator
