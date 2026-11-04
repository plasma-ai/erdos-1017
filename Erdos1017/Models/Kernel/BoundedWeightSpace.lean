module

public import Erdos1017.Models.Kernel.StationaryKernel
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Bounded functions inside L²

Essentially bounded functions include into L² on a probability space
(`boundedToL2`) with a norm bound, their mean is a continuous linear functional
(`boundedMean`), and the weight directions (`WeightDirections`) are mean-zero
bounded changes of vertex weight whose small norm keeps weights nonnegative.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace Erdos1017.Variation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual inclusion of essentially bounded functions into L² on a
probability space, preserving their almost-everywhere function classes. -/
def boundedToL2Linear : Lp ℝ ∞ μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := ⟨f.val, Lp.antitone (by simp : (2 : ENNReal) ≤ ∞) f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsProbabilityMeasure μ] in
theorem bounded_ae_norm_le (f : Lp ℝ ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  have h := ae_le_lpNorm_exponent_top (Lp.memLp f)
  simpa only [← toReal_eLpNorm, Lp.norm_def] using h

theorem boundedToL2_norm_le (f : Lp ℝ ∞ μ) : ‖boundedToL2Linear f‖ ≤ ‖f‖ := by
  have h := Lp.norm_le_of_ae_bound (f := boundedToL2Linear f) (norm_nonneg f)
    (bounded_ae_norm_le f)
  simpa [measureUnivNNReal] using h

def boundedToL2 : Lp ℝ ∞ μ →L[ℝ] Lp ℝ 2 μ :=
  boundedToL2Linear.mkContinuous 1 (fun f => by simpa using boundedToL2_norm_le f)

/-- The mean of an essentially bounded function, expressed as a continuous
linear functional through its actual L² inclusion. -/
def boundedMean : Lp ℝ ∞ μ →L[ℝ] ℝ :=
  (innerSL ℝ (Lp.const 2 μ (1 : ℝ))).comp boundedToL2

theorem boundedMean_eq_integral (f : Lp ℝ ∞ μ) : boundedMean f = ∫ x, f x ∂μ := by
  exact KernelOperator.inner_constant_one (boundedToL2 f)

/-- Mean-zero bounded changes of vertex weight. -/
def WeightDirections (μ : Measure Ω) [IsProbabilityMeasure μ] :=
  (boundedMean (μ := μ)).ker

omit [IsProbabilityMeasure μ] in
theorem weight_nonnegative_of_norm_lt_one (f : Lp ℝ ∞ μ) (hf : ‖f‖ < 1) :
    ∀ᵐ x ∂μ, 0 ≤ 1 + f x := by
  filter_upwards [bounded_ae_norm_le f] with x hx
  have h := neg_abs_le (f x)
  rw [Real.norm_eq_abs] at hx
  linarith

end Erdos1017.Variation
