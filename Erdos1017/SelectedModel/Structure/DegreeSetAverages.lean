module

public import Erdos1017.SelectedModel.Structure.NormalizedSetL2

/-!
# Normalized set averages of bounded functions

Strict almost-everywhere bounds and almost-everywhere constants on a positive
measurable set transfer to the normalized `L²` average of that set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A strict almost-everywhere upper bound on a positive measurable set
gives the same strict bound for its actual normalized L² average. -/
theorem normalizedSetL2_inner_lt_of_ae_lt
    (s : Set Ω) (hs : MeasurableSet s) (hspos : 0 < μ s)
    (g : Lp ℝ 2 μ) (a : ℝ) (hg : ∀ᵐ x ∂μ.restrict s, g x < a) :
    ⟪g, normalizedSetL2 (μ := μ) s hs⟫ < a := by
  have hconst : Integrable (fun _ : Ω => a) (μ.restrict s) := integrable_const a
  have hgint : Integrable (fun x => g x) (μ.restrict s) :=
    ((Lp.memLp g).integrable (by norm_num)).integrableOn
  have hint : Integrable (fun x => a - g x) (μ.restrict s) := hconst.sub hgint
  have hnonneg : ∀ᵐ x ∂μ.restrict s, 0 ≤ a - g x :=
    hg.mono (fun _ hx => (sub_pos.mpr hx).le)
  have hpositive : 0 < ∫ x in s, a - g x ∂μ := by
    by_contra hnot
    have hzero : (∫ x in s, a - g x ∂μ) = 0 :=
      le_antisymm (le_of_not_gt hnot) (integral_nonneg_of_ae hnonneg)
    have hz := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
    obtain ⟨x, _, hx, hzx⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hspos.ne' (hg.and hz)
    exact (ne_of_gt (sub_pos.mpr hx)) hzx
  have hmass : 0 < μ.real s := ENNReal.toReal_pos hspos.ne' (measure_ne_top μ s)
  have hset : (∫ x in s, g x ∂μ) < a * μ.real s := by
    rw [integral_sub hconst hgint, setIntegral_const] at hpositive
    simp only [smul_eq_mul, mul_comm] at hpositive
    linarith
  calc
    ⟪g, normalizedSetL2 (μ := μ) s hs⟫ =
        (μ.real s)⁻¹ * ∫ x in s, g x ∂μ := by
      rw [real_inner_comm]
      exact normalizedSetL2_inner s hs g
    _ < (μ.real s)⁻¹ * (a * μ.real s) :=
      mul_lt_mul_of_pos_left hset (inv_pos.mpr hmass)
    _ = a := by field_simp

/-- An almost-everywhere constant on a positive measurable set has that
same normalized L² average. -/
theorem normalizedSetL2_inner_eq_of_ae_eq
    (s : Set Ω) (hs : MeasurableSet s) (hspos : 0 < μ s)
    (g : Lp ℝ 2 μ) (a : ℝ) (hg : ∀ᵐ x ∂μ.restrict s, g x = a) :
    ⟪g, normalizedSetL2 (μ := μ) s hs⟫ = a := by
  rw [real_inner_comm]
  exact normalizedSetL2_inner_of_constant s hs hspos g a hg

/-- A strict almost-everywhere lower bound on a positive measurable set
gives the same strict bound for its actual normalized L² average. -/
theorem normalizedSetL2_inner_gt_of_ae_gt
    (s : Set Ω) (hs : MeasurableSet s) (hspos : 0 < μ s)
    (g : Lp ℝ 2 μ) (a : ℝ) (hg : ∀ᵐ x ∂μ.restrict s, a < g x) :
    a < ⟪g, normalizedSetL2 (μ := μ) s hs⟫ := by
  have hneg : ∀ᵐ x ∂μ.restrict s, (-g) x < -a := by
    filter_upwards [hg, ae_restrict_of_ae (Lp.coeFn_neg g)] with x hx hcoe
    rw [hcoe]
    exact neg_lt_neg hx
  have hlt := normalizedSetL2_inner_lt_of_ae_lt s hs hspos (-g) (-a) hneg
  rw [inner_neg_left] at hlt
  linarith

end Erdos1017.KernelOperator
