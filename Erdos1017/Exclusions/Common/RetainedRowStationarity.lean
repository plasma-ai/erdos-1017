module

public import Erdos1017.Models.Selection.FullModelVariation
public import Erdos1017.Models.Capped.CappedShiftedSelection

/-!
# Stationarity from two retained degree values

Two retained positive sets with distinct degree values identify an optimum's own
multiplier and row constant, and the new optimum supplies its own regular
multiplier.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Two retained positive sets with distinct actual degree values identify
an optimum's own multiplier and row constant. The new optimum supplies
its own regular multiplier; no old stationarity is assigned to it. -/
theorem full_stationary_of_two_retained_degree_values
    (W : Model Ω μ) (hfull : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (U V : Set Ω) (hU : 0 < μ U) (hV : 0 < μ V)
    (gU gV m ν : ℝ) (hne : gU ≠ gV)
    (hrowsU : ∀ᵐ x ∂μ.restrict U,
      (∫ y, adjacencyKernel W x y ∂μ) = gU ∧ (∫ y, chargeKernel W x y ∂μ) = ν + m * gU)
    (hrowsV : ∀ᵐ x ∂μ.restrict V,
      (∫ y, adjacencyKernel W x y ∂μ) = gV ∧ (∫ y, chargeKernel W x y ∂μ) = ν + m * gV) :
    ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν := by
  have hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0 := by
    intro hz
    obtain ⟨b, hb⟩ := (Variation.kernel_weightFirstVariation_eq_zero_iff
      (adjacencyKernel W) (by norm_num) (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W)).mp hz
    obtain ⟨x, _, hx, hxU⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hU.ne'
      ((ae_restrict_of_ae hb).and hrowsU)
    obtain ⟨y, _, hy, hyV⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hV.ne'
      ((ae_restrict_of_ae hb).and hrowsV)
    exact hne (hxU.1.symm.trans (hx.trans (hy.symm.trans hyV.1)))
  obtain ⟨n, a, _, heigen, _, _⟩ := exists_full_regular_multiplier W hfull hopt hregular
  have hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W n x y ∂μ) = a := by
    apply KernelOperator.stationary_of_constant_one_eigenvector _ (by positivity)
      (shiftedKernel_measurable W n) (shiftedKernel_bound W n) a
    change shiftedOperator W n (Lp.const 2 μ (1 : ℝ)) = _
    rwa [shiftedOperator_eq]
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (adjacencyKernel_measurable W) 1 (adjacencyKernel_bound W)
  have hY : Integrable (fun p : Ω × Ω => chargeKernel W p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (chargeKernel_measurable W) 3 (chargeKernel_bound W)
  have hexpand : ∀ᵐ x ∂μ, (∫ y, chargeKernel W x y ∂μ) - n * (∫ y, adjacencyKernel W x y ∂μ) = a := by
    filter_upwards [hrow, hG.prod_right_ae, hY.prod_right_ae] with x hx hg hy
    have he : (fun y => shiftedKernel W n x y) =
        fun y => chargeKernel W x y - n * adjacencyKernel W x y := by
      funext y
      exact shiftedMoment_eq W n (x, y)
    rwa [he, integral_sub hy (hg.const_mul n), integral_const_mul] at hx
  obtain ⟨x, _, hx, hxU⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hU.ne'
    ((ae_restrict_of_ae hexpand).and hrowsU)
  obtain ⟨y, _, hy, hyV⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hV.ne'
    ((ae_restrict_of_ae hexpand).and hrowsV)
  rw [hxU.1, hxU.2] at hx
  rw [hyV.1, hyV.2] at hy
  have heq : (m - n) * (gU - gV) = 0 := by nlinarith
  have hnm : n = m := by
    have hmn := (mul_eq_zero.mp heq).resolve_right (sub_ne_zero.mpr hne)
    linarith
  have ha : a = ν := by rw [hnm] at hx; linarith
  simpa only [hnm, ha] using hrow

end Erdos1017.CappedModel
