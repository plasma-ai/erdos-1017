module

public import Erdos1017.SelectedModel.Structure.NormalizedSetL2

/-!
# Kernel energy of normalized set indicators

Normalized set indicators are nonnegative densities whose unhalved bilinear
energy is the rectangle integral divided by the two masses, zero for a zero
rectangle and strictly positive for a positive rectangle between positive sets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual normalized set indicator has its expected AE representative. -/
theorem normalizedSetL2_coe (s : Set Ω) (hs : MeasurableSet s) :
    (normalizedSetL2 (μ := μ) s hs : Ω → ℝ) =ᵐ[μ]
      fun x => (μ.real s)⁻¹ * s.indicator (fun _ => (1 : ℝ)) x := by
  filter_upwards [Lp.coeFn_smul (μ.real s)⁻¹
    (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)),
    show ⇑(indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)) =ᵐ[μ]
      s.indicator (fun _ => 1) from indicatorConstLp_coeFn] with x hx hi
  change ((μ.real s)⁻¹ • indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)) x = _
  simp only [hx, Pi.smul_apply, smul_eq_mul, hi]

/-- Normalized set indicators are actual nonnegative densities. -/
theorem normalizedSetL2_nonnegative (s : Set Ω) (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, 0 ≤ normalizedSetL2 (μ := μ) s hs x := by
  filter_upwards [normalizedSetL2_coe s hs] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs, measureReal_nonneg]

/-- The unhalved bilinear energy of normalized sets is the actual rectangle
integral divided by their two masses. The source set is the second coordinate. -/
theorem operator_inner_normalizedSetL2
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ⟪operator K hB0 hK hB (normalizedSetL2 t ht), normalizedSetL2 s hs⟫ =
      ((μ.real s)⁻¹ * (μ.real t)⁻¹) *
        ∫ p : Ω × Ω, K p.1 p.2 ∂(μ.restrict s).prod (μ.restrict t) := by
  rw [operator_inner, Measure.prod_restrict, ← integral_indicator (hs.prod ht),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (normalizedSetL2_coe s hs),
    Measure.quasiMeasurePreserving_snd.ae (normalizedSetL2_coe t ht)] with p hp hq
  rw [hp, hq]
  by_cases hps : p.1 ∈ s <;> by_cases hpt : p.2 ∈ t <;>
    simp [hps, hpt, mul_comm, mul_left_comm]

/-- A genuinely zero rectangle has zero normalized-set bilinear energy. -/
theorem operator_inner_normalizedSetL2_eq_zero
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hzero : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), K p.1 p.2 = 0) :
    ⟪operator K hB0 hK hB (normalizedSetL2 t ht), normalizedSetL2 s hs⟫ = 0 := by
  rw [operator_inner_normalizedSetL2, integral_congr_ae hzero, integral_zero, mul_zero]

/-- A strictly positive actual rectangle between two positive sets gives
strictly positive normalized-set energy, with no uniform lower margin. -/
theorem operator_inner_normalizedSetL2_pos
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hspos : 0 < μ s) (htpos : 0 < μ t)
    (hpos : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), 0 < K p.1 p.2) :
    0 < ⟪operator K hB0 hK hB (normalizedSetL2 t ht), normalizedSetL2 s hs⟫ := by
  have hle : (μ.restrict s).prod (μ.restrict t) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hi : Integrable (fun p : Ω × Ω => K p.1 p.2) ((μ.restrict s).prod (μ.restrict t)) :=
    ((integrable_const B).mono' hK hB).mono_measure hle
  have hn := hpos.mono (fun _ hp => hp.le)
  have hpositive : 0 < ∫ p : Ω × Ω, K p.1 p.2 ∂(μ.restrict s).prod (μ.restrict t) := by
    by_contra hnot
    have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
      (le_antisymm (le_of_not_gt hnot) (integral_nonneg_of_ae hn))
    obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hspos.ne'
      (Measure.ae_ae_of_ae_prod (hpos.and hz))
    obtain ⟨y, _, hy, hyzero⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae htpos.ne' hx
    exact (ne_of_gt hy) hyzero
  rw [operator_inner_normalizedSetL2]
  exact mul_pos (mul_pos (inv_pos.mpr (ENNReal.toReal_pos hspos.ne' (measure_ne_top μ s)))
    (inv_pos.mpr (ENNReal.toReal_pos htpos.ne' (measure_ne_top μ t)))) hpositive

end Erdos1017.KernelOperator
