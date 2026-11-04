module

public import Erdos1017.Exclusions.Common.Universal.UniversalCopyInequality
public import Erdos1017.Exclusions.Common.KernelCubicIntegration

/-!
# Positive body and missing body outside a universal atom

This module defines the positive charges outside the independent atom and the
missing-pair indicator on that body, and shows that universal rows bound the
signed missing-row integral by the positive-body composition and that the atom
accounts for exactly its own missing square.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Positive original charges outside the original independent atom. -/
def positiveBody (Y : Ω → Ω → ℝ) (I : Set Ω) (x y : Ω) : ℝ :=
  if x ∉ I ∧ y ∉ I then max (Y x y) 0 else 0

/-- The original missing-pair indicator restricted to the same outside body. -/
def missingBody (A : Ω → Ω → Bool) (I : Set Ω) (x y : Ω) : ℝ :=
  if x ∉ I ∧ y ∉ I ∧ A x y = false then 1 else 0

theorem measurable_positiveBody (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (I : Set Ω) (hI : MeasurableSet I) :
    Measurable (Function.uncurry (positiveBody Y I)) :=
  Measurable.ite ((hI.compl.preimage measurable_fst).inter
    (hI.compl.preimage measurable_snd)) (hY.max measurable_const) measurable_const

theorem measurable_missingBody (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (I : Set Ω) (hI : MeasurableSet I) :
    Measurable (Function.uncurry (missingBody A I)) :=
  Measurable.ite ((hI.compl.preimage measurable_fst).inter
    ((hI.compl.preimage measurable_snd).inter (hA (measurableSet_singleton false))))
    measurable_const measurable_const

omit [MeasurableSpace Ω] in
theorem positiveBody_mem (Y : Ω → Ω → ℝ) (I : Set Ω)
    (hY : ∀ x y, Y x y ≤ 1) (x y : Ω) : positiveBody Y I x y ∈ Icc (0 : ℝ) 1 := by
  unfold positiveBody
  split_ifs
  · exact ⟨le_max_right _ _, max_le (hY x y) zero_le_one⟩
  · exact ⟨le_rfl, zero_le_one⟩

omit [MeasurableSpace Ω] in
theorem positiveBody_symm (Y : Ω → Ω → ℝ) (I : Set Ω)
    (hsym : ∀ x y, Y x y = Y y x) (x y : Ω) :
    positiveBody Y I x y = positiveBody Y I y x := by
  simp only [positiveBody, hsym x y, and_comm]

omit [MeasurableSpace Ω] in
theorem missingBody_mem (A : Ω → Ω → Bool) (I : Set Ω) (x y : Ω) :
    missingBody A I x y ∈ Icc (0 : ℝ) 1 := by
  unfold missingBody
  split_ifs <;> constructor <;> norm_num

omit [MeasurableSpace Ω] in
theorem missingBody_positiveBody_mul (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I : Set Ω)
    (hzero : ∀ x y, A x y = false → Y x y = 0) (x y : Ω) :
    missingBody A I x y * positiveBody Y I x y = 0 := by
  by_cases h : x ∉ I ∧ y ∉ I ∧ A x y = false
  · simp [missingBody, positiveBody, h.1, h.2.1, h.2.2, hzero x y h.2.2]
  · simp [missingBody, h]

/-- Original universal rows make the signed missing-row integral no larger
than the actual positive-body composition. The exceptional set stays AE. -/
theorem missing_integral_le_body_composed (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (I : Set Ω) (hI : MeasurableSet I)
    (hYB : ∀ x y, ‖Y x y‖ ≤ 3) (hY1 : ∀ x y, Y x y ≤ 1)
    (hsym : ∀ x y, Y x y = Y y x) (x y : Ω) (hx : x ∉ I) (hy : y ∉ I)
    (huniversal : ∀ᵐ z ∂μ, z ∈ I → A x z = true) :
    (∫ z in missingSection A x, Y y z ∂μ) ≤
      KernelOperator.composedKernel (μ := μ) (missingBody A I) (positiveBody Y I) x y := by
  have hms := measurableSet_missingSection A hA x
  have hiY : Integrable (Y y) μ := Integrable.of_bound
    (hY.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 3
    (Eventually.of_forall (hYB y))
  have hiP : Integrable (fun z => missingBody A I x z * positiveBody Y I z y) μ :=
    Integrable.of_bound
      (((measurable_missingBody A hA I hI).comp
        (measurable_const.prodMk measurable_id)).mul
        ((measurable_positiveBody Y hY I hI).comp
          (measurable_id.prodMk measurable_const))).aestronglyMeasurable 1
      (Eventually.of_forall (fun z => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (missingBody_mem A I x z).1,
          abs_of_nonneg (positiveBody_mem Y I hY1 z y).1]
        exact (mul_le_mul (missingBody_mem A I x z).2 (positiveBody_mem Y I hY1 z y).2
          (positiveBody_mem Y I hY1 z y).1 zero_le_one).trans_eq (mul_one 1)))
  rw [← integral_indicator hms]
  apply integral_mono_ae (hiY.indicator hms) hiP
  filter_upwards [huniversal] with z hz
  by_cases ha : A x z = false
  · have hzI : z ∉ I := fun hi => by simpa [ha] using hz hi
    simp [missingSection, missingBody, positiveBody, hx, hzI, hy, ha, hsym z y]
  · simp [missingSection, missingBody, ha]

/-- A genuine universal independent atom accounts for exactly its own
missing square. The remaining missing-body square energy is original. -/
theorem missingBody_square_integral (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (I : Set Ω) (hI : MeasurableSet I)
    (huniversal : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → (A p.1 p.2 = true ↔ p.2 ∉ I))
    (hsym : ∀ x y, A x y = A y x) :
    (∫ p : Ω × Ω, (missingBody A I p.1 p.2) ^ 2 ∂μ.prod μ) =
      1 - (∫ p : Ω × Ω, (if A p.1 p.2 = true then (1 : ℝ) else 0) ∂μ.prod μ) -
        (μ.real I) ^ 2 := by
  have hrev := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    huniversal
  have he : ∀ᵐ p ∂μ.prod μ, (missingBody A I p.1 p.2) ^ 2 =
      1 - (if A p.1 p.2 = true then (1 : ℝ) else 0) -
        I.indicator (fun _ => (1 : ℝ)) p.1 * I.indicator (fun _ => (1 : ℝ)) p.2 := by
    filter_upwards [huniversal, hrev] with p hp hr
    change (p.2 ∈ I → (A p.2 p.1 = true ↔ p.1 ∉ I)) at hr
    rw [← hsym p.1 p.2] at hr
    by_cases hx : p.1 ∈ I <;> by_cases hy : p.2 ∈ I <;>
      cases ha : A p.1 p.2 <;> simp_all [missingBody]
  have hiA : Integrable (fun p : Ω × Ω => if A p.1 p.2 = true then (1 : ℝ) else 0)
      (μ.prod μ) := Integrable.of_bound
    (Measurable.ite (hA (measurableSet_singleton true)) measurable_const
      measurable_const).aestronglyMeasurable 1
    (Eventually.of_forall (fun p => by split_ifs <;> norm_num))
  have hiI : Integrable (I.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hI
  have hiII : Integrable (fun p : Ω × Ω => I.indicator (fun _ => (1 : ℝ)) p.1 *
      I.indicator (fun _ => (1 : ℝ)) p.2) (μ.prod μ) := hiI.mul_prod hiI
  have hi1 : Integrable (fun p : Ω × Ω => 1 -
      (if A p.1 p.2 = true then (1 : ℝ) else 0)) (μ.prod μ) :=
    (integrable_const 1).sub hiA
  rw [integral_congr_ae he, integral_sub hi1 hiII,
    integral_sub (integrable_const 1) hiA, integral_const, probReal_univ, smul_eq_mul,
    mul_one, integral_prod_mul, integral_indicator hI, setIntegral_const]
  simp only [smul_eq_mul, mul_one, pow_two]

end Erdos1017.IndependentAtomCopy
