module

public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteClassMasses
public import Erdos1017.SelectedModel.Flows.FullMissingFlowEndpoints
public import Erdos1017.SelectedModel.Structure.IntegrableRelativeWeight

/-!
# Class masses along a flow

Every original measurable cell has its exact receipt-minus-supply mass at each
affine flow time, class receipts and supplies over the independent classes are
summable, and the total endpoint independent-class mass is the sum of the
original class masses, receipts and supplies.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Function

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Actual real set mass under an integrable nonnegative density equals
its original-law set integral, including zero-density regions. -/
theorem weightedMeasure_real_set (w : Ω → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (A : Set Ω) (hA : MeasurableSet A) :
    (weightedMeasure (μ := μ) w).real A = ∫ x in A, w x ∂μ := by
  calc
    _ = ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂weightedMeasure (μ := μ) w := by
      rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
    _ = ∫ x, w x * A.indicator (fun _ => (1 : ℝ)) x ∂μ :=
      integral_weightedMeasure_real w hw.aestronglyMeasurable.aemeasurable hw0 _
    _ = ∫ x in A, w x ∂μ := by
      rw [← integral_indicator hA]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        by_cases hx : x ∈ A
        · simp only [indicator_of_mem hx, mul_one]
        · simp only [indicator_of_notMem hx, mul_zero])

variable [IsProbabilityMeasure μ]

/-- The exact original-cell mass at every actual affine interpolation time.
No original-cell mass-retention premise is assumed. -/
theorem integrableTilt_real_set (v : Ω → ℝ) (hv : Integrable v μ)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (A : Set Ω) (hA : MeasurableSet A) :
    (weightedMeasure (μ := μ) (integrableTiltWeight v t)).real A =
      μ.real A + t * ∫ x in A, v x ∂μ := by
  rw [weightedMeasure_real_set _ (integrableTiltWeight_integrable v hv t)
    (integrableTiltWeight_nonnegative v hbelow t ht) A hA]
  change (∫ x in A, 1 + t * v x ∂μ) = _
  rw [integral_add (integrable_const 1) (hv.restrict.const_mul t),
    integral_const_mul, setIntegral_const, smul_eq_mul, mul_one]

end Erdos1017.CappedModel

namespace Erdos1017.MissingFlow

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every original measurable cell has its exact receipt-minus-supply mass
at each actual affine flow time. Marginals need only be integrable. -/
theorem affine_real_set (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, supply μ q x ≤ 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (A : Set Ω) (hA : MeasurableSet A) :
    (weightedMeasure (μ := μ) (integrableTiltWeight (direction μ q) t)).real A =
      μ.real A + t * ((∫ x in A, receipt μ q x ∂μ) - ∫ x in A, supply μ q x ∂μ) := by
  rw [integrableTilt_real_set _ (integrable_direction hq)
    (direction_ge_neg_one hq0 hsupply) t ht A hA]
  simp only [direction]
  rw [integral_sub (integrable_marginals hq).1.restrict
    (integrable_marginals hq).2.restrict]

/-- The endpoint law has the exact original-cell mass increment. That it is a
probability measure is proved with the endpoint law's definition. -/
theorem endpoint_real_set (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, supply μ q x ≤ 1) (A : Set Ω) (hA : MeasurableSet A) :
    (missingFlowEndpointLaw μ q).real A =
      μ.real A + (∫ x in A, receipt μ q x ∂μ) - ∫ x in A, supply μ q x ∂μ := by
  have h := affine_real_set q hq hq0 hsupply 1 ⟨by norm_num, le_rfl⟩ A hA
  change (missingFlowEndpointLaw μ q).real A = _ at h
  simpa only [one_mul, add_sub_assoc] using h

/-- A genuinely removed original cell has zero mass under the actual
endpoint law, derived from its vanishing endpoint density on that cell. -/
theorem endpoint_real_set_eq_zero (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, supply μ q x ≤ 1) (A : Set Ω) (hA : MeasurableSet A)
    (hremoved : ∀ᵐ x ∂μ, x ∈ A → 1 + direction μ q x = 0) :
    (missingFlowEndpointLaw μ q).real A = 0 := by
  rw [missingFlowEndpointLaw, weightedMeasure_real_set _
    (integrableTiltWeight_integrable _ (integrable_direction hq) 1)
    (integrableTiltWeight_nonnegative _ (direction_ge_neg_one hq0 hsupply)
      1 ⟨by norm_num, le_rfl⟩) A hA]
  apply integral_eq_zero_of_ae
  apply (ae_restrict_iff' hA).mpr
  filter_upwards [hremoved] with x hx hmem
  simpa only [integrableTiltWeight, one_mul, Pi.zero_apply] using hx hmem

/-- A cell supplying no mass has its actual original mass plus its actual
receipt under the endpoint law. -/
theorem endpoint_real_set_eq_add_receipt (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, supply μ q x ≤ 1) (A : Set Ω) (hA : MeasurableSet A)
    (hsupply0 : ∀ᵐ x ∂μ, x ∈ A → supply μ q x = 0) :
    (missingFlowEndpointLaw μ q).real A = μ.real A + ∫ x in A, receipt μ q x ∂μ := by
  rw [endpoint_real_set q hq hq0 hsupply A hA]
  have hz : (∫ x in A, supply μ q x ∂μ) = 0 :=
    integral_eq_zero_of_ae ((ae_restrict_iff' hA).mpr hsupply0)
  rw [hz, sub_zero]

/-- Cells with no receipt or supply retain their actual original mass. -/
theorem endpoint_real_set_eq_original (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, supply μ q x ≤ 1) (A : Set Ω) (hA : MeasurableSet A)
    (hreceipt0 : ∀ᵐ x ∂μ, x ∈ A → receipt μ q x = 0)
    (hsupply0 : ∀ᵐ x ∂μ, x ∈ A → supply μ q x = 0) :
    (missingFlowEndpointLaw μ q).real A = μ.real A := by
  rw [endpoint_real_set_eq_add_receipt q hq hq0 hsupply A hA hsupply0]
  have hz : (∫ x in A, receipt μ q x ∂μ) = 0 :=
    integral_eq_zero_of_ae ((ae_restrict_iff' hA).mpr hreceipt0)
  rw [hz, add_zero]

variable {ι : Type*} [Countable ι]

local instance flowClassOptionMeasurable : MeasurableSpace (Option ι) := ⊤

/-- The same original class label is tracked at every affine flow time. -/
theorem classMass_affine (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, supply μ q x ≤ 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (labels : Ω → Option ι) (hlabels : Measurable labels) (i : ι) :
    MultipartiteClassMasses.classMass
      (weightedMeasure (μ := μ) (integrableTiltWeight (direction μ q) t)) labels i =
      MultipartiteClassMasses.classMass μ labels i +
        t * ((∫ x in labels ⁻¹' {some i}, receipt μ q x ∂μ) -
          ∫ x in labels ⁻¹' {some i}, supply μ q x ∂μ) :=
  affine_real_set q hq hq0 hsupply t ht _ (hlabels (measurableSet_singleton (some i)))

/-- Endpoint class mass is computed on the same original physical fiber. -/
theorem classMass_endpoint (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, supply μ q x ≤ 1)
    (labels : Ω → Option ι) (hlabels : Measurable labels) (i : ι) :
    MultipartiteClassMasses.classMass (missingFlowEndpointLaw μ q) labels i =
      MultipartiteClassMasses.classMass μ labels i +
        (∫ x in labels ⁻¹' {some i}, receipt μ q x ∂μ) -
          ∫ x in labels ⁻¹' {some i}, supply μ q x ∂μ :=
  endpoint_real_set q hq hq0 hsupply _ (hlabels (measurableSet_singleton (some i)))

/-- Actual class receipts are summable and sum to receipt on the original
independent-class region. -/
theorem hasSum_class_receipt (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (labels : Ω → Option ι) (hlabels : Measurable labels) :
    HasSum (fun i => ∫ x in labels ⁻¹' {some i}, receipt μ q x ∂μ)
      (∫ x in ⋃ i, labels ⁻¹' {some i}, receipt μ q x ∂μ) :=
  MultipartiteClassMasses.hasSum_integral_classes labels hlabels _ (integrable_marginals hq).1

/-- Actual supplies over the same original classes are also summable. -/
theorem hasSum_class_supply (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (labels : Ω → Option ι) (hlabels : Measurable labels) :
    HasSum (fun i => ∫ x in labels ⁻¹' {some i}, supply μ q x ∂μ)
      (∫ x in ⋃ i, labels ⁻¹' {some i}, supply μ q x ∂μ) :=
  MultipartiteClassMasses.hasSum_integral_classes labels hlabels _ (integrable_marginals hq).2

/-- Class receipt cannot exceed the entire actual original flow mass. -/
theorem tsum_class_receipt_le_flow_mass (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (labels : Ω → Option ι) (hlabels : Measurable labels) :
    (∑' i, ∫ x in labels ⁻¹' {some i}, receipt μ q x ∂μ) ≤ ∫ p, q p ∂μ.prod μ := by
  rw [(hasSum_class_receipt q hq labels hlabels).tsum_eq]
  exact (setIntegral_le_integral (integrable_marginals hq).1
    (nonnegative_marginals hq0).1).trans_eq (integral_marginals hq).1

/-- The actual total endpoint independent-class mass has exactly the sum
of its original class masses, receipts and supplies. -/
theorem tsum_classMass_endpoint (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, supply μ q x ≤ 1)
    (labels : Ω → Option ι) (hlabels : Measurable labels) :
    (∑' i, MultipartiteClassMasses.classMass (missingFlowEndpointLaw μ q) labels i) =
      (∑' i, MultipartiteClassMasses.classMass μ labels i) +
        (∑' i, ∫ x in labels ⁻¹' {some i}, receipt μ q x ∂μ) -
          ∑' i, ∫ x in labels ⁻¹' {some i}, supply μ q x ∂μ := by
  have := missingFlowEndpoint_probability q hq hq0 hsupply
  calc
    _ = (missingFlowEndpointLaw μ q).real (⋃ i, labels ⁻¹' {some i}) :=
      MultipartiteClassMasses.tsum_classMass labels hlabels
    _ = μ.real (⋃ i, labels ⁻¹' {some i}) +
        (∫ x in ⋃ i, labels ⁻¹' {some i}, receipt μ q x ∂μ) -
          ∫ x in ⋃ i, labels ⁻¹' {some i}, supply μ q x ∂μ :=
      endpoint_real_set q hq hq0 hsupply _
        (MeasurableSet.iUnion (fun i => hlabels (measurableSet_singleton (some i))))
    _ = _ := by
      rw [← MultipartiteClassMasses.tsum_classMass labels hlabels,
        ← (hasSum_class_receipt q hq labels hlabels).tsum_eq,
        ← (hasSum_class_supply q hq labels hlabels).tsum_eq]

end Erdos1017.MissingFlow
