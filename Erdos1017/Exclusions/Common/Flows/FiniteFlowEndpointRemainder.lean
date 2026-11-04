module

public import Erdos1017.Exclusions.Common.Flows.FullForwardFiniteRerouting

/-!
# Endpoint remainder of a finite rerouting

The remainder `finiteEndpointRemainder` is the original vertex mass plus
retained receipt in a recipient bin; on a disjoint bin the current endpoint law
is its uniform density plus this remainder, and its shifted energy is covered by
the uniform component up to eight times bin mass times the small-set error.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical Function

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The old vertex mass and all retained original receipt in a recipient
bin, measured against the original probability law. -/
def finiteEndpointRemainder {n : ℕ} (μ : Measure Ω) (q : Ω × Ω → ℝ)
    (C : Set Ω) (P : Fin n → Set Ω) (θ : Fin n → ℝ) : Ω → ℝ :=
  C.indicator (fun x => 1 + receipt μ (retainedFiniteSources q P θ) x)

theorem integrable_finiteEndpointRemainder {n : ℕ} (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (C : Set Ω) (P : Fin n → Set Ω)
    (hC : MeasurableSet C) (hP : ∀ i, MeasurableSet (P i)) (θ : Fin n → ℝ) :
    Integrable (finiteEndpointRemainder μ q C P θ) μ :=
  ((integrable_const 1).add
    (integrable_marginals (integrable_retainedFiniteSources q hq P hP θ)).1).indicator hC

theorem finiteEndpointRemainder_nonnegative {n : ℕ} (q : Ω × Ω → ℝ)
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (C : Set Ω) (P : Fin n → Set Ω)
    (θ : Fin n → ℝ) (hdis : Pairwise (Disjoint on P))
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂μ, 0 ≤ finiteEndpointRemainder μ q C P θ x := by
  have hret := (retainedFiniteSources_bounds q hq0 P θ hdis hθ).mono (fun _ hp => hp.1)
  filter_upwards [(nonnegative_marginals hret).1] with x hx
  by_cases hC : x ∈ C
  · rw [finiteEndpointRemainder, indicator_of_mem hC]
    exact add_nonneg zero_le_one hx
  · rw [finiteEndpointRemainder, indicator_of_notMem hC]

/-- Finite rerouting keeps only a fraction of old receipt, so its actual
remainder is bounded by the same small-set quantity used before rerouting. -/
theorem integral_finiteEndpointRemainder_le {n : ℕ} (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (C : Set Ω) (P : Fin n → Set Ω) (hC : MeasurableSet C)
    (hP : ∀ i, MeasurableSet (P i)) (θ : Fin n → ℝ)
    (hdis : Pairwise (Disjoint on P)) (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1) :
    (∫ x, finiteEndpointRemainder μ q C P θ x ∂μ) ≤
      μ.real C + ∫ x in C, receipt μ q x ∂μ := by
  have hle : ∀ᵐ x ∂μ, finiteEndpointRemainder μ q C P θ x ≤
      C.indicator (fun x => 1 + receipt μ q x) x := by
    filter_upwards [receipt_retainedFiniteSources_le q hq hq0 P hP θ hdis hθ] with x hx
    by_cases hCx : x ∈ C
    · simp only [finiteEndpointRemainder, indicator_of_mem hCx]
      linarith
    · simp only [finiteEndpointRemainder, indicator_of_notMem hCx, le_refl]
  have hb := integral_mono_ae (integrable_finiteEndpointRemainder q hq C P hC hP θ)
    (((integrable_const 1).add (integrable_marginals hq).1).indicator hC) hle
  rw [integral_indicator hC] at hb
  change (∫ x, finiteEndpointRemainder μ q C P θ x ∂μ) ≤
    (∫ x in C, 1 + receipt μ q x ∂μ) at hb
  rw [integral_add (integrable_const 1) (integrable_marginals hq).1.restrict,
    setIntegral_const, smul_eq_mul, mul_one] at hb
  exact hb

end Erdos1017.MissingFlow

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- On a recipient disjoint from all other recipients, the current endpoint
law has its assigned uniform original-law density plus actual retained receipt.
The supplied full-flow proof is obtained by `finiteRedirect` at applications. -/
theorem finite_endpoint_density_decomposition (hq : S.IsFullForwardFlow q) {n : ℕ}
    (C P : Fin n → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hP : ∀ i, MeasurableSet (P i)) (θ : Fin n → ℝ)
    (ht : S.IsFullForwardFlow (MissingFlow.finiteRedirect μ q C P θ))
    (i : Fin n) (hCH : C i ⊆ S.H) (hdis : ∀ j, j ≠ i → Disjoint (C i) (C j)) :
    (C i).indicator (integrableTiltWeight
      (MissingFlow.direction μ (MissingFlow.finiteRedirect μ q C P θ)) 1) =ᵐ[μ]
      fun x => (θ i * μ.real (P i)) * (C i).indicator (fun _ => 1 / μ.real (C i)) x +
        MissingFlow.finiteEndpointRemainder μ q (C i) P θ x := by
  filter_upwards [ht.supply, MissingFlow.receipt_finiteRedirect q hq.integrable C P hC hP θ]
    with x hs hrec
  by_cases hx : x ∈ C i
  · have hnL : x ∉ S.L := fun hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 (hCH hx) hL
    have hsum : (∑ j, (θ j * μ.real (P j)) *
        (C j).indicator (fun _ => 1 / μ.real (C j)) x) =
        (θ i * μ.real (P i)) * (1 / μ.real (C i)) := by
      rw [Finset.sum_eq_single i]
      · rw [indicator_of_mem hx]
      · intro j _ hji
        have hj : x ∉ C j := fun hj => Set.disjoint_left.mp (hdis j hji) hx hj
        simp only [indicator_of_notMem hj, mul_zero]
      · simp
    simp only [indicator_of_mem hx, integrableTiltWeight, one_mul,
      MissingFlow.direction, MissingFlow.finiteEndpointRemainder, hs,
      indicator_of_notMem hnL, sub_zero, hrec, hsum]
    ring
  · simp only [MissingFlow.finiteEndpointRemainder, indicator_of_notMem hx, mul_zero, add_zero]

/-- Integrating the actual per-bin density gives its exact current mass. -/
theorem finite_endpoint_mass_split (hq : S.IsFullForwardFlow q) {n : ℕ}
    (C P : Fin n → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hP : ∀ i, MeasurableSet (P i)) (θ : Fin n → ℝ)
    (ht : S.IsFullForwardFlow (MissingFlow.finiteRedirect μ q C P θ))
    (i : Fin n) (hpos : 0 < μ.real (C i)) (hCH : C i ⊆ S.H)
    (hdis : ∀ j, j ≠ i → Disjoint (C i) (C j)) :
    (missingFlowEndpointLaw μ (MissingFlow.finiteRedirect μ q C P θ)).real (C i) =
      θ i * μ.real (P i) + ∫ x, MissingFlow.finiteEndpointRemainder μ q (C i) P θ x ∂μ := by
  let v := MissingFlow.direction μ (MissingFlow.finiteRedirect μ q C P θ)
  have hv := MissingFlow.integrable_direction ht.integrable
  change (weightedMeasure (μ := μ) (integrableTiltWeight v 1)).real (C i) = _
  rw [weightedMeasure_real_set _ (integrableTiltWeight_integrable v hv 1)
    (integrableTiltWeight_nonnegative v
      (MissingFlow.direction_ge_neg_one ht.nonnegative ht.supply_le_one) 1 ⟨by norm_num, le_rfl⟩)
      (C i) (hC i), ← integral_indicator (hC i),
    integral_congr_ae (hq.finite_endpoint_density_decomposition C P hC hP θ ht i hCH hdis),
    integral_add (((integrable_const _).indicator (hC i)).const_mul _)
      (MissingFlow.integrable_finiteEndpointRemainder q hq.integrable (C i) P (hC i) hP θ),
    integral_const_mul, integral_indicator (hC i), setIntegral_const, smul_eq_mul,
    mul_one_div, div_self hpos.ne', mul_one]

/-- Actual shifted energy in a disjoint diffuse bin is covered by its
uniform component up to eight times bin mass times its old small-set error. -/
theorem finite_endpoint_energy_remainder_bound (hq : S.IsFullForwardFlow q) {n : ℕ}
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (C P : Fin n → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hP : ∀ i, MeasurableSet (P i)) (θ : Fin n → ℝ)
    (hPdis : Pairwise (Disjoint on P)) (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (ht : S.IsFullForwardFlow (MissingFlow.finiteRedirect μ q C P θ))
    (i : Fin n) (hpos : 0 < μ.real (C i)) (hCH : C i ⊆ S.H)
    (hdis : ∀ j, j ≠ i → Disjoint (C i) (C j)) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        ((C i).indicator (integrableTiltWeight
          (MissingFlow.direction μ (MissingFlow.finiteRedirect μ q C P θ)) 1)) ≤
      (θ i * μ.real (P i)) ^ 2 * KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        ((C i).indicator (fun _ => 1 / μ.real (C i))) +
      8 * (missingFlowEndpointLaw μ (MissingFlow.finiteRedirect μ q C P θ)).real (C i) *
        (μ.real (C i) + ∫ x in C i, MissingFlow.receipt μ q x ∂μ) := by
  let ρ := (C i).indicator (fun _ => 1 / μ.real (C i))
  let w := MissingFlow.finiteEndpointRemainder μ q (C i) P θ
  have hρ : Integrable ρ μ := (integrable_const _).indicator (hC i)
  have hρ0 : ∀ᵐ x ∂μ, 0 ≤ ρ x := Eventually.of_forall
    (fun x => indicator_nonneg (fun _ _ => by positivity) x)
  have hmean : (∫ x, ρ x ∂μ) = 1 := by
    rw [integral_indicator (hC i), setIntegral_const, smul_eq_mul, mul_one_div, div_self hpos.ne']
  have hw := MissingFlow.integrable_finiteEndpointRemainder q hq.integrable (C i) P (hC i) hP θ
  have hw0 := MissingFlow.finiteEndpointRemainder_nonnegative q hq.nonnegative (C i) P θ hPdis hθ
  have hB : ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel W m p.1 p.2‖ ≤ 4 := by
    filter_upwards [hW.moment_mem] with p hp
    change ‖shiftedMoment W m p‖ ≤ 4
    rw [Real.norm_of_nonneg hp.1]
    exact hp.2
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 :=
    (shiftedMoment_symm W m).mono (fun _ hp => hp.symm)
  have hb := KernelOperator.kernelEnergy_add_remainder_le (shiftedKernel W m)
    (by norm_num : (0 : ℝ) ≤ 4) (shiftedKernel_measurable W m) hB hsym ρ w hρ hw hρ0 hw0
    hmean (θ i * μ.real (P i)) (mul_nonneg (hθ i).1 measureReal_nonneg)
  rw [← hq.finite_endpoint_mass_split C P hC hP θ ht i hpos hCH hdis] at hb
  have hsmall := MissingFlow.integral_finiteEndpointRemainder_le q hq.integrable hq.nonnegative
    (C i) P (hC i) hP θ hPdis hθ
  have herror := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ 8 * (missingFlowEndpointLaw μ (MissingFlow.finiteRedirect μ q C P θ)).real (C i)
      by positivity)
  rw [KernelOperator.kernelEnergy_congr_ae (shiftedKernel W m)
    (hq.finite_endpoint_density_decomposition C P hC hP θ ht i hCH hdis)]
  dsimp only [ρ, w] at hb
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow
