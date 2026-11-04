module

public import Erdos1017.Exclusions.Common.Flows.FiniteFlowEndpointRemainder
public import Erdos1017.Exclusions.Common.CappedFiniteDustAtomization
public import Erdos1017.Exclusions.Common.ControlledDiffuseAtomization

/-!
# Energy budget of finitely many diffuse redirects

Any selected subfamily of uniform source redirects is paid by one full-flow
energy, the current-law internal energies of finitely many disjoint recipients
are covered together with their retained-receipt errors, and the finite-bin
model comparison keeps the full endpoint square sum in the budget at the
original multiplier.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical Function

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- Any selected subfamily of actual uniform source redirects is paid by
one and the same full-flow energy. Unselected subflows are nonnegative. -/
theorem finite_selected_uniform_energy_credit (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) {n k : ℕ}
    (C P : Fin n → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hP : ∀ i, MeasurableSet (P i)) (hpos : ∀ i, 0 < μ.real (C i))
    (θ : Fin n → ℝ) (hPdis : Pairwise (Disjoint on P))
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (ht : S.IsFullForwardFlow (MissingFlow.finiteRedirect μ q C P θ))
    (e : Fin k → Fin n) (he : Function.Injective e)
    (hzero : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1 ∈ C (e i) → p.2 ∈ P (e i) →
      shiftedKernel W m p.1 p.2 = 0) :
    (∑ i, (θ (e i) * μ.real (P (e i))) ^ 2 *
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        ((C (e i)).indicator (fun _ => 1 / μ.real (C (e i))))) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.finiteRedirect μ q C P θ)) := by
  let u : Fin n → Ω × Ω → ℝ := fun i => MissingFlow.uniformSubflow μ (C i) (P i) (θ i)
  have hu (i : Fin n) := MissingFlow.integrable_uniformSubflow (μ := μ) (C i) (P i) (hC i) (hP i) (θ i)
  have hu0 (i : Fin n) (p : Ω × Ω) : 0 ≤ u i p :=
    MissingFlow.uniformSubflow_nonnegative _ _ _ (hθ i).1 p
  have hdom : ∀ᵐ p ∂μ.prod μ, (∑ i, u (e i) p) ≤ MissingFlow.finiteRedirect μ q C P θ p := by
    filter_upwards [MissingFlow.sum_uniformSubflow_le_finiteRedirect q hq.nonnegative C P θ hPdis hθ]
      with p hp
    apply le_trans _ hp
    exact Finset.sum_le_sum_of_injOn e he.injOn (Finset.subset_univ _)
      (fun _ _ => le_rfl) (fun a _ _ => hu0 a p)
  have hsum := hW.sum_subflow_energy_le hd hgap k (fun i => u (e i))
    (MissingFlow.finiteRedirect μ q C P θ) (fun i => hu (e i)) ht.integrable
    (fun i => Eventually.of_forall (hu0 (e i))) hdom ht.oriented_support
  have hB : ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel W m p.1 p.2‖ ≤ 4 := by
    filter_upwards [hW.moment_mem] with p hp
    change ‖shiftedMoment W m p‖ ≤ 4
    rw [Real.norm_of_nonneg hp.1]
    exact hp.2
  apply le_trans _ hsum
  apply Finset.sum_le_sum
  intro i _
  exact MissingFlow.uniformSubflow_energy_ge (shiftedKernel W m)
    (shiftedKernel_measurable W m) hB ((shiftedMoment_symm W m).mono (fun _ hp => hp.symm))
    (hW.moment_mem.mono (fun _ hp => hp.1))
    (C (e i)) (P (e i)) (hC (e i)) (hP (e i)) (hpos (e i)) (hzero i) (θ (e i))

/-- Current-law internal energies of finitely many disjoint recipients are
covered together by one full-flow energy plus their actual retained-receipt errors. -/
theorem finite_selected_endpoint_energy_bound (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) {n k : ℕ}
    (C P : Fin n → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hP : ∀ i, MeasurableSet (P i)) (hpos : ∀ i, 0 < μ.real (C i))
    (θ : Fin n → ℝ) (hPdis : Pairwise (Disjoint on P))
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (ht : S.IsFullForwardFlow (MissingFlow.finiteRedirect μ q C P θ))
    (e : Fin k → Fin n) (he : Function.Injective e)
    (hCdis : Pairwise (Disjoint on C)) (hCH : ∀ i, C (e i) ⊆ S.H)
    (hzero : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1 ∈ C (e i) → p.2 ∈ P (e i) →
      shiftedKernel W m p.1 p.2 = 0) :
    (∑ i, ∫ p : Ω × Ω in C (e i) ×ˢ C (e i), shiftedKernel W m p.1 p.2
      ∂(missingFlowEndpointLaw μ (MissingFlow.finiteRedirect μ q C P θ)).prod
        (missingFlowEndpointLaw μ (MissingFlow.finiteRedirect μ q C P θ))) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.finiteRedirect μ q C P θ)) +
      8 * ∑ i, (missingFlowEndpointLaw μ (MissingFlow.finiteRedirect μ q C P θ)).real (C (e i)) *
        (μ.real (C (e i)) + ∫ x in C (e i), MissingFlow.receipt μ q x ∂μ) := by
  have hcredit := hq.finite_selected_uniform_energy_credit hW hd hgap C P hC hP hpos θ
    hPdis hθ ht e he hzero
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    hq.finite_endpoint_energy_remainder_bound hW C P hC hP θ hPdis hθ ht (e i)
      (hpos (e i)) (hCH i) (fun j hji => hCdis hji.symm))
  have heq (i : Fin k) := ht.endpoint_internal_kernel_integral (shiftedKernel W m) (C (e i)) (hC (e i))
  simp only [Finset.sum_add_distrib] at hb
  have herror : (∑ i : Fin k,
      8 * (missingFlowEndpointLaw μ (MissingFlow.finiteRedirect μ q C P θ)).real (C (e i)) *
        (μ.real (C (e i)) + ∫ x in C (e i), MissingFlow.receipt μ q x ∂μ)) =
      8 * ∑ i : Fin k,
        (missingFlowEndpointLaw μ (MissingFlow.finiteRedirect μ q C P θ)).real (C (e i)) *
          (μ.real (C (e i)) + ∫ x in C (e i), MissingFlow.receipt μ q x ∂μ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [herror] at hb
  simp_rw [heq]
  linarith

/-- The actual current-law finite-bin model comparison preserves the full
endpoint square sum in the old-multiplier budget. No single-peak truncation
of that reserve is made. -/
theorem finite_dust_atomization_budget (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (n : ℕ) (C : Fin n → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hCpos : ∀ i, 0 < (missingFlowEndpointLaw μ q) (C i))
    (hdis : Pairwise (Disjoint on C)) (hCD : ∀ i, C i ⊆ S.D)
    (A : ℝ) (hclasses : ∀ j, S.forwardClassMass q j ≤ A)
    (hCA : ∀ i, (missingFlowEndpointLaw μ q).real (C i) ≤ A) :
    (2 * (c - m * d) + m) +
        KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) ≤
      2 * A ^ 2 + m * (∑' j, (S.forwardClassMass q j) ^ 2) +
        (∑ i, ∫ p : Ω × Ω in C i ×ˢ C i, shiftedKernel W m p.1 p.2
          ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q)) +
        m * ∑ i, ((missingFlowEndpointLaw μ q).real (C i)) ^ 2 := by
  let := hq.endpoint_probability
  let : NullSingletonClass (missingFlowEndpointLaw μ q) := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hcost := FiniteDustAtomization.objective_sub_sum_internal_le_sq hq.endpoint
    (hq.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by
      filter_upwards [hq.endpoint_collapsed_support hW hd hgap] with p hp
      split_ifs at hp ⊢ <;> exact hp) n C hC hCpos hdis
    (fun i => (hCD i).trans S.diffuse_subset_collapsed_dust) A hclasses hCA
  have heq : (∑ i, ∫ p : Ω × Ω in C i ×ˢ C i, chargeKernel hq.endpoint p.1 p.2
        ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q)) =
      (∑ i, ∫ p : Ω × Ω in C i ×ˢ C i, shiftedKernel W m p.1 p.2
        ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q)) +
      m * ∑ i, ((missingFlowEndpointLaw μ q).real (C i)) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact hq.endpoint_diffuse_internal_charge hW hd hgap (C i) (hC i) (hCD i)
  rw [heq] at hcost
  have hbudget := hq.endpoint_budget hW
  rw [hq.missing_density_eq_classMass_sq hW hd hgap] at hbudget
  nlinarith

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow
