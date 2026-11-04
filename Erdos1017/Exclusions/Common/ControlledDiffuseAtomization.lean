module

public import Erdos1017.Exclusions.Common.Flows.SelectedDiffuseRerouting
public import Erdos1017.Exclusions.Common.CappedDustAtomization

/-!
# Controlled atomization of the diffuse remainder

The diffuse remainder carries the collapsed dust label, its internal charge
under the endpoint law splits into the original shifted kernel and a multiplier
term, and atomization with the full-flow budget gives the controlled inequality
at every target mass of the common peak (`exists_controlled_diffuse_peak_atom`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The original diffuse remainder has the actual collapsed dust label,
pointwise on the original carrier. -/
theorem diffuse_subset_collapsed_dust (S : SelectedHighLowStructure W m) :
    S.D ⊆ S.collapsedPartLabel ⁻¹' {none} := by
  intro x hx
  apply (HalfGraphMultipartite.collapsedLabel_eq_none_iff S.ρ S.I x).mpr
  intro hi
  exact Set.disjoint_left.mp (S.diffuse_disjoint_fiber ⟨S.ρ x, hi⟩) hx rfl

namespace IsFullForwardFlow

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- Internal charge under the current endpoint law equals the internal
original shifted kernel plus the original multiplier times the actual
recipient square mass. The diffuse endpoint adjacency is derived as one. -/
theorem endpoint_diffuse_internal_charge (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (C : Set Ω) (hC : MeasurableSet C) (hCD : C ⊆ S.D) :
    (∫ p : Ω × Ω in C ×ˢ C, chargeKernel hq.endpoint p.1 p.2
      ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q)) =
      (∫ p : Ω × Ω in C ×ˢ C, shiftedKernel W m p.1 p.2
        ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q)) +
        m * ((missingFlowEndpointLaw μ q).real C) ^ 2 := by
  let := hq.endpoint_probability
  have hA : ∀ᵐ p ∂((missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q)).restrict (C ×ˢ C),
      adjacencyKernel hq.endpoint p.1 p.2 = 1 := by
    filter_upwards [ae_restrict_of_ae (hq.endpoint_collapsed_support hW hd hgap),
      ae_restrict_mem (hC.prod hC)] with p hp hx
    have hn : S.collapsedPartLabel p.1 = none := S.diffuse_subset_collapsed_dust (hCD hx.1)
    rw [ite_eq_left (Or.inr hn)] at hp
    exact hp
  have heq : ∀ᵐ p ∂((missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q)).restrict (C ×ˢ C),
      chargeKernel hq.endpoint p.1 p.2 = shiftedKernel W m p.1 p.2 + m := by
    filter_upwards [hA] with p hp
    have he := shiftedMoment_eq hq.endpoint m p
    change shiftedKernel W m p.1 p.2 =
      chargeKernel hq.endpoint p.1 p.2 - m * adjacencyKernel hq.endpoint p.1 p.2 at he
    rw [hp] at he
    linarith
  have hM : Integrable (fun p : Ω × Ω => shiftedKernel W m p.1 p.2)
      ((missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q)) :=
    integrable_bounded_moment hq.endpoint (shiftedColor m)
      (continuous_shiftedColor m).measurable.stronglyMeasurable (3 + ‖m‖) (shiftedColor_norm_le m)
  rw [integral_congr_ae heq, integral_add hM.restrict (integrable_const m),
    setIntegral_const, smul_eq_mul, measureReal_prod_prod]
  ring

/-- Actual current-law atomization and the original full-flow budget yield
the controlled inequality before the internal energy is cancelled. -/
theorem dust_atomization_budget_le (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (i : S.I) (A : ℝ) (hAi : S.forwardClassMass q i = A)
    (hclasses : ∀ j, S.forwardClassMass q j ≤ A)
    (C : Set Ω) (hC : MeasurableSet C) (hCD : C ⊆ S.D)
    (b : ℝ) (hb : 0 < b) (hmass : (missingFlowEndpointLaw μ q).real C = b) (hbA : b ≤ A) :
    (2 * (c - m * d) + m) +
        KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) ≤
      (2 + m) * A ^ 2 + m * b ^ 2 +
        ∫ p : Ω × Ω in C ×ˢ C, shiftedKernel W m p.1 p.2
          ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q) := by
  let := hq.endpoint_probability
  let : NullSingletonClass (missingFlowEndpointLaw μ q) := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hCpos : 0 < (missingFlowEndpointLaw μ q) C := by
    have hp : 0 < (missingFlowEndpointLaw μ q).real C := by rw [hmass]; exact hb
    exact ENNReal.toReal_pos_iff.mp hp |>.1
  have hcost := DustAtomization.objective_sub_internal_le_sq hq.endpoint (hq.endpoint_fullFeasible hW.full)
    S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by
      filter_upwards [hq.endpoint_collapsed_support hW hd hgap] with p hp
      split_ifs at hp ⊢ <;> exact hp) C hC hCpos
    (hCD.trans S.diffuse_subset_collapsed_dust) A hclasses (by rw [hmass]; exact hbA)
  have hmassProps := hq.classMass_properties
  have hsq : Summable (fun j => (S.forwardClassMass q j) ^ 2) :=
    hmassProps.2.1.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
      nlinarith [(hmassProps.1 j).1, (hmassProps.1 j).2])
  have hsingle := (hsq.le_tsum i (fun _ _ => sq_nonneg _)).trans_eq
    (hq.missing_density_eq_classMass_sq hW hd hgap).symm
  rw [hAi] at hsingle
  have hneg := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hmul := mul_le_mul_of_nonpos_left hsingle hneg.le
  have hcharge := hq.endpoint_diffuse_internal_charge hW hd hgap C hC hCD
  rw [hmass] at hcharge
  have hbudget := hq.endpoint_budget hW
  nlinarith

end IsFullForwardFlow

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The same original common peak satisfies the controlled diffuse
atomization inequality at every legal target mass. Actual finite incidence,
small recipients, full flows, energy credit, and current-law atomized-model
feasibility are all derived internally. No largest-original-atom premise is used. -/
theorem exists_controlled_diffuse_peak_atom (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      0 < μ.real {x | S.ρ x = i} ∧
      ((∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.H) ∨
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.N)) ∧
      (∀ (u : Ω × Ω → ℝ), S.IsFullForwardFlow u →
        0 < S.forwardClassMass u i ∧
        ForwardPeak.massPeak (S.forwardClassMass u) = S.forwardClassMass u i ∧
        ForwardPeak.IsSeparatedPeak (S.forwardClassMass u) (forwardPeakGap d c m) i) ∧
      (∀ k : S.I, k ≠ i → (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H) →
        μ.real {x | S.ρ x = k} + μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) ≤
          μ.real {x | S.ρ x = i} - forwardPeakGap d c m) ∧
      (∀ k : S.I, k ≠ i → (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.N) →
        μ.real {x | S.ρ x = k} ≤ μ.real {x | S.ρ x = i} - forwardPeakGap d c m) ∧
      ∀ b ∈ Ioc (0 : ℝ) (μ.real {x | S.ρ x = i}),
        0 < μ (S.D ∩ S.H ∩ {x | b < S.outsideSectionMass x}) →
          2 * (c - m * d) + m ≤
            (2 + m) * (μ.real {x | S.ρ x = i}) ^ 2 + m * b ^ 2 := by
  obtain ⟨hΔ, i, q, hq, havoid, hside, hmass, hpeak, havoided, hhigh, hneutral⟩ :=
    S.exists_common_forward_peak_atom hW hd hgap
  have hApos : 0 < μ.real {x | S.ρ x = i} := hmass ▸ (hpeak q hq).1
  refine ⟨hΔ, i, hApos, hside, hpeak, hhigh, hneutral, ?_⟩
  intro b hb hpositive
  apply le_of_forall_pos_le_add
  intro ε hε
  have hscale : 0 < 8 * b := mul_pos (by norm_num) hb.1
  obtain ⟨C, J, θ, hC, hJ, hCp, hCD, hCH, hJL, hJI, hzero, hsmall, hθ, hu, hCb, hkeep⟩ :=
    hq.exists_selected_small_diffuse_rerouting hW hd hgap b (ε / (8 * b)) hb.1
      (div_pos hε hscale) hpositive
  let u := fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p
  have hstill : ∀ᵐ p ∂μ.prod μ, u p ≠ 0 → S.ρ p.1 ≠ i := hkeep i havoid
  have hAi := (havoided u hu hstill).1
  have hclasses : ∀ j, S.forwardClassMass u j ≤ μ.real {x | S.ρ x = i} := by
    intro j
    by_cases hj : j = i
    · subst j
      exact hAi.le
    · have hsep := (hpeak u hu).2.2 j hj
      rw [hAi] at hsep
      linarith
  have hbudget := hu.dust_atomization_budget_le hW hd hgap i _ hAi hclasses
    C hC hCD b hb.1 hCb hb.2
  have herror := hq.diffuse_endpoint_energy_le_flow_energy_add_error hW hd hgap
    C J hC hJ hCp hCD hCH hJL hJI hzero θ ⟨hθ.1.le, hθ.2.le⟩ b hCb
  rw [hu.endpoint_internal_kernel_integral (shiftedKernel W m) C hC] at hbudget
  have hsmall' : 8 * b * (μ.real C + ∫ x in C, MissingFlow.receipt μ q x ∂μ) < ε := by
    have h := mul_lt_mul_of_pos_left hsmall hscale
    exact h.trans_eq (mul_div_cancel₀ ε hscale.ne')
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure
