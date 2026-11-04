module

public import Erdos1017.Exclusions.Common.Flows.FiniteDiffuseFlowBudget
public import Erdos1017.Exclusions.Common.SharpCounts.MultipartiteSharpCountCells

/-!
# Sharp budget for finite dust atomization

Finite atomization on the endpoint keeps its original peak and pays every old
and new class square through one sharp selector budget
(`finite_dust_atomization_sharp_budget`).
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

/-- Finite atomization on the actual endpoint retains its original peak
and pays every old and new class square through one sharp selector budget. -/
theorem finite_dust_atomization_sharp_budget (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (n : ℕ) (C : Fin n → Set Ω) (hC : ∀ j, MeasurableSet (C j))
    (hCpos : ∀ j, 0 < (missingFlowEndpointLaw μ q) (C j))
    (hdis : Pairwise (Disjoint on C)) (hCD : ∀ j, C j ⊆ S.D)
    (A : ℝ) (hclasses : ∀ j, S.forwardClassMass q j ≤ A)
    (hCA : ∀ j, (missingFlowEndpointLaw μ q).real (C j) ≤ A)
    (i : S.I) (hmain : S.forwardClassMass q i = A)
    (hA : A ∈ Icc (1 / 4 : ℝ) (1 / 3)) :
    let T := (1 - A) / A
    (2 * (c - m * d) + m) +
        KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) +
        (-m - 2 / 3) * ((∑' j, (S.forwardClassMass q j) ^ 2) +
          ∑ j, ((missingFlowEndpointLaw μ q).real (C j)) ^ 2) ≤
      2 * (A ^ 2 * (6 * T - T ^ 2) / 12) - (2 / 3) * A ^ 2 +
        ∑ j, ∫ p : Ω × Ω in C j ×ˢ C j, shiftedKernel W m p.1 p.2
          ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q) := by
  let := hq.endpoint_probability
  let : NullSingletonClass (missingFlowEndpointLaw μ q) := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  obtain ⟨V, labels, hV, hlabels, hOld, hNew, _, hVA, _, hVd, hVc⟩ :=
    FiniteDustAtomization.exists_model hq.endpoint (hq.endpoint_fullFeasible hW.full)
      S.collapsedPartLabel S.measurable_collapsedPartLabel
      (by
        filter_upwards [hq.endpoint_collapsed_support hW hd hgap] with p hp
        split_ifs at hp ⊢ <;> exact hp) n C hC hCpos hdis
      (fun j => (hCD j).trans S.diffuse_subset_collapsed_dust)
  have hmain' : MultipartiteClassMasses.classMass (missingFlowEndpointLaw μ q)
      labels (.inl i) = A := by
    simpa only [MultipartiteClassMasses.classMass, hOld, S.collapsedPartLabel_fiber,
      S.forwardClassMass_eq_fiber] using hmain
  have hparts : ∀ k, MultipartiteClassMasses.classMass (missingFlowEndpointLaw μ q)
      labels k ≤ MultipartiteClassMasses.classMass (missingFlowEndpointLaw μ q)
        labels (.inl i) := by
    intro k
    rw [hmain']
    cases k with
    | inl j => simpa only [MultipartiteClassMasses.classMass, hOld,
        S.collapsedPartLabel_fiber, S.forwardClassMass_eq_fiber] using hclasses j
    | inr j => simpa only [MultipartiteClassMasses.classMass, hNew] using hCA j
  have hApos : 0 < A := by linarith only [hA.1]
  obtain ⟨_, hmiddle, _⟩ := MultipartiteClassMasses.objective_sharp_countCells
    V hV labels hlabels (by
      filter_upwards [hVA] with p hp
      split_ifs at hp ⊢ <;> exact hp) (.inl i) (by rw [hmain']; exact hApos) hparts
  rw [hmain'] at hmiddle
  have hT : (1 - A) / A ∈ Icc (2 : ℝ) 3 := by
    constructor
    · apply (le_div_iff₀ hApos).mpr
      linarith only [hA.2]
    · apply (div_le_iff₀ hApos).mpr
      linarith only [hA.1]
  have hcost := hmiddle hT
  rw [hVc, hVd] at hcost
  have heq : (∑ j, ∫ p : Ω × Ω in C j ×ˢ C j, chargeKernel hq.endpoint p.1 p.2
        ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q)) =
      (∑ j, ∫ p : Ω × Ω in C j ×ˢ C j, shiftedKernel W m p.1 p.2
        ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q)) +
      m * ∑ j, ((missingFlowEndpointLaw μ q).real (C j)) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hq.endpoint_diffuse_internal_charge hW hd hgap (C j) (hC j) (hCD j)
  rw [heq] at hcost
  have hbudget := hq.endpoint_budget hW
  have hmissing := hq.missing_density_eq_classMass_sq hW hd hgap
  dsimp only
  rw [hbudget, ← hmissing]
  nlinarith only [hcost]

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow
