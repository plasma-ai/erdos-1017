module

public import Erdos1017.Exclusions.Common.Physical.PhysicalPositiveCover
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalPrimal

/-!
# Rooted primal in the zero-body branch

Zero positive-body energy, measured with the original charge and law, makes
every tight parent of the same-model primal meet the root, so a universal whole
atom in the selected strict-gap model constructs its own tight bounded-order
primal with a unique root.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Zero positive-body energy is measured using the original charge and
original probability law, on the literal complement of the whole fiber. -/
theorem zero_body_ae_charge_nonpositive (S : SelectedHighLowStructure W m) (r : S.I)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val → chargeKernel W p.1 p.2 ≤ 0 := by
  apply PhysicalPrimal.ae_nonpositive_of_bodyPositiveEnergy_zero μ
    (Function.uncurry (chargeKernel W))
    (W.stronglyMeasurable_moment CappedColor.continuous_charge.measurable.stronglyMeasurable).measurable
    3 _ _ (S.hfibers r.val r.property).1 hzero
  intro p
  have ha := adjacency_moment_mem W p
  have hlo := neg_three_adjacency_moment_le_charge W p
  have hhi := charge_moment_le_adjacency W p
  change |W.moment CappedColor.charge p| ≤ 3
  apply abs_le.mpr
  constructor <;> linarith [ha.1, ha.2]

/-- The actual same-model primal's every tight parent meets the root in
the zero-body branch. Pair balance transfers the original pair-null
exception; joint absolute continuity is not asserted. -/
theorem UniversalPhysicalPrimal.ae_parent_meets_of_zero_body
    {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∃ i, S.ρ (v i) = r.val := by
  have hcover := S.zero_body_ae_charge_nonpositive r hzero
  apply PhysicalPrimal.ae_parent_meets_positive_cover P.laws _ P.feasible.2.2.2
    (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val} _ P.tight_original n
  exact ae_mono Measure.restrict_le_self hcover

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- An actual universal whole atom in the selected strict-gap model
constructs its own tight bounded-order primal. Vanishing original body
energy then forces a unique root in every parent and zero rootless law.
This is the physical zero-body entry, not the subsequent cover exclusion. -/
theorem exists_zero_body_rooted_primal (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∃ P : S.UniversalPhysicalPrimal r c,
      (∀ n, ∀ᵐ v ∂P.laws n, ∃! i, S.ρ (v i) = r.val) ∧
      ∀ n, PhysicalRootReplacement.noRootLaw (P.laws n) {x | S.ρ x = r.val} = 0 := by
  obtain ⟨P⟩ := S.exists_universal_physical_primal r hW hd hgap hN
  refine ⟨P, ?_, ?_⟩
  · intro n
    filter_upwards [P.ae_parent_meets_of_zero_body hzero n, P.unique_root n]
      with v hv hu
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, hi, fun j hj => hu j i hj hi⟩
  · intro n
    apply PhysicalPrimal.noRootLaw_eq_zero_of_positive_cover P.laws _ P.feasible.2.2.2
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val} _ P.tight_original n
    exact ae_mono Measure.restrict_le_self (S.zero_body_ae_charge_nonpositive r hzero)

end Erdos1017.CappedModel.SelectedHighLowStructure
