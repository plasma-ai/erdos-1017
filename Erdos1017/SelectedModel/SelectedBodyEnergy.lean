module

public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure
public import Erdos1017.Exclusions.Common.Physical.PhysicalPositiveCover
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyBody

/-!
# Positive-body energy of the selected model

The raw positive-body energy on the restricted original product law is
nonnegative for any cover set, and strict support identifies it with the
physical representative's global positive-body square integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Original raw positive-body energy is nonnegative, on the literal
restricted original product law, for any proposed cover set. -/
theorem bodyPositiveEnergy_nonnegative (W : Model Ω μ) (I : Set Ω) :
    0 ≤ PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W)) I :=
  integral_nonneg (fun p => sq_nonneg (max (chargeKernel W p.1 p.2) 0))

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Actual own strict support identifies the raw restricted body energy
with the physical representative's global positive-body square integral.
The identity is licensed by one event on the same original product measure. -/
theorem FullStationaryClass.bodyPositiveEnergy_eq_physicalBody
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (I : Set Ω) (hI : MeasurableSet I) :
    PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W)) I =
      ∫ p : Ω × Ω,
        (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m) I p.1 p.2) ^ 2
          ∂μ.prod μ := by
  have hcharge := PhysicalRepresentative.charge_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  rw [PhysicalPrimal.bodyPositiveEnergy, ← integral_indicator (hI.compl.prod hI.compl)]
  apply integral_congr_ae
  filter_upwards [hcharge] with p hp
  by_cases h : p.1 ∉ I ∧ p.2 ∉ I
  · simp [IndependentAtomCopy.positiveBody, Function.uncurry, h, hp]
  · simp [IndependentAtomCopy.positiveBody, h]

end Erdos1017.CappedModel
