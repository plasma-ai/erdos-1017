module

public import Erdos1017.Exclusions.Cusp.SelectedCuspRecoveryBounds
public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceCredits

/-!
# The shared source budget at a cusp endpoint

All four original source resources are paid from the same endpoint budget, the
strict excess and nonnegative partial-flow energy being dropped only after the
exact accounting (`cusp_source_budget_lt`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- All four original source resources are paid from the same actual
endpoint budget. The strict excess and nonnegative partial-flow energy
are dropped only after the exact full-flow decomposition is substituted. -/
theorem cusp_source_budget_lt (R : S.ReverseRecovery) (r i : S.I)
    (k : ℕ) (hk : 4 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    S.originalAtomMass i * R.cuspPeakCredit r i + R.cuspRemainderCredit r i +
        S.originalAtomMass i * R.cuspCrossEnergy i + R.cuspRemainderEnergy i / 2 <
      (2 - 2 / (k : ℝ) + m) * (R.height ^ 2 - 1 / (k : ℝ) ^ 2) / 2 -
        (-m - 1) * R.cuspOutsideSquares r i / 2 := by
  have hparameters := hW.cusp_contact_parameters k (by omega) hdk hgap hglobal
  have hmargin := hparameters.2.2.2.2
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hid : 2 * (c - m * d) + m - (2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2 =
      2 * (c - ((k : ℝ) - 1) / (k : ℝ) ^ 3) := by
    rw [hdk]
    field_simp
    ring
  have hexcess : 0 < c - ((k : ℝ) - 1) / (k : ℝ) ^ 3 := by linarith
  have hbudget := R.cusp_endpoint_source_budget r i k hk hdk hW hgap hglobal hr hinside
  rw [R.cusp_full_flow_energy hW hparameters.1 hgap r i hr hinside] at hbudget
  have hpartial := R.isFullReverseFlow.sourceSlice_energy_nonnegative hW hparameters.1
    hgap R.measurableSet_source.compl
  change 0 ≤ kernelEnergy (μ := μ) (shiftedKernel W m)
    (MissingFlow.direction μ R.cuspPartialFlow) at hpartial
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
