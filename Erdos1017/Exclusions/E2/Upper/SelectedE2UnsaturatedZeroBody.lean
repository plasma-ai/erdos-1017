module

public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards
public import Erdos1017.Exclusions.Common.Saturation.SelectedUnsaturatedZeroBody

/-!
# Unsaturated zero-body exit at the `E₂` contact

`E₂` value and derivative contact pay every `ell` and bonus guard in the
original unsaturated zero-body exit, with no peak, atom count, Phi or
edited-model input remaining (`not_e2_zero_body_of_no_saturated_partner`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {W : Model Ω μ} {m : ℝ}

/-- Actual E2 value and derivative contact pay every ell and bonus guard
in the original unsaturated zero-body exit. No peak, atom count, Phi or
edited-model input remains. -/
theorem not_e2_zero_body_of_no_saturated_partner
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hnosat : ∀ u : S.I, u ≠ r → ¬S.IsSaturatedAtomPair r u) : False := by
  obtain ⟨_, hell, _, _, hbonus, _⟩ := S.e2_atom_contact_guards r hW hq hdq hvalue hderiv hgap hglobal
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq
  exact S.not_zero_body_of_no_saturated_partner r hW hd hgap hell.1 hzero hbonus hnosat

end Erdos1017.CappedModel.SelectedHighLowStructure
