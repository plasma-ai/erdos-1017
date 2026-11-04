module

public import Erdos1017.Exclusions.Cusp.SelectedCuspAtomGuards
public import Erdos1017.Exclusions.Common.Saturation.SelectedUnsaturatedZeroBody

/-!
# Unsaturated zero-body guards at a reciprocal cusp

A reciprocal cusp, including `k = 3`, pays every own-slope and signed-bonus
guard of the original unsaturated zero-body exclusion, with no smooth cusp
derivative (`not_cusp_zero_body_of_no_saturated_partner`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {W : Model Ω μ} {m : ℝ}

/-- The actual reciprocal cusp, including k=3, pays every own-slope and
signed-bonus guard of the original unsaturated zero-body exclusion. No
smooth cusp derivative, peak, source or atom-count certificate is used. -/
theorem not_cusp_zero_body_of_no_saturated_partner
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (k : ℕ) (hk : 3 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hnosat : ∀ u : S.I, u ≠ r → ¬S.IsSaturatedAtomPair r u) : False := by
  obtain ⟨hd, _, hell, _, _⟩ := hW.cusp_contact_parameters k hk hdk hgap hglobal
  obtain ⟨_, _, _, _, _, _, hbonus, _⟩ := S.cusp_atom_contact_guards r hW k hk hdk hgap hglobal
  exact S.not_zero_body_of_no_saturated_partner r hW hd hgap (by linarith [hell.1]) hzero hbonus hnosat

end Erdos1017.CappedModel.SelectedHighLowStructure
