module

public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWZeroBody
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWAtomGuards
public import Erdos1017.Exclusions.Common.Saturation.SelectedUnsaturatedZeroBody

/-!
# Zero-body exclusion at smooth `W` with or without an atomic partner

The smooth-`W` zero-body case is excluded whether or not the universal positive
cover has a saturated atomic partner (`no_smoothW_zero_body`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- The original smooth-W zero-body case is excluded whether or not
the universal positive cover has a saturated original atomic partner. -/
theorem no_smoothW_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) : False := by
  by_cases hsat : ∃ a : S.I, S.IsSaturatedAtomPair r a
  · obtain ⟨a, hpair⟩ := hsat
    exact S.no_smoothW_saturated_zero_body r a hW hd hgap he hactive hglobal hpair hzero
  · obtain ⟨hell, _, _, hratio, _⟩ :=
      S.smoothW_atom_contact_guards r hW hd hgap he hactive hglobal
    exact S.not_zero_body_of_no_saturated_partner r hW hd hgap hell.1 hzero hratio
      (fun a _ hpair => hsat ⟨a, hpair⟩)

end Erdos1017.CappedModel.SelectedHighLowStructure
