module

public import Erdos1017.Exclusions.Corner.SelectedCornerRNull
public import Erdos1017.Exclusions.Corner.SelectedCornerZeroBodyCases

/-!
# Exclusion of zero body energy at the corner

An original atom at the `W`/`E₂` corner cannot have zero positive-body energy:
every diffuse-region alternative of the saturated case is excluded, and both
saturation and all diffuse and exterior alternatives are derived.
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

/-- Every diffuse-region alternative of the actual saturated corner
zero-body case is excluded without a region or exterior-atom certificate. -/
theorem no_corner_saturated_zero_body
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) : False := by
  by_cases hR : μ (S.D ∩ S.rootNeighborhood a) = 0
  · exact S.no_corner_zero_body_R_null r a hW hd hgap he heq hglobal hpair hzero hR
  · by_cases hE : μ (S.D \ S.rootNeighborhood a) = 0
    · exact S.no_corner_zero_body_E_null r a hW hd hgap he heq hglobal hpair hzero hE
    · exact S.no_corner_zero_body_of_positive_regions r a hW hd hgap he heq hglobal
        hpair hzero (pos_iff_ne_zero.mpr hR) (pos_iff_ne_zero.mpr hE)

/-- An original atom at the W/E2 corner cannot have zero positive-body
energy. Both saturation and all diffuse/exterior alternatives are derived. -/
theorem no_corner_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) : False := by
  by_cases hsat : ∃ a : S.I, S.IsSaturatedAtomPair r a
  · obtain ⟨a, hpair⟩ := hsat
    exact S.no_corner_saturated_zero_body r a hW hd hgap he heq hglobal hpair hzero
  · exact S.not_corner_zero_body_of_no_saturated_partner r hW hd hgap he heq hglobal
      hzero (fun a _ hpair => hsat ⟨a, hpair⟩)

end Erdos1017.CappedModel.SelectedHighLowStructure
