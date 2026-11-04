module

public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWRNull
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWPositiveRegions
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredNullDiffuseDensity

/-!
# Positive-E and null-diffuse zero-body cases at smooth `W`

Two zero-body cases at smooth-`W` contact are excluded: the positive-`E`
saturated case, for null or positive `R` and any countable exterior family, and
the null-diffuse case, whose slope and ratio guards come from the original
model.
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

/-- Every positive-E smooth-W saturated zero-body case is excluded,
including a null or positive R and any countable exterior family. -/
theorem no_smoothW_zero_body_of_E_positive
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) : False := by
  by_cases hR : μ (S.D ∩ S.rootNeighborhood a) = 0
  · exact S.no_smoothW_zero_body_R_null r a hW hd hgap he hactive hglobal hpair hzero hR hE
  · exact S.no_smoothW_zero_body_of_positive_regions r a hW hd hgap he hactive hglobal
      hpair hzero (pos_iff_ne_zero.mpr hR) hE

/-- The actual null-diffuse contradiction applies at smooth-W contact
with its slope and ratio guards derived from the original model. -/
theorem no_smoothW_zero_body_of_D_null
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hD : μ S.D = 0) : False := by
  obtain ⟨hell, _, _, hratio, _⟩ :=
    S.smoothW_covered_contact_guards r a hpair.1 hW hd hgap he hactive hglobal
  exact S.not_covered_null_diffuse r a hW hd hgap hpair hell.1 hzero hD hratio

end Erdos1017.CappedModel.SelectedHighLowStructure
