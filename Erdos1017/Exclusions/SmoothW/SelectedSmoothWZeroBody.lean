module

public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWENull
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWZeroBodyCases

/-!
# Saturated zero-body case at a smooth point of `W`

The saturated zero-body case is excluded at smooth-`W` contact, covering every
diffuse-region and exterior-atom alternative (`no_smoothW_saturated_zero_body`).
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

/-- The original saturated zero-body case is excluded at genuine smooth-W
contact. All diffuse-region and exterior-atom alternatives are proved. -/
theorem no_smoothW_saturated_zero_body
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
      {x | S.ρ x = r.val} = 0) : False := by
  by_cases hE : μ (S.D \ S.rootNeighborhood a) = 0
  · by_cases hR : μ (S.D ∩ S.rootNeighborhood a) = 0
    · have hD : μ S.D = 0 := by
        have hparts : S.D = (S.D ∩ S.rootNeighborhood a) ∪
            (S.D \ S.rootNeighborhood a) := (inter_union_sdiff _ _).symm
        apply le_antisymm _ zero_le
        calc
          μ S.D = μ ((S.D ∩ S.rootNeighborhood a) ∪ (S.D \ S.rootNeighborhood a)) :=
            congrArg μ hparts
          _ ≤ μ (S.D ∩ S.rootNeighborhood a) + μ (S.D \ S.rootNeighborhood a) :=
            measure_union_le _ _
          _ = 0 := by rw [hR, hE, add_zero]
      exact S.no_smoothW_zero_body_of_D_null r a hW hd hgap he hactive hglobal hpair hzero hD
    · exact S.no_smoothW_zero_body_E_null r a hW hd hgap he hactive hglobal hpair hzero
        hE (pos_iff_ne_zero.mpr hR)
  · exact S.no_smoothW_zero_body_of_E_positive r a hW hd hgap he hactive hglobal hpair hzero
      (pos_iff_ne_zero.mpr hE)

end Erdos1017.CappedModel.SelectedHighLowStructure
