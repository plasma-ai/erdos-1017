module

public import Erdos1017.ContactLocation.BenchmarkMixedSplitJunction
public import Erdos1017.ContactLocation.FullOneSidedContact

/-!
# No contact at the `W`/split junction

The `W`/split junction cannot carry a strict-gap global benchmark contact of a
`FullStationaryClass` model; the common one-sided slope and the concave
right-side extension are derived (`no_mixed_split_junction_contact`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The actual W/split junction cannot carry an original strict-gap
global benchmark contact. The common one-sided slope and the concave
right-side extension are derived from the literal junction density. -/
theorem FullStationaryClass.no_mixed_split_junction_contact
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hd1 : d = 1 / 2 - Benchmark.epsilonStar) : False := by
  subst d
  have hd : 1 / 2 - Benchmark.epsilonStar ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) :=
    ⟨by linarith [Benchmark.epsilonStar_lt_tenth],
      by linarith [Benchmark.epsilonStar_pos]⟩
  have hbracket := hW.multiplier_mem_one_sided_slopes_of_strict_gap hd hgap hglobal
    Benchmark.benchmark_mixed_split_left_hasDerivWithinAt
    Benchmark.benchmark_mixed_split_right_hasDerivWithinAt
  have hm : m = -(Real.sqrt 21 - 1) / 6 := le_antisymm hbracket.2 hbracket.1
  have hne := hW.multiplier_ne_right_concave_slope_of_strict_gap hd hgap hglobal
    (Benchmark.splitDensityExtension 2)
    (Benchmark.splitDensityExtension_contDiffAt 2 hd.2)
    (Benchmark.splitDensityExtension_second_deriv_neg 2 (by omega) hd.2).le
    Benchmark.benchmark_mixed_split_right_eventually.symm
  exact hne (hm.trans Benchmark.splitDensityExtension_two_junction_hasDerivAt.deriv.symm)

end Erdos1017.CappedModel
