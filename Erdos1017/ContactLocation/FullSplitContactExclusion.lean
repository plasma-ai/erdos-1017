module

public import Erdos1017.ContactLocation.BenchmarkSplitCurvature
public import Erdos1017.ContactLocation.FullPositiveContactCurvature

/-!
# No contact in a strict split cell

A strict-gap global benchmark contact of a `FullStationaryClass` model cannot
lie in a strict split cell inside the open split-active band; benchmark activity
and `C²` regularity are derived (`no_split_cell_contact`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An actual strict-gap global benchmark contact cannot lie in a strict
split cell inside the open split-active band. Benchmark activity and C²
regularity are derived from the displayed density and cell guards. -/
theorem FullStationaryClass.no_split_cell_contact
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (n : ℕ)
    (hband : d ∈ Set.Ioo (1 / 2 - Benchmark.epsilonStar) (1 / 2))
    (hcell : Real.sqrt (1 - 2 * d) ∈
      Set.Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) : False := by
  have hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) :=
    ⟨by linarith [hband.1, Benchmark.epsilonStar_lt_tenth], hband.2⟩
  have hpos := hW.benchmark_second_deriv_pos_of_strict_gap hd hgap hglobal
    (Benchmark.benchmark_contDiffAt_split_cell n hband hcell)
  exact (not_lt_of_gt hpos)
    (Benchmark.benchmark_second_deriv_neg_split_cell n hband hcell)

end Erdos1017.CappedModel
