module

public import Erdos1017.ContactLocation.BenchmarkSplitCellClassification
public import Erdos1017.ContactLocation.FullSplitContactExclusion

/-!
# Split contacts lie at reciprocal cusps

A strict-gap global benchmark contact of a `FullStationaryClass` model in the
open split band must lie at a reciprocal cusp, since the strict split cells are
excluded (`split_contact_is_reciprocal`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An actual strict-gap global benchmark contact in the open split band
must lie at a reciprocal cusp. The split cell and its exclusion are
derived from the actual parameter, with no supplied index premise. -/
theorem FullStationaryClass.split_contact_is_reciprocal
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hband : d ∈ Set.Ioo (1 / 2 - Benchmark.epsilonStar) (1 / 2)) :
    ∃ k : ℕ, 3 ≤ k ∧ Real.sqrt (1 - 2 * d) = 1 / (k : ℝ) ∧
      d = (1 - 1 / (k : ℝ) ^ 2) / 2 := by
  have hd0 : 0 < 1 - 2 * d := by linarith [hband.2]
  have hr : Real.sqrt (1 - 2 * d) ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
    refine ⟨Real.sqrt_pos.mpr hd0, (Real.sqrt_lt' (by norm_num)).mpr ?_⟩
    nlinarith [hband.1, Benchmark.epsilonStar_lt_tenth]
  rcases Benchmark.split_cell_or_reciprocal hr with hcell | hreciprocal
  · obtain ⟨n, hn⟩ := hcell
    exact (hW.no_split_cell_contact hgap hglobal n hband hn).elim
  · obtain ⟨k, hk, hrk⟩ := hreciprocal
    refine ⟨k, hk, hrk, ?_⟩
    have hsq := Real.sq_sqrt hd0.le
    rw [hrk, one_div_pow] at hsq
    linarith

end Erdos1017.CappedModel
