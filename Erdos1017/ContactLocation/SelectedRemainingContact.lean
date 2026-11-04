module

public import Erdos1017.Benchmark.BenchmarkContactAlternatives
public import Erdos1017.ContactLocation.FullMixedSplitJunction
public import Erdos1017.ContactLocation.FullSplitContactLocation
public import Erdos1017.Models.Selection.FullStationarySelection
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWExclusion

/-!
# The remaining contact cases for a selected maximum

This module defines `RemainingBenchmarkContact`, the contact cases left after
strict `W`, split interiors and the split/`W` junction are excluded, shows that
every selected strict-gap global maximum lies in one of the three remaining
cases, and constructs from a failure of the upper bound a selected model with
one remaining contact. It feeds the assembly in `FullBenchmarkUpper`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

/-- The remaining actual contacts after strict W, split interiors, and
the split/W junction have been excluded. The corner retains equality;
no smooth E2 multiplier is assigned to it. -/
def RemainingBenchmarkContact (d m : ℝ) : Prop :=
  (∃ q ∈ Ioo (0 : ℝ) (213 / 1000),
    1 / 2 - d ∈ Ioo Benchmark.epsilonC (1 / 4) ∧
    Benchmark.mixedCurve (1 / 2 - d) < Benchmark.twoHeadCurve (1 / 2 - d) ∧
    d = (1 - LowerE2Scalar.missingMass q) / 2 ∧
    benchmark d = Benchmark.twoHeadValue ((q + 2) / 3) ∧
    HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d ∧
    m = -LowerE2Scalar.multiplier q) ∨
  (1 / 2 - d ∈ Ioo Benchmark.epsilonC Benchmark.epsilonD ∧
    Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d)) ∨
  (∃ k : ℕ, 3 ≤ k ∧ Real.sqrt (1 - 2 * d) = 1 / (k : ℝ) ∧
    d = (1 - 1 / (k : ℝ) ^ 2) / 2)

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- Every actual selected strict-gap global maximum lies in one of the
three explicit remaining contact cases. All excluded cases are discharged
on the same original model and its recorded multiplier. -/
theorem SelectedHighLowStructure.remaining_benchmark_contact
    (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : RemainingBenchmarkContact d m := by
  rcases lt_trichotomy (1 / 2 - d) Benchmark.epsilonStar with hsplit | heq | hfamily
  · exact Or.inr (Or.inr (hW.split_contact_is_reciprocal hgap hglobal
      ⟨by linarith, hd.2⟩))
  · exact (hW.no_mixed_split_junction_contact hgap hglobal (by linarith)).elim
  · rcases Benchmark.family_contact_alternatives
      ⟨hfamily, show 1 / 2 - d < 1 / 4 by linarith [hd.1]⟩ with hWbranch | hE2 | hcorner
    · exact (S.no_smoothW_contact hW hd hgap hWbranch.1 hWbranch.2 hglobal).elim
    · obtain ⟨q, hq, hdq, hvalue, hder⟩ :=
        Benchmark.strict_twoHead_contact_parameters hd hE2.1.1 hE2.2
      have hm := full_stationary_multiplier_eq_benchmark_deriv W hW.full hglobal
        (show HasDerivAt benchmark (-LowerE2Scalar.multiplier q) (density W) by
          rwa [hW.density_eq]) m _ hW.stationary
        (hW.strict_gap_structure hd hgap).nonconstant_degree
      exact Or.inl ⟨q, hq, hE2.1, hE2.2, hdq, hvalue, hder, hm⟩
    · exact Or.inr (Or.inl hcorner)

/-- A genuine failure of the upper bound constructs an actual selected
model and one remaining contact. Neither the selected structure nor a
contact classification is an input to this existence theorem. -/
theorem exists_selected_remaining_contact
    (hfailure : ∃ d ∈ Icc (0 : ℝ) (1 / 2),
      benchmark d < FractionalGraph.densityLimit d) :
    ∃ (d : ℝ) (W : Model Ω μ) (m : ℝ), d ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧
      FullStationaryClass d (FractionalGraph.densityLimit d) W m ∧
      benchmark d < FractionalGraph.densityLimit d ∧
      (∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
        FullFeasible V → objective V - benchmark (density V) ≤
          objective W - benchmark (density W)) ∧
      ∃ _S : SelectedHighLowStructure W m, RemainingBenchmarkContact d m := by
  obtain ⟨d, W, m, hd, hW, hpositive, hglobal, hmin, hmax⟩ :=
    exists_selected_full_positive_global_excess (Ω := Ω) (μ := μ) hfailure
  have hgap : benchmark d < FractionalGraph.densityLimit d := by
    rw [hW.objective_eq, hW.density_eq] at hpositive
    linarith
  obtain ⟨S⟩ := hW.exists_selected_high_low_structure hd hgap hmin hmax
  exact ⟨d, W, m, hd, hW, hgap, hglobal, S, S.remaining_benchmark_contact hW hd hgap hglobal⟩

end Erdos1017.CappedModel
