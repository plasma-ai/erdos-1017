module

public import Erdos1017.ContactLocation.BenchmarkSplitSideExtensions
public import Erdos1017.ContactLocation.FullOneSidedContact

/-!
# Slope bracket and gamma margin at a split cusp

At a reciprocal benchmark cusp of a full stationary class, the own multiplier
lies strictly between the two side slopes, and with the benchmark value this
gives a positive quantitative lower bound on the model's gamma.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- At an actual reciprocal benchmark cusp, the original own multiplier
lies strictly between the two explicit side slopes. Both actual branch
identities and both endpoint exclusions are derived. -/
theorem FullStationaryClass.split_cusp_strict_slope
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (k : ℕ) (hk : 3 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    -m ∈ Ioo (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)) (2 - 2 / (k : ℝ)) ∧
      2 - 2 / (k : ℝ) < 2 := by
  subst d
  have hband := Benchmark.split_cusp_mem_band k hk
  have hd : (1 - 1 / (k : ℝ) ^ 2) / 2 ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
    ⟨by linarith [hband.1, Benchmark.epsilonStar_lt_tenth], hband.2⟩
  have hleft : HasDerivWithinAt benchmark (-(2 - 2 / (k : ℝ)))
      (Iic ((1 - 1 / (k : ℝ) ^ 2) / 2)) ((1 - 1 / (k : ℝ) ^ 2) / 2) :=
    (Benchmark.split_cusp_left_hasDerivAt k hk).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
      (Benchmark.benchmark_split_cusp_left_eventually k hk) le_rfl
  have hright : HasDerivWithinAt benchmark
      (-(2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)))
      (Ici ((1 - 1 / (k : ℝ) ^ 2) / 2)) ((1 - 1 / (k : ℝ) ^ 2) / 2) :=
    (Benchmark.split_cusp_right_hasDerivAt k hk).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
      (Benchmark.benchmark_split_cusp_right_eventually k hk) le_rfl
  have hbracket := hW.multiplier_mem_one_sided_slopes_of_strict_gap
    hd hgap hglobal hleft hright
  have hneleft := hW.multiplier_ne_left_concave_slope_of_strict_gap hd hgap hglobal
    (Benchmark.splitDensityExtension (k - 1))
    (Benchmark.splitDensityExtension_contDiffAt (k - 1) hd.2)
    (Benchmark.splitDensityExtension_second_deriv_neg (k - 1) (by omega) hd.2).le
    (Benchmark.benchmark_split_cusp_left_eventually k hk).symm
  have hneright := hW.multiplier_ne_right_concave_slope_of_strict_gap hd hgap hglobal
    (Benchmark.splitDensityExtension k)
    (Benchmark.splitDensityExtension_contDiffAt k hd.2)
    (Benchmark.splitDensityExtension_second_deriv_neg k (by omega) hd.2).le
    (Benchmark.benchmark_split_cusp_right_eventually k hk).symm
  rw [(Benchmark.split_cusp_left_hasDerivAt k hk).deriv] at hneleft
  rw [(Benchmark.split_cusp_right_hasDerivAt k hk).deriv] at hneright
  have hstrictleft := lt_of_le_of_ne hbracket.1 hneleft.symm
  have hstrictright := lt_of_le_of_ne hbracket.2 hneright
  exact ⟨⟨by linarith, by linarith⟩, Benchmark.split_cusp_upper_slope_lt_two k (by omega)⟩

/-- The strict cusp bracket and the actual benchmark value give a
positive quantitative lower bound for this same model's gamma. -/
theorem FullStationaryClass.split_cusp_gamma_margin
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (k : ℕ) (hk : 3 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    0 < (2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2 ∧
      (2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2 < 2 * (c - m * d) + m := by
  have hslope := (hW.split_cusp_strict_slope k hk hdk hgap hglobal).1.2
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hband : d ∈ Ioo (1 / 2 - Benchmark.epsilonStar) (1 / 2) := by
    rw [hdk]
    exact Benchmark.split_cusp_mem_band k hk
  have hsqrt : Real.sqrt (1 - 2 * d) = 1 / (k : ℝ) := by
    rw [hdk]
    have heq : 1 - 2 * ((1 - 1 / (k : ℝ) ^ 2) / 2) = (1 / (k : ℝ)) ^ 2 := by ring
    rw [heq, Real.sqrt_sq (by positivity)]
  have hvalue : benchmark d = ((k : ℝ) - 1) / (k : ℝ) ^ 3 := by
    rw [(Benchmark.benchmark_split_eventually hband).eq_of_nhds, hsqrt]
    exact Benchmark.splitValue_reciprocal k (by omega)
  have hmargin : 0 < (2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2 :=
    div_pos (by linarith) (sq_pos_of_pos hk0)
  refine ⟨hmargin, ?_⟩
  have hid : 2 * (c - m * d) + m -
      (2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2 =
        2 * (c - ((k : ℝ) - 1) / (k : ℝ) ^ 3) := by
    rw [hdk]
    field_simp
    ring
  rw [hvalue] at hgap
  linarith

end Erdos1017.CappedModel
