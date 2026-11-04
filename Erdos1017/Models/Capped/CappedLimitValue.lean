module

public import Erdos1017.Models.Capped.CappedGrowingLimit
public import Erdos1017.Models.Capped.CappedLowerComparison

/-!
# Convergence of capped values to the finite-graph limit

Both capped comparisons give a uniform error independent of density, the
attained capped values converge to the finite-graph limit (`capValue_tendsto`),
and that limit is attained by a fully feasible decorated model on the fixed
atomless space which compares every fully feasible competitor.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]

/-- Both capped comparisons give a uniform error independent of density.
The cutoff can exceed the displayed order. -/
theorem capValue_error_bound (n r : ℕ) (hnr : n + 2 ≤ r) (d : ℝ)
    (hd : d ∈ Set.Icc 0 (1 / 2)) :
    0 ≤ capValue Ω μ r d - FractionalGraph.densityLimit d ∧
      capValue Ω μ r d - FractionalGraph.densityLimit d ≤
        1 / (2 * ((n : ℝ) + 1)) := by
  have hr : 2 ≤ r := by omega
  have hlow := densityLimit_le_capValue (μ := μ) r d hd
  have hupp := capValue_le_densityLimit_add_error (μ := μ) r hr d hd
  refine ⟨sub_nonneg.mpr hlow, ?_⟩
  have hnrreal : (n : ℝ) + 2 ≤ r := by exact_mod_cast hnr
  have hnreal : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hchoose : (n : ℝ) + 1 ≤ (r.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    have hproduct : 0 ≤ ((r : ℝ) - 2) * ((r : ℝ) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hdiv := div_le_div_of_nonneg_left hd.1 hden hchoose
  have hsmall := div_le_div_of_nonneg_right hd.2 hden.le
  have heq : (1 / 2 : ℝ) / ((n : ℝ) + 1) = 1 / (2 * ((n : ℝ) + 1)) := by
    rw [div_div]
  linarith

/-- The actual attained capped values converge to the finite-graph limit. -/
theorem capValue_tendsto (d : ℝ) (hd : d ∈ Set.Icc 0 (1 / 2)) :
    Tendsto (fun n : ℕ => capValue Ω μ (n + 2) d) atTop
      (𝓝 (FractionalGraph.densityLimit d)) := by
  have herror : Tendsto (fun n : ℕ => capValue Ω μ (n + 2) d -
      FractionalGraph.densityLimit d) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => (capValue_error_bound (μ := μ) n (n + 2) le_rfl d hd).1)
      (fun n => (capValue_error_bound (μ := μ) n (n + 2) le_rfl d hd).2)
    simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
  simpa only [sub_add_cancel, zero_add] using herror.add_const (FractionalGraph.densityLimit d)

/-- The finite-graph fractional limit is attained by a genuine fully
feasible decorated model on the fixed atomless probability space. -/
theorem exists_fullFeasible_at_density (d : ℝ) (hd : d ∈ Set.Icc 0 (1 / 2)) :
    ∃ W : Model Ω μ, FullFeasible W ∧ density W = d ∧
      objective W = FractionalGraph.densityLimit d := by
  choose W hW hdW hoW _ using fun n : ℕ =>
    exists_fixedMeasureMaximizer (μ := μ) (n + 2) d hd
  have hr : StrictMono (fun n : ℕ => n + 2) :=
    fun i j hij => Nat.add_lt_add_right hij 2
  obtain ⟨V, φ, hφ, hV, _, hdensity, hobjective⟩ :=
    exists_fullFeasible_growing_limit W (fun n => n + 2) hr.tendsto_atTop hW
  have hdV : density V = d := by
    have h : Tendsto (fun _ : ℕ => d) atTop (𝓝 (density V)) := by
      simpa only [hdW] using hdensity
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hvalues : Tendsto (fun n : ℕ => objective (W n)) atTop
      (𝓝 (FractionalGraph.densityLimit d)) := by
    simpa only [hoW] using capValue_tendsto (μ := μ) d hd
  exact ⟨V, hV, hdV, tendsto_nhds_unique hobjective (hvalues.comp hφ.tendsto_atTop)⟩

/-- The attained full model compares every fully feasible competitor,
including competitors with another latent probability law. -/
theorem exists_full_maximizer (d : ℝ) (hd : d ∈ Set.Icc 0 (1 / 2)) :
    ∃ W : Model Ω μ, FullFeasible W ∧ density W = d ∧
      objective W = FractionalGraph.densityLimit d ∧
      ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
        FullFeasible V → density V = d → objective V ≤ objective W := by
  obtain ⟨W, hW, hdW, hoW⟩ := exists_fullFeasible_at_density (μ := μ) d hd
  refine ⟨W, hW, hdW, hoW, ?_⟩
  intro ν _ V hV hdV
  simpa only [hdV, hoW] using fullFeasible_objective_le_densityLimit V hV

end Erdos1017.CappedModel
