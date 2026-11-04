module

public import Erdos1017.Models.Capped.CappedSamplingApproximation

/-!
# Fully feasible limits of growing capped models

A model is fully feasible (`FullFeasible`) when every finite clique order
satisfies its sampled inequality; sampling bounds its objective by the
finite-graph fractional limit, and growing capped models have a fully feasible
subsequential limit with sampled tests, density and objective converging
together.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every finite clique order satisfies its actual sampled inequality. -/
def FullFeasible (W : Model Ω μ) : Prop := ∀ r : ℕ, Feasible r W

omit [IsProbabilityMeasure μ] in
/-- Increasing the set of imposed orders can only strengthen feasibility. -/
theorem feasible_mono {W : Model Ω μ} {r s : ℕ} (hW : Feasible s W) (hrs : r ≤ s) :
    Feasible r W :=
  fun n hn hnr => hW n hn (hnr.trans hrs)

/-- Sampling bounds the objective of every fully feasible model by the
actual finite-graph fractional limit. -/
theorem fullFeasible_objective_le_densityLimit (W : Model Ω μ) (hW : FullFeasible W) :
    objective W ≤ FractionalGraph.densityLimit (density W) := by
  have hbound (n : ℕ) : objective W ≤ FractionalGraph.densityLimit (density W) +
      density W / ((n : ℝ) + 1) := by
    have h := objective_le_densityLimit_add_cap_error W (r := n + 2) (by omega) (hW _)
    have hchoose : (n : ℝ) + 1 ≤ ((n + 2).choose 2 : ℝ) := by
      rw [Nat.cast_choose_two]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hdiv := div_le_div_of_nonneg_left (density_mem W).1 hden hchoose
    linarith
  have hlim : Tendsto (fun n : ℕ => FractionalGraph.densityLimit (density W) +
      density W / ((n : ℝ) + 1)) atTop (𝓝 (FractionalGraph.densityLimit (density W))) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (density W)
    simpa only [mul_zero, add_zero, mul_one_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => FractionalGraph.densityLimit (density W))
        atTop (𝓝 (FractionalGraph.densityLimit (density W)))).add h
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => objective W) atTop (𝓝 (objective W)))
    hlim (Eventually.of_forall hbound)

/-- Eventual feasibility suffices for closedness of the imposed sampled
tests; no finite initial segment of the sequence is used. -/
theorem feasible_of_eventual_sampledTest_limit (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (r : ℕ) (hW : ∀ᶠ k in atTop, Feasible r (W k))
    (hconv : ∀ n, 2 ≤ n → n ≤ r →
      Tendsto (fun k => continuousTestIntegral (W k) n
        ⟨violation, continuous_violation n⟩) atTop
        (𝓝 (continuousTestIntegral V n ⟨violation, continuous_violation n⟩))) :
    Feasible r V := by
  apply (feasible_iff_testIntegral V r).mpr
  intro n hn hnr
  have hzero : (fun k => continuousTestIntegral (W k) n
      ⟨violation, continuous_violation n⟩) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [hW] with k hk
    have ht := (feasible_iff_testIntegral (W k) r).mp hk n hn hnr
    rw [testIntegral_eq_ofReal_continuousTestIntegral] at ht
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp ht)
      (integral_nonneg (fun _ => integral_nonneg violation_nonneg))
  have hzlim : Tendsto (fun k => continuousTestIntegral (W k) n
      ⟨violation, continuous_violation n⟩) atTop (𝓝 0) :=
    (tendsto_congr' hzero).mpr tendsto_const_nhds
  have hz : continuousTestIntegral V n ⟨violation, continuous_violation n⟩ = 0 :=
    tendsto_nhds_unique (hconv n hn hnr) hzlim
  rw [testIntegral_eq_ofReal_continuousTestIntegral, hz, ENNReal.ofReal_zero]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]

/-- Growing capped models have an actual fully feasible subsequential limit,
with all sampled continuous tests, density and objective converging together. -/
theorem exists_fullFeasible_growing_limit (W : ℕ → Model Ω μ) (r : ℕ → ℕ)
    (hr : Tendsto r atTop atTop) (hW : ∀ k, Feasible (r k) (W k)) :
    ∃ (V : Model Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧ FullFeasible V ∧
      (∀ (n : ℕ) (F : C(CliquePair n → CappedColor, ℝ)),
        Tendsto (fun k => continuousTestIntegral (W (φ k)) n F) atTop
          (𝓝 (continuousTestIntegral V n F))) ∧
      Tendsto (fun k => density (W (φ k))) atTop (𝓝 (density V)) ∧
      Tendsto (fun k => objective (W (φ k))) atTop (𝓝 (objective V)) := by
  obtain ⟨V, φ, hφ, hconv, hdensity, hobjective⟩ := exists_sampledTest_limit W
  refine ⟨V, φ, hφ, ?_, hconv, hdensity, hobjective⟩
  intro s
  apply feasible_of_eventual_sampledTest_limit (fun k => W (φ k)) V s
  · have hs := (hr.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop s)
    exact hs.mono (fun k hk => feasible_mono (hW (φ k)) hk)
  · intro n _ _
    exact hconv n ⟨violation, continuous_violation n⟩

end Erdos1017.CappedModel
