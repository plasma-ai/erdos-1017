module

public import Erdos1017.Models.Capped.CappedLimitValue
public import Erdos1017.SelectedModel.Capped.CappedValueContinuity
public import Erdos1017.Models.Capped.CappedDeterministicLimit

/-!
# Capped maximizer sequences and their limits

Capped values converge to the fractional density limit along any growing cutoff
sequence, also with varying prescribed densities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]

/-- The actual capped value converges along any cutoff sequence tending
to infinity; no monotonicity or rate is imposed. -/
theorem capValue_tendsto_of_growing_cutoff (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (d : ℝ) (hd : d ∈ Set.Icc 0 (1 / 2)) :
    Tendsto (fun n => capValue Ω μ (r n) d) atTop (𝓝 (FractionalGraph.densityLimit d)) := by
  have herr : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨s, hs⟩ := (herr.eventually (gt_mem_nhds hε)).exists
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hr.eventually (eventually_ge_atTop (s + 2)))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hlo, hhi⟩ := capValue_error_bound (μ := μ) s (r n) (hN n hn) d hd
  rw [Real.dist_eq, abs_of_nonneg hlo]
  exact hhi.trans_lt hs

/-- Actual cap values converge to the genuine fractional density limit
when both prescribed densities and imposed cutoffs vary. Limit admissibility
is derived; the density estimate is the actual three-Lipschitz cap bound. -/
theorem capValue_tendsto_of_density_cutoff (r : ℕ → ℕ) (d : ℕ → ℝ) (d₀ : ℝ)
    (hr : Tendsto r atTop atTop) (hd : ∀ n, d n ∈ Set.Icc 0 (1 / 2))
    (hlim : Tendsto d atTop (𝓝 d₀)) :
    Tendsto (fun n => capValue Ω μ (r n) (d n)) atTop (𝓝 (FractionalGraph.densityLimit d₀)) := by
  have hd₀ : d₀ ∈ Set.Icc 0 (1 / 2) :=
    isClosed_Icc.mem_of_tendsto hlim (Eventually.of_forall hd)
  have hzero : Tendsto (fun n => capValue Ω μ (r n) (d n) - capValue Ω μ (r n) d₀) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [Real.norm_eq_abs]
    apply squeeze_zero (fun _ => abs_nonneg _)
      (fun n => capValue_abs_sub_le (μ := μ) (r n) (d n) d₀ (hd n) hd₀)
    simpa using ((hlim.sub_const d₀).abs.const_mul 3)
  simpa only [sub_add_cancel, zero_add] using
    hzero.add (capValue_tendsto_of_growing_cutoff (μ := μ) r hr d₀ hd₀)

end Erdos1017.CappedModel
