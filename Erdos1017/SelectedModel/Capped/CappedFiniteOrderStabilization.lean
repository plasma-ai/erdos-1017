module

public import Erdos1017.SelectedModel.Capped.CappedUniformGaps
public import Erdos1017.SelectedModel.Capped.CappedArityApplication

/-!
# Finite-order stabilization of the capped value

Uniform capped gaps and the finite-arity budget give one cutoff beyond which
every larger cap is fully feasible, so at a strict benchmark-gap density every
sufficiently large capped value equals `F`
(`exists_eventual_capValue_eq_densityLimit`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An actual selected capped maximizer beyond the explicit spectral budget
is fully feasible. Its strict support is derived from its actual capped
maximality, regularity and meanzero eigenvector. -/
theorem fullFeasible_of_selected_cap_gap_budget (W : Model Ω μ) (m ν g s : ℝ)
    (hg : 0 < g) (hs : 0 < s) {r : ℕ} (hdata : SelectedCapData r W m ν)
    (hgap : CapGapBounds W m ν g s)
    (hbudget : FiniteArity.Certificate.testBudget (Real.sqrt (8 + 32 / s)) g ≤ r) :
    FullFeasible W := by
  obtain ⟨w, σ, hw, hmean, hσ, hsσ, heigen⟩ := hgap.meanzero_eigenvector
  have hsupport := strict_support_of_positive_eigenvector W hdata.maximal m ν hdata.stationary
    hgap.regular w hw hmean σ hσ heigen (hdata.moment_mem.mono (fun _ h => h.1)) hdata.complementary
  exact (fullFeasible_of_explicit_spectral_budget W m ν g s hg hs
    ⟨hdata.multiplier_mem.1, hgap.multiplier_neg⟩ hgap.gamma_lower hsupport hdata.deterministic
    hdata.moment_mem hdata.stationary hdata.finite_positive hdata.index_le_two
    w hw hmean σ hsσ heigen hdata.maximal.1 hbudget).1

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]

/-- The actual capped optimum equals F once its actual selected maximizer
is made fully feasible by the proved spectral test budget. -/
theorem capValue_eq_densityLimit_of_selected_cap_gap_budget (W : Model Ω μ) (m ν g s : ℝ)
    (hg : 0 < g) (hs : 0 < s) {r : ℕ} (hdata : SelectedCapData r W m ν)
    (hgap : CapGapBounds W m ν g s)
    (hbudget : FiniteArity.Certificate.testBudget (Real.sqrt (8 + 32 / s)) g ≤ r) :
    capValue Ω μ r (density W) = FractionalGraph.densityLimit (density W) := by
  have hfull := fullFeasible_of_selected_cap_gap_budget W m ν g s hg hs hdata hgap hbudget
  have hobjective := objective_eq_capValue_of_isMaximizer W hdata.maximal
  apply le_antisymm
  · rw [← hobjective]
    exact fullFeasible_objective_le_densityLimit W hfull
  · exact densityLimit_le_capValue (μ := μ) r (density W) (density_mem W)

variable [StandardBorelSpace Ω] [MeasurableEq Ω]

omit [MeasurableEq Ω] in
/-- Capped attainment and the actual averaged selection construct a selected
cap record at every prescribed interior density and every imposed cutoff. -/
theorem exists_selected_cap_data_at_density (r : ℕ) (d : ℝ) (hd : d ∈ Ioo (0 : ℝ) (1 / 2)) :
    ∃ (W : Model Ω μ) (m ν : ℝ), SelectedCapData r W m ν ∧ density W = d := by
  obtain ⟨U, hU, hdU, _⟩ := exists_maximizer (μ := μ) r d ⟨hd.1.le, hd.2.le⟩
  obtain ⟨W, m, ν, hdW, _, hdata⟩ := exists_selected_cap_data U hU
    (by rw [hdU]; exact hd.1) (by rw [hdU]; exact hd.2)
  exact ⟨W, m, ν, hdata, hdW.trans hdU⟩

/-- Actual uniform capped gaps and the explicit finite-arity budget give
one cutoff that stabilizes every larger cap at every density in a compact
strict benchmark-gap set. No omitted clique test is assumed. -/
theorem exists_uniform_finite_order_stabilization (J : Set ℝ) (hJ : IsCompact J)
    (hdomain : J ⊆ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : ∀ d ∈ J, benchmark d < FractionalGraph.densityLimit d) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ r : ℕ, N ≤ r → ∀ d ∈ J,
      capValue Ω μ r d = FractionalGraph.densityLimit d := by
  obtain ⟨r₀, g, s, hg, hs, hbounds⟩ := exists_uniform_cap_gap_bounds (μ := μ) J hJ hdomain hgap
  let b := FiniteArity.Certificate.testBudget (Real.sqrt (8 + 32 / s)) g
  let N := max 2 (max r₀ b)
  refine ⟨N, le_max_left _ _, ?_⟩
  intro r hr d hdJ
  have hr₀ : r₀ ≤ r := (le_max_left r₀ b).trans ((le_max_right 2 (max r₀ b)).trans hr)
  have hbudget : b ≤ r := (le_max_right r₀ b).trans ((le_max_right 2 (max r₀ b)).trans hr)
  have hd : d ∈ Ioo (0 : ℝ) (1 / 2) := ⟨by linarith [(hdomain hdJ).1], (hdomain hdJ).2⟩
  obtain ⟨W, m, ν, hdata, hdW⟩ := exists_selected_cap_data_at_density (μ := μ) r d hd
  have hboundsW := hbounds r hr₀ W m ν hdata (hdW ▸ hdJ)
  have heq := capValue_eq_densityLimit_of_selected_cap_gap_budget W m ν g s hg hs hdata hboundsW hbudget
  simpa only [hdW] using heq

/-- At a genuine strict benchmark-gap density, every sufficiently large
actual capped value equals the full fractional density limit. -/
theorem exists_eventual_capValue_eq_densityLimit (d : ℝ)
    (hdomain : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < FractionalGraph.densityLimit d) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ r : ℕ, N ≤ r → capValue Ω μ r d = FractionalGraph.densityLimit d := by
  obtain ⟨N, hN, hstable⟩ := exists_uniform_finite_order_stabilization (μ := μ) ({d} : Set ℝ)
    isCompact_singleton
    (by intro x hx; simpa only [mem_singleton_iff.mp hx] using hdomain)
    (by intro x hx; simpa only [mem_singleton_iff.mp hx] using hgap)
  exact ⟨N, hN, fun r hr => hstable r hr d (mem_singleton d)⟩

/-- The actual finite-order equality required by physical primal attainment
is a consequence of stabilization, rather than an input to this theorem. -/
theorem exists_finite_order_equality (d : ℝ) (hdomain : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < FractionalGraph.densityLimit d) :
    ∃ N : ℕ, 2 ≤ N ∧ capValue Ω μ N d = FractionalGraph.densityLimit d := by
  obtain ⟨N, hN, hstable⟩ := exists_eventual_capValue_eq_densityLimit (μ := μ) d hdomain hgap
  exact ⟨N, hN, hstable N le_rfl⟩

/-- Physical admissibility and a genuine strict gap derive the lower
density endpoint automatically, since F and B agree below one quarter. -/
theorem exists_finite_order_equality_of_strict_gap (d : ℝ) (hd0 : 0 ≤ d) (hdhalf : d < 1 / 2)
    (hgap : benchmark d < FractionalGraph.densityLimit d) :
    ∃ N : ℕ, 2 ≤ N ∧ capValue Ω μ N d = FractionalGraph.densityLimit d := by
  have hquarter : 1 / 4 < d := by
    by_contra hnot
    have hdq : d ≤ 1 / 4 := not_lt.mp hnot
    rw [FractionalGraph.densityLimit_eq_self d ⟨hd0, hdq⟩, benchmark_of_le_quarter hdq] at hgap
    exact (lt_irrefl d) hgap
  exact exists_finite_order_equality (μ := μ) d ⟨hquarter, hdhalf⟩ hgap

end Erdos1017.CappedModel
