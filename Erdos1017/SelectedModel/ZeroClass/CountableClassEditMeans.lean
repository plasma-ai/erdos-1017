module

public import Erdos1017.SelectedModel.ZeroClass.CountableClassEdits

/-!
# Means of countable class edits via prefixes

Color moments, adjacency means and signed charge means of the finite prefix
edits converge to those of the simultaneous class edit, so a common density or
objective of all prefixes is that of the global edit, and mean preservation by
every prefix transfers to the countable edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every fixed continuous color moment of the actual prefix edits
converges in integral to that of the actual simultaneous class edit. -/
theorem prefixClassEdit_moment_integral_tendsto
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1) (f : C(CappedColor, ℝ)) :
    Tendsto (fun N => ∫ p, (prefixClassEdit W t ht m hm N).moment f p ∂μ.prod μ) atTop
      (𝓝 (∫ p, (countableClassEdit W t ht m hm).moment f p ∂μ.prod μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro N
    exact ((prefixClassEdit W t ht m hm N).stronglyMeasurable_moment
      f.continuous.stronglyMeasurable).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    filter_upwards with p
    have h := norm_integral_le_of_norm_le_const (μ := (prefixClassEdit W t ht m hm N).kernel p)
      (Eventually.of_forall f.norm_coe_le_norm)
    simpa only [DecoratedKernel.moment, probReal_univ, mul_one] using h
  · filter_upwards with p
    have heq : (fun N => (prefixClassEdit W t ht m hm N).moment f p) =ᶠ[atTop]
        (fun _ => (countableClassEdit W t ht m hm).moment f p) := by
      filter_upwards [eventually_ge_atTop (max (t p.1).1 (t p.2).1)] with N hN
      unfold DecoratedKernel.moment
      rw [prefixClassEdit_kernel_eq W t ht m hm N p
        ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN)]
    exact (tendsto_congr' heq).mpr tendsto_const_nhds

/-- Actual adjacency means converge on the original common carrier. -/
theorem prefixClassEdit_density_tendsto
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1) :
    Tendsto (fun N => density (prefixClassEdit W t ht m hm N)) atTop
      (𝓝 (density (countableClassEdit W t ht m hm))) :=
  (prefixClassEdit_moment_integral_tendsto W t ht m hm
    ⟨CappedColor.adjacency, CappedColor.continuous_adjacency⟩).div_const 2

/-- Actual signed charge means converge on the original common carrier. -/
theorem prefixClassEdit_objective_tendsto
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1) :
    Tendsto (fun N => objective (prefixClassEdit W t ht m hm N)) atTop
      (𝓝 (objective (countableClassEdit W t ht m hm))) :=
  (prefixClassEdit_moment_integral_tendsto W t ht m hm
    ⟨CappedColor.charge, CappedColor.continuous_charge⟩).div_const 2

/-- A common density of all actual prefix edits is the global edit's
actual density. -/
theorem countableClassEdit_density_eq_of_prefix
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1) (d : ℝ)
    (hd : ∀ N, density (prefixClassEdit W t ht m hm N) = d) :
    density (countableClassEdit W t ht m hm) = d := by
  apply tendsto_nhds_unique (prefixClassEdit_density_tendsto W t ht m hm)
  simpa only [hd] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => d) atTop (𝓝 d))

/-- A common signed objective of all actual prefix edits is the global
edit's actual objective. -/
theorem countableClassEdit_objective_eq_of_prefix
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1) (c : ℝ)
    (hc : ∀ N, objective (prefixClassEdit W t ht m hm N) = c) :
    objective (countableClassEdit W t ht m hm) = c := by
  apply tendsto_nhds_unique (prefixClassEdit_objective_tendsto W t ht m hm)
  simpa only [hc] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))

/-- If every actual prefix preserves both original means, their actual
simultaneous countable edit preserves those same means. -/
theorem countableClassEdit_means_eq_of_prefix
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1)
    (hd : ∀ N, density (prefixClassEdit W t ht m hm N) = density W)
    (hc : ∀ N, objective (prefixClassEdit W t ht m hm N) = objective W) :
    density (countableClassEdit W t ht m hm) = density W ∧
      objective (countableClassEdit W t ht m hm) = objective W :=
  ⟨countableClassEdit_density_eq_of_prefix W t ht m hm (density W) hd,
    countableClassEdit_objective_eq_of_prefix W t ht m hm (objective W) hc⟩

end Erdos1017.CappedModel
