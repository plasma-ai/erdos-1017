module

public import Erdos1017.SelectedModel.Selection.FullIndexOneComparison
public import Erdos1017.Models.Selection.FullKernelSelection
public import Erdos1017.SelectedModel.Selection.FullMultiplierSigns
public import Erdos1017.SelectedModel.Capped.CappedSecondPositiveDirection
public import Erdos1017.Multipartite.BenchmarkSplitComparison
public import Erdos1017.Models.Selection.FullStationaryCompactness

/-!
# Pointwise structure of a strict benchmark gap

The structure `FullStrictGapStructure` records the consequences of a strict
benchmark gap for one stationary shifted kernel: positive index exactly two,
nonconstant degree and a positive mean-zero eigenvector, for every full
stationary-class member above the benchmark.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Constant degree is impossible above the benchmark for an actual full
optimum. Conditional averaging and the genuine full singular selection
construct the index-one comparison used in the contradiction. -/
theorem full_regular_of_strict_benchmark_gap (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hd : density W ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark (density W) < objective W) :
    Variation.weightFirstVariation (adjacencyOperator W) ≠ 0 := by
  intro hsingular
  let V := averaged W
  have hV : FullFeasible V := fullFeasible_averaged W hW
  have hdV : density V = density W := density_averaged W
  have hcV : objective V = objective W := objective_averaged W
  have hoptV : objective V = FractionalGraph.densityLimit (density V) := by
    rw [hcV, hdV]
    exact hopt
  have hdegree := (Variation.kernel_weightFirstVariation_eq_zero_iff (adjacencyKernel W)
    (by norm_num) (adjacencyKernel_measurable W) (adjacencyKernel_bound W)).mp hsingular
  have hadjacency : adjacencyKernel V = adjacencyKernel W := by
    funext x y
    exact adjacency_moment_averaged W (x, y)
  have hsingularV : Variation.weightFirstVariation (adjacencyOperator V) = 0 := by
    apply (Variation.kernel_weightFirstVariation_eq_zero_iff (adjacencyKernel V)
      (by norm_num) (adjacencyKernel_measurable V) (adjacencyKernel_bound V)).mpr
    simpa only [hadjacency] using hdegree
  have hd0V : 0 < density V := by rw [hdV]; linarith [hd.1]
  have hdhalfV : density V < 1 / 2 := hdV ▸ hd.2
  obtain ⟨m, ν, hm, _, _, hmem, hcomp, hrow, _, hfinite, hindex⟩ :=
    exists_full_singular_kernel V hV hoptV hsingularV hd0V hdhalfV
  have hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment V m p :=
    hmem.mono (fun _ h => h.1)
  have hexcess : 1 / 2 - density V < objective V := by
    rw [hdV, hcV]
    exact (Benchmark.benchmark_ge_missing ⟨hd.1.le, hd.2.le⟩).trans_lt hgap
  have hν := full_stationary_value_pos_of_complement_excess V hV m ν hexcess hdhalfV hnonneg hrow
  have hdet : ∀ p, ∀ᵐ c ∂V.kernel p,
      CappedColor.charge c = conditionalCharge V p * CappedColor.adjacency c := by
    intro p
    change ∀ᵐ c ∂(averaged W).kernel p,
      CappedColor.charge c = conditionalCharge (averaged W) p * CappedColor.adjacency c
    rw [conditionalCharge_averaged]
    exact averaged_deterministic W p
  have hbound := full_objective_le_benchmark_of_index_one V hV m ν hm hν hrow hnonneg hcomp
    (shiftedColor_deterministic_of_complementary V m hcomp hdet) hfinite hindex
  rw [hdV, hcV] at hbound
  exact (not_le_of_gt hgap) hbound

/-- Pointwise consequences of a genuine strict benchmark gap for one
recorded stationary shifted kernel. No uniform lower gap is included. -/
structure FullStrictGapStructure (W : Model Ω μ) (m ν : ℝ) : Prop where
  multiplier_neg : m < 0
  stationary_pos : 0 < ν
  index_eq_two : Module.finrank ℝ
    (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) = 2
  regular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0
  nonconstant_degree : ¬∃ a : ℝ, ∀ᵐ x ∂μ, (∫ y, adjacencyKernel W x y ∂μ) = a
  gamma_pos : 0 < ν + m
  strict_support : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
    if 0 < shiftedMoment W m p then 1 else 0
  positive_eigenvector : ∃ (w : Lp ℝ 2 μ) (σ : ℝ), w ≠ 0 ∧ (∫ x, w x ∂μ) = 0 ∧
    0 < σ ∧ shiftedOperator W m w = σ • w

/-- Actual full optimality, a strict benchmark gap and the recorded stationary
shifted-kernel data imply positive index exactly two, nonconstant degree, an actual
positive meanzero eigenvector, strict support and positive gamma. -/
theorem full_strict_gap_structure (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hd : density W ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark (density W) < objective W) (m ν : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p)
    (hfinite : FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)))
    (hindex : Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 2) :
    FullStrictGapStructure W m ν := by
  have hregular := full_regular_of_strict_benchmark_gap W hW hopt hd hgap
  have hexcess : 1 / 2 - density W < objective W :=
    (Benchmark.benchmark_ge_missing ⟨hd.1.le, hd.2.le⟩).trans_lt hgap
  have hmneg := full_multiplier_neg_of_complement_excess W hW m hexcess hnonneg
  have hν := full_stationary_value_pos_of_complement_excess W hW m ν hexcess hd.2 hnonneg hrow
  have htwo : 2 ≤ Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) := by
    by_contra hnot
    have hone : Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 1 := by
      omega
    exact (not_le_of_gt hgap)
      (full_objective_le_benchmark_of_index_one W hW m ν hm hν hrow hnonneg hcomp hdet hfinite hone)
  have : FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) := hfinite
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := exists_positive_meanzero_eigenvector W m ν hrow htwo
  refine ⟨hmneg, hν, by omega, hregular, ?_, ?_, ?_, w, σ, hw, hmean, hσ, heigen⟩
  · intro hconstant
    exact hregular ((Variation.kernel_weightFirstVariation_eq_zero_iff (adjacencyKernel W)
      (by norm_num) (adjacencyKernel_measurable W) (adjacencyKernel_bound W)).mpr hconstant)
  · exact full_gamma_pos_of_positive_eigenvector W hW hopt m ν hrow hregular hd.2
      w hw hmean σ hσ heigen
  · exact full_strict_support_of_positive_eigenvector W hW hopt m ν hrow hregular
      w hw hmean σ hσ heigen hnonneg hcomp

/-- Every actual full stationary-class member above the benchmark has the
pointwise strict-gap structure for its same recorded multiplier. -/
theorem FullStationaryClass.strict_gap_structure {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) : FullStrictGapStructure W m (2 * (c - m * d)) := by
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hdW : density W ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hW.density_eq ▸ hd
  have hgapW : benchmark (density W) < objective W := by
    rw [hW.density_eq, hW.objective_eq]
    exact hgap
  exact full_strict_gap_structure W hW.full hopt hdW hgapW m _ hW.multiplier_mem hW.stationary
    (hW.moment_mem.mono (fun _ h => h.1)) hW.complementary hW.deterministic
    hW.finite_positive hW.index_le_two

/-- The lower density endpoint is derived from the actual full objective:
below one quarter, both the full value and the benchmark equal the density. -/
theorem FullStationaryClass.strict_gap_structure_of_density_lt_half
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hdhalf : d < 1 / 2) (hgap : benchmark d < c) :
    FullStrictGapStructure W m (2 * (c - m * d)) := by
  have hquarter : 1 / 4 < d := by
    by_contra hnot
    have hdq : d ≤ 1 / 4 := not_lt.mp hnot
    have hd0 : 0 ≤ d := hW.density_eq ▸ (density_mem W).1
    have hvalue := FractionalGraph.densityLimit_eq_self d ⟨hd0, hdq⟩
    rw [hW.optimal, hvalue, benchmark_of_le_quarter hdq] at hgap
    exact (lt_irrefl d) hgap
  exact hW.strict_gap_structure ⟨hquarter, hdhalf⟩ hgap

end Erdos1017.CappedModel
