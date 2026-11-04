module

public import Erdos1017.SelectedModel.MultipartiteValue.FractionalMultipartiteComparison
public import Erdos1017.SelectedModel.Selection.FullNonnegativeBound
public import Erdos1017.Models.Capped.CappedGrowingLimit
public import Erdos1017.Benchmark.BenchmarkContinuity
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Benchmark bound for models with multipartite support

A fully feasible decorated model whose finite sampled graphs are almost surely
complete multipartite satisfies the benchmark, by finite weak duality and
convergence of the expected sampled benchmark; deterministic partition support
gives this almost surely (`objective_le_benchmark_of_partition_support`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Erdos1017.CappedModel

/-- Every actual color sample has density in the original benchmark domain,
including the empty sample. -/
theorem sampleDensity_mem {n : ℕ} (c : CliquePair n → CappedColor) :
    sampleDensity c ∈ Icc (0 : ℝ) (1 / 2) := by
  have hnonneg : 0 ≤ ∑ e, CappedColor.adjacency (c e) :=
    Finset.sum_nonneg (fun e _ => (CappedColor.adjacency_mem (c e)).1)
  refine ⟨div_nonneg hnonneg (sq_nonneg _), ?_⟩
  by_cases hn : n = 0
  · subst n
    simp [sampleDensity]
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsum : (∑ e, CappedColor.adjacency (c e)) ≤ (n.choose 2 : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, card_cliquePair, nsmul_eq_mul, mul_one] using
      (Finset.sum_le_sum (s := Finset.univ) (fun e _ => (CappedColor.adjacency_mem (c e)).2))
  have hchoose := Nat.cast_choose_two ℝ n
  unfold sampleDensity
  apply (div_le_iff₀ (sq_pos_of_pos hnreal)).mpr
  nlinarith

/-- The benchmark of the actual sampled graph density is a continuous
finite-color observable, despite the benchmark's piecewise definition. -/
theorem continuous_sampleBenchmark (n : ℕ) :
    Continuous (fun c : CliquePair n → CappedColor => benchmark (sampleDensity c)) :=
  benchmark_continuousOn.comp_continuous
    (by unfold sampleDensity; fun_prop) sampleDensity_mem

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual sampled benchmark observable is integrable for every order. -/
theorem integrable_sampleBenchmark (W : Model Ω μ) (n : ℕ) :
    Integrable (fun c => benchmark (sampleDensity c))
      (sampledColorLaw W n : Measure (CliquePair n → CappedColor)) := by
  let B : C(CliquePair n → CappedColor, ℝ) := ⟨_, continuous_sampleBenchmark n⟩
  exact Integrable.of_bound B.continuous.aestronglyMeasurable ‖B‖
    (Eventually.of_forall fun c => B.norm_coe_le_norm c)

private theorem benchmark_error_affine_bound {d : ℝ} (hd : d ∈ Icc (0 : ℝ) (1 / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ Icc (0 : ℝ) (1 / 2),
      |benchmark x - benchmark d| ≤ ε + K * |x - d| := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous benchmark_continuousOn
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn benchmark_continuousOn
  let C := max 1 (2 * M)
  have hC : 0 ≤ C := le_trans zero_le_one (le_max_left _ _)
  refine ⟨C / δ, div_nonneg hC hδ.le, ?_⟩
  intro x hx
  by_cases hxd : |x - d| < δ
  · have hsmall : |benchmark x - benchmark d| < ε := by
      simpa only [Real.dist_eq] using hclose x hx d hd (by simpa only [Real.dist_eq] using hxd)
    exact hsmall.le.trans (le_add_of_nonneg_right (mul_nonneg (div_nonneg hC hδ.le) (abs_nonneg _)))
  · have hδx : δ ≤ |x - d| := le_of_not_gt hxd
    have hbound : |benchmark x - benchmark d| ≤ C := by
      calc
        _ ≤ |benchmark x| + |benchmark d| := abs_sub _ _
        _ ≤ M + M := add_le_add (by simpa only [Real.norm_eq_abs] using hM x hx)
          (by simpa only [Real.norm_eq_abs] using hM d hd)
        _ ≤ C := by dsimp [C]; linarith [le_max_right (1 : ℝ) (2 * M)]
    have hlinear : C ≤ C / δ * |x - d| := by
      calc
        C = C / δ * δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hδx (div_nonneg hC hδ.le)
    linarith

/-- Actual sampled benchmark errors vanish by actual density concentration
and the proved continuity of the original benchmark on its compact domain. -/
theorem sampleBenchmark_abs_error_tendsto (W : Model Ω μ) :
    Tendsto (fun n => ∫ c : CliquePair n → CappedColor,
      |benchmark (sampleDensity c) - benchmark (density W)|
        ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK, hpoint⟩ := benchmark_error_affine_bound (density_mem W) (half_pos hε)
  have hlim := (sampleDensity_abs_error_tendsto W).const_mul K
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  let ν := sampledColorLaw W n
  let F : C(CliquePair n → CappedColor, ℝ) :=
    ⟨fun c => |benchmark (sampleDensity c) - benchmark (density W)|,
      (continuous_sampleBenchmark n |>.sub continuous_const).abs⟩
  let E : C(CliquePair n → CappedColor, ℝ) :=
    ⟨fun c => |sampleDensity c - density W|, by unfold sampleDensity; fun_prop⟩
  have hF : Integrable F (ν : Measure _) := Integrable.of_bound
    F.continuous.aestronglyMeasurable ‖F‖ (Eventually.of_forall fun c => F.norm_coe_le_norm c)
  have hE : Integrable E (ν : Measure _) := Integrable.of_bound
    E.continuous.aestronglyMeasurable ‖E‖ (Eventually.of_forall fun c => E.norm_coe_le_norm c)
  have hupper : (∫ c, F c ∂(ν : Measure _)) ≤ ε / 2 + K * ∫ c, E c ∂(ν : Measure _) := by
    calc
      _ ≤ ∫ c, ε / 2 + K * E c ∂(ν : Measure _) := by
        apply integral_mono hF ((integrable_const _).add (hE.const_mul K))
        exact fun c => hpoint (sampleDensity c) (sampleDensity_mem c)
      _ = _ := by
        rw [integral_add (integrable_const _) (hE.const_mul K), integral_const_mul]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hsmall : K * (∫ c, E c ∂(ν : Measure _)) < ε / 2 := by
    have h := hN n hn
    rw [Real.dist_eq, mul_zero, sub_zero] at h
    exact (le_abs_self _).trans_lt h
  have hnonneg : 0 ≤ ∫ c, F c ∂(ν : Measure _) :=
    integral_nonneg (fun c => abs_nonneg _)
  change |(∫ c, F c ∂(ν : Measure _)) - 0| < ε
  rw [sub_zero, abs_of_nonneg hnonneg]
  linarith

/-- The expected benchmark of the actual finite sample converges to the
benchmark at the actual model density, with no supplied convergence premise. -/
theorem integral_sampleBenchmark_tendsto (W : Model Ω μ) :
    Tendsto (fun n => ∫ c : CliquePair n → CappedColor, benchmark (sampleDensity c)
      ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)))
      atTop (𝓝 (benchmark (density W))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (sampleBenchmark_abs_error_tendsto W) ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hsmall := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at hsmall
  rw [Real.dist_eq]
  have hrewrite : (∫ c, benchmark (sampleDensity c)
      ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) - benchmark (density W) =
      ∫ c, benchmark (sampleDensity c) - benchmark (density W)
        ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)) := by
    rw [integral_sub (integrable_sampleBenchmark W n) (integrable_const _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [hrewrite]
  exact abs_integral_le_integral_abs.trans_lt hsmall

/-- Actual finite dual weak duality and the actual complete multipartite
graph theorem apply directly to each fully tested sampled configuration. -/
theorem sampleCharge_le_benchmark {n : ℕ} (c : CliquePair n → CappedColor) (hn : 0 < n)
    (hdual : WeightedGraph.DualFeasible (configurationGraph c) (chargeMatrix c))
    (hMP : (configurationGraph c).IsCompleteMultipartite) :
    sampleCharge c ≤ benchmark (sampleDensity c) := by
  have hweak := WeightedGraph.dual_objective_le_value (configurationGraph c) (chargeMatrix c) hdual
  rw [chargeMatrix_objective] at hweak
  have hfinite := FractionalMultipartite.normalized_value_le_benchmark (configurationGraph c) hn hMP
  rw [← configuration_adjacency_sum c] at hfinite
  exact (div_le_div_of_nonneg_right hweak (sq_nonneg (n : ℝ))).trans hfinite

/-- A fully feasible actual decorated model whose actual finite sampled
graphs are almost surely complete multipartite satisfies the benchmark. -/
theorem objective_le_benchmark_of_sampled_multipartite (W : Model Ω μ) (hW : FullFeasible W)
    (hMP : ∀ n : ℕ, ∀ᵐ c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)),
      (configurationGraph c).IsCompleteMultipartite) :
    objective W ≤ benchmark (density W) := by
  have hbias : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbound : ∀ᶠ n : ℕ in atTop,
      (1 - 1 / (n : ℝ)) * objective W ≤
        ∫ c, benchmark (sampleDensity c)
          ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let C : C(CliquePair n → CappedColor, ℝ) := ⟨sampleCharge, by unfold sampleCharge; fun_prop⟩
    have hC : Integrable C (sampledColorLaw W n : Measure _) := Integrable.of_bound
      C.continuous.aestronglyMeasurable ‖C‖ (Eventually.of_forall fun c => C.norm_coe_le_norm c)
    have hsample : ∀ᵐ c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)),
        C c ≤ benchmark (sampleDensity c) := by
      filter_upwards [ae_sampled_configuration_dualFeasible W hW n, hMP n] with c hc hmp
      exact sampleCharge_le_benchmark c (by omega) hc hmp
    have h := integral_mono_ae hC (integrable_sampleBenchmark W n) hsample
    change (∫ c, sampleCharge c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) ≤ _ at h
    rwa [integral_sampleCharge W n (by omega)] at h
  simpa using le_of_tendsto_of_tendsto (hbias.mul_const (objective W))
    (integral_sampleBenchmark_tendsto W) hbound

/-- A deterministic partition of the sampled vertices into independent
classes supplies the actual complete multipartite graph predicate. -/
theorem configurationGraph_isCompleteMultipartite_of_partMap {n : ℕ}
    (c : CliquePair n → CappedColor) {ι : Type*} (π : Fin n → ι)
    (hpart : ∀ i j, (configurationGraph c).Adj i j ↔ π i ≠ π j) :
    (configurationGraph c).IsCompleteMultipartite := by
  constructor
  intro i j k hij hjk
  simp only [hpart, not_ne_iff] at hij hjk ⊢
  exact hij.trans hjk

/-- Being complete multipartite is a measurable property of the actual
finite sampled color configuration. -/
theorem measurableSet_configuration_multipartite (n : ℕ) :
    MeasurableSet {c : CliquePair n → CappedColor |
      (configurationGraph c).IsCompleteMultipartite} := by
  have hadj (i j : Fin n) : MeasurableSet {c : CliquePair n → CappedColor |
      (configurationGraph c).Adj i j} := by
    have hcolor : Continuous (fun c : CliquePair n → CappedColor => pairColor c i j) := by
      unfold pairColor
      split_ifs <;> fun_prop
    exact measurableSet_eq_fun (CappedColor.continuous_adjacency.comp hcolor).measurable measurable_const
  simp only [SimpleGraph.IsCompleteMultipartite, isTrans_def, imp_iff_not_or, not_not,
    ofPred_forall, ofPred_or]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    MeasurableSet.iInter (fun k => (hadj i j).union ((hadj j k).union (hadj i k).compl))))

/-- Actual conditional adjacency supported on the inequality of partition
labels makes every actual sampled graph complete multipartite almost surely.
The labels may form any type; their measurability is not needed separately
because the actual pair-support assertion is supplied almost everywhere. -/
theorem ae_sampled_multipartite_of_partition_support (W : Model Ω μ) {ι : Type*} (π : Ω → ι)
    (hpart : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p,
      CappedColor.adjacency z = 1 ↔ π p.1 ≠ π p.2) (n : ℕ) :
    ∀ᵐ c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)),
      (configurationGraph c).IsCompleteMultipartite := by
  have hpairs : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), ∀ e : CliquePair n,
      ∀ᵐ z ∂W.kernel (x e.val.1, x e.val.2),
        CappedColor.adjacency z = 1 ↔ π (x e.val.1) ≠ π (x e.val.2) := by
    simp only [ae_all_iff]
    intro e
    exact (DecoratedCounting.measurePreserving_pairProjection (μ := μ) e.val.1 e.val.2
      e.property.ne).quasiMeasurePreserving.ae hpart
  apply Measure.ae_comp_of_ae_ae (measurableSet_configuration_multipartite n)
  filter_upwards [hpairs] with x hx
  have hcolors : ∀ᵐ c ∂cliqueLaw W x, ∀ e : CliquePair n,
      CappedColor.adjacency (c e) = 1 ↔ π (x e.val.1) ≠ π (x e.val.2) := by
    simp only [ae_all_iff]
    intro e
    exact (measurePreserving_eval (fun e : CliquePair n =>
      W.kernel (x e.val.1, x e.val.2)) e).quasiMeasurePreserving.ae (hx e)
  filter_upwards [hcolors] with c hc
  apply configurationGraph_isCompleteMultipartite_of_partMap c (π ∘ x)
  intro i j
  change CappedColor.adjacency (pairColor c i j) = 1 ↔ π (x i) ≠ π (x j)
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [pairColor_lt c i j hij]
    exact hc ⟨(i, j), hij⟩
  · simp
  · rw [pairColor_symm, pairColor_lt c j i hji]
    exact (hc ⟨(j, i), hji⟩).trans ne_comm

/-- Full feasibility and actual deterministic multipartite partition
support imply the original benchmark comparison for the actual model. -/
theorem objective_le_benchmark_of_partition_support (W : Model Ω μ) (hW : FullFeasible W)
    {ι : Type*} (π : Ω → ι)
    (hpart : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p,
      CappedColor.adjacency z = 1 ↔ π p.1 ≠ π p.2) :
    objective W ≤ benchmark (density W) :=
  objective_le_benchmark_of_sampled_multipartite W hW
    (ae_sampled_multipartite_of_partition_support W π hpart)

end Erdos1017.CappedModel
