module

public import Erdos1017.Models.Capped.CappedAveraging
public import Erdos1017.Models.Decorated.DecoratedSamplingMoments
public import Erdos1017.Models.Decorated.DecoratedCountingIntegration
public import Erdos1017.SelectedModel.Selection.NonnegativeDualBound
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Half bound for nonnegative-color models

Full feasibility with nonnegative conditional colors implies that the capped
charge plus the density is at most one half, by transferring subclique tests and
dual feasibility to finite color samples; conditional averaging extends this to
nonnegative charge moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every imposed subclique test transfers to the unconditional sampled color law. -/
theorem ae_sampled_all_subclique_tests (W : Model Ω μ)
    (hW : ∀ r, Feasible r W) (n : ℕ) :
    ∀ᵐ c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)),
      ∀ k, 2 ≤ k → k ≤ n → ∀ e : Fin k ↪o Fin n,
        violation (fun p => c (pairEmbedding e p)) = 0 := by
  simp only [ae_all_iff]
  intro k hk hkn e
  have hrestr : Continuous (fun c : CliquePair n → CappedColor =>
      fun p : CliquePair k => c (pairEmbedding e p)) :=
    continuous_pi (fun p => continuous_apply (pairEmbedding e p))
  have hmeas : MeasurableSet {c : CliquePair n → CappedColor |
      violation (fun p => c (pairEmbedding e p)) = 0} :=
    measurableSet_eq_fun ((continuous_violation k).comp hrestr).measurable measurable_const
  apply Measure.ae_comp_of_ae_ae hmeas
  filter_upwards [ae_all_subclique_tests W (hW n) n] with x hx
  filter_upwards [hx] with c hc
  exact hc k hk hkn e

/-- Actual kernel charge nonnegativity transfers to every sampled pair. -/
theorem ae_sampled_charge_nonneg (W : Model Ω μ)
    (hcharge : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p, 0 ≤ CappedColor.charge z)
    (n : ℕ) :
    ∀ᵐ c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)),
      ∀ e : CliquePair n, 0 ≤ CappedColor.charge (c e) := by
  simp only [ae_all_iff]
  intro e
  have hpair :=
    (DecoratedCounting.measurePreserving_pairProjection (μ := μ) e.val.1 e.val.2
      e.property.ne).quasiMeasurePreserving.ae hcharge
  have hmeas : MeasurableSet {c : CliquePair n → CappedColor |
      0 ≤ CappedColor.charge (c e)} :=
    (isClosed_le continuous_const
      (CappedColor.continuous_charge.comp (continuous_apply e))).measurableSet
  apply Measure.ae_comp_of_ae_ae hmeas
  filter_upwards [hpair] with x hx
  change ∀ᵐ c ∂Measure.pi (fun p : CliquePair n =>
    W.kernel (x p.val.1, x p.val.2)), 0 ≤ CappedColor.charge (c e)
  exact (measurePreserving_eval (fun p : CliquePair n =>
    W.kernel (x p.val.1, x p.val.2)) e).quasiMeasurePreserving.ae hx

theorem chargeMatrix_nonneg_of_all {n : ℕ} (c : CliquePair n → CappedColor)
    (hc : ∀ e, 0 ≤ CappedColor.charge (c e)) (i j : Fin n) :
    0 ≤ chargeMatrix c i j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [chargeMatrix, pairColor_lt c i j hij]
    exact hc _
  · rw [chargeMatrix_self]
  · rw [chargeMatrix_symm, chargeMatrix, pairColor_lt c j i hji]
    exact hc _

/-- Full capped feasibility transfers to a feasible finite graph dual on the sample. -/
theorem ae_sampled_configuration_dualFeasible (W : Model Ω μ)
    (hW : ∀ r, Feasible r W) (n : ℕ) :
    ∀ᵐ c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)),
      WeightedGraph.DualFeasible (configurationGraph c) (chargeMatrix c) := by
  filter_upwards [ae_sampled_all_subclique_tests W hW n] with c hc
  exact configuration_dualFeasible c hc

theorem sampleCharge_eq_uniform_objective {n : ℕ} (c : CliquePair n → CappedColor) :
    sampleCharge c = WeightedGraph.objective (fun _ : Fin n => (1 : ℝ) / n)
      (chargeMatrix c) := by
  rw [WeightedGraph.objective_div, chargeMatrix_objective]
  rfl

theorem sampleDensity_eq_uniform_density {n : ℕ} (c : CliquePair n → CappedColor) :
    sampleDensity c = WeightedGraph.density (configurationGraph c)
      (fun _ : Fin n => (1 : ℝ) / n) := by
  rw [WeightedGraph.density, WeightedGraph.objective_div,
    WeightedGraph.adjacency_objective, ← configuration_adjacency_sum]
  rfl

/-- The finite weighted bound applies to each actual feasible nonnegative sample. -/
theorem sampleCharge_add_sampleDensity_le_half {n : ℕ}
    (c : CliquePair n → CappedColor) (hn : 0 < n)
    (hdual : WeightedGraph.DualFeasible (configurationGraph c) (chargeMatrix c))
    (hcharge : ∀ e, 0 ≤ CappedColor.charge (c e)) :
    sampleCharge c + sampleDensity c ≤ 1 / 2 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ∀ i : Fin n, 0 ≤ (1 : ℝ) / n := fun _ => div_nonneg (by norm_num) hnreal.le
  have hsum : (∑ _ : Fin n, (1 : ℝ) / n) = 1 := by
    simp [div_eq_mul_inv, hnreal.ne']
  rw [sampleCharge_eq_uniform_objective, sampleDensity_eq_uniform_density]
  exact WeightedGraph.nonnegative_dual_objective_add_density_le_half
    (configurationGraph c) (chargeMatrix c) hdual
    (chargeMatrix_nonneg_of_all c hcharge) _ hw hsum

/-- The actual finite color sample gives the bound with its exact finite-size bias. -/
theorem sampled_nonnegative_bound (W : Model Ω μ)
    (hW : ∀ r, Feasible r W)
    (hcharge : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p, 0 ≤ CappedColor.charge z)
    (n : ℕ) (hn : 0 < n) :
    (1 - 1 / (n : ℝ)) * (objective W + density W) ≤ 1 / 2 := by
  let C : C(CliquePair n → CappedColor, ℝ) :=
    ⟨sampleCharge, by unfold sampleCharge; fun_prop⟩
  let A : C(CliquePair n → CappedColor, ℝ) :=
    ⟨sampleDensity, by unfold sampleDensity; fun_prop⟩
  have hC : Integrable C (sampledColorLaw W n : Measure _) :=
    Integrable.of_bound C.continuous.aestronglyMeasurable ‖C‖
      (Eventually.of_forall fun c => C.norm_coe_le_norm c)
  have hA : Integrable A (sampledColorLaw W n : Measure _) :=
    Integrable.of_bound A.continuous.aestronglyMeasurable ‖A‖
      (Eventually.of_forall fun c => A.norm_coe_le_norm c)
  have hsample : ∀ᵐ c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)),
      C c + A c ≤ 1 / 2 := by
    filter_upwards [ae_sampled_configuration_dualFeasible W hW n,
      ae_sampled_charge_nonneg W hcharge n] with c hdual hnonneg
    exact sampleCharge_add_sampleDensity_le_half c hn hdual hnonneg
  have h := integral_mono_ae (hC.add hA) (integrable_const _) hsample
  change (∫ c, C c + A c ∂(sampledColorLaw W n : Measure
    (CliquePair n → CappedColor))) ≤ _ at h
  rw [integral_add hC hA] at h
  change (∫ c, sampleCharge c ∂(sampledColorLaw W n : Measure
      (CliquePair n → CappedColor))) +
    (∫ c, sampleDensity c ∂(sampledColorLaw W n : Measure
      (CliquePair n → CappedColor))) ≤ _ at h
  rw [integral_sampleCharge W n hn, integral_sampleDensity W n hn] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  nlinarith

/-- Full feasibility and nonnegative actual conditional colors imply the
sharp half bound for the capped charge and density. -/
theorem full_nonnegative_objective_add_density_le_half (W : Model Ω μ)
    (hW : ∀ r, Feasible r W)
    (hcharge : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p, 0 ≤ CappedColor.charge z) :
    objective W + density W ≤ 1 / 2 := by
  have hlim : Tendsto (fun n : ℕ =>
      (1 - 1 / ((n + 1 : ℕ) : ℝ)) * (objective W + density W)) atTop
      (𝓝 (objective W + density W)) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_zero, one_mul] using
      (hone.sub hzero).mul_const (objective W + density W)
  apply le_of_tendsto hlim
  exact Eventually.of_forall (fun n =>
    sampled_nonnegative_bound W hW hcharge (n + 1) (Nat.succ_pos n))

/-- Conditional averaging turns nonnegative charge moments into an actual
nonnegative-color model without changing its objective or density. -/
theorem full_moment_nonnegative_objective_add_density_le_half (W : Model Ω μ)
    (hW : ∀ r, Feasible r W)
    (hcharge : ∀ᵐ p ∂μ.prod μ, 0 ≤ W.moment CappedColor.charge p) :
    objective W + density W ≤ 1 / 2 := by
  have hconditional : ∀ᵐ p ∂μ.prod μ, 0 ≤ conditionalCharge W p := by
    filter_upwards [hcharge] with p hp
    exact div_nonneg hp (adjacency_moment_mem W p).1
  have hcolors : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂(averaged W).kernel p, 0 ≤ CappedColor.charge c := by
    filter_upwards [hconditional] with p hp
    filter_upwards [averaged_deterministic W p] with c hc
    rw [hc]
    exact mul_nonneg hp (CappedColor.adjacency_mem c).1
  have h := full_nonnegative_objective_add_density_le_half (averaged W)
    (fun r => feasible_averaged W (hW r)) hcolors
  rwa [objective_averaged, density_averaged] at h

end Erdos1017.CappedModel
