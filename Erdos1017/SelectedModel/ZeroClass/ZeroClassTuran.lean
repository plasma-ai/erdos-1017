module

public import Erdos1017.Models.Decorated.DecoratedSamplingMoments
public import Erdos1017.Models.Capped.CappedSubcliqueTests
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-!
# Turán bound from zero clique presence

This module defines the clique-presence indicator `cliquePresence` and shows
that zero expectation makes the sampled graph clique-free almost surely, so
finite Turán bounds the sampled edge count and zero sampled `(k+1)`-clique
density bounds the unhalved adjacency mean by `1 - 1/k`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The indicator that every pair in a sampled color configuration is present. -/
def cliquePresence {n : ℕ} (c : CliquePair n → CappedColor) : ℝ :=
  ∏ e, CappedColor.adjacency (c e)

@[fun_prop] theorem continuous_cliquePresence (n : ℕ) :
    Continuous (cliquePresence : (CliquePair n → CappedColor) → ℝ) := by
  unfold cliquePresence
  fun_prop

theorem cliquePresence_nonneg {n : ℕ} (c : CliquePair n → CappedColor) :
    0 ≤ cliquePresence c := by
  exact Finset.prod_nonneg (fun e _ => (CappedColor.adjacency_mem (c e)).1)

/-- A zero clique-presence expectation makes every selected subclique
absent almost surely in the actual unconditional finite color law. -/
theorem ae_sampled_zero_subcliques (W : Model Ω μ) (k n : ℕ)
    (hzero : (∫ c, cliquePresence c
      ∂(sampledColorLaw W (k + 1) : Measure (CliquePair (k + 1) → CappedColor))) = 0) :
    ∀ᵐ c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)),
      ∀ e : Fin (k + 1) ↪o Fin n,
        cliquePresence (fun p => c (pairEmbedding e p)) = 0 := by
  have hbase : ∀ᵐ c ∂(sampledColorLaw W (k + 1) :
      Measure (CliquePair (k + 1) → CappedColor)), cliquePresence c = 0 := by
    exact (integral_eq_zero_iff_of_nonneg cliquePresence_nonneg
      ((continuous_cliquePresence (k + 1)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).mp hzero
  apply ae_all_iff.mpr
  intro e
  have hrestr : Continuous (fun c : CliquePair n → CappedColor =>
      fun p : CliquePair (k + 1) => c (pairEmbedding e p)) :=
    continuous_pi (fun p => continuous_apply (pairEmbedding e p))
  have hmeas : MeasurableSet {c : CliquePair n → CappedColor |
      cliquePresence (fun p => c (pairEmbedding e p)) = 0} :=
    measurableSet_eq_fun ((continuous_cliquePresence (k + 1)).comp hrestr).measurable
      measurable_const
  apply Measure.ae_comp_of_ae_ae hmeas
  have hlatent := Measure.ae_ae_of_ae_comp
    (κ := cliqueKernel W (k + 1)) (μ := Measure.pi (fun _ : Fin (k + 1) => μ)) hbase
  have hsel := (FiniteArity.measurePreserving_subtuple μ e.toEmbedding).quasiMeasurePreserving.ae
    hlatent
  filter_upwards [hsel] with x hx
  exact (measurePreserving_cliqueRestriction W x e).quasiMeasurePreserving.ae hx

/-- The actual finite sampled graph is clique-free almost surely when the
unconditional forbidden-clique presence test has zero expectation. -/
theorem ae_sampled_cliqueFree (W : Model Ω μ) (k n : ℕ)
    (hzero : (∫ c, cliquePresence c
      ∂(sampledColorLaw W (k + 1) : Measure (CliquePair (k + 1) → CappedColor))) = 0) :
    ∀ᵐ c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)),
      (configurationGraph c).CliqueFree (k + 1) := by
  classical
  filter_upwards [ae_sampled_zero_subcliques W k n hzero] with c hc
  intro S hS
  let e : Fin (k + 1) ↪o Fin n := S.orderEmbOfFin hS.2
  have hpair (p : CliquePair (k + 1)) :
      CappedColor.adjacency (c (pairEmbedding e p)) = 1 := by
    have h := hS.1 (S.orderEmbOfFin_mem hS.2 p.val.1)
      (S.orderEmbOfFin_mem hS.2 p.val.2) (e.strictMono p.property).ne
    change CappedColor.adjacency (pairColor c (e p.val.1) (e p.val.2)) = 1 at h
    rwa [pairColor_lt _ _ _ (e.strictMono p.property)] at h
  have hone : cliquePresence (fun p => c (pairEmbedding e p)) = 1 := by
    simp [cliquePresence, hpair]
  exact one_ne_zero (hone.symm.trans (hc e))

/-- Finite Turán bounds the normalized edge count of each actual
clique-free sampled graph, including samples with at most `k` vertices. -/
theorem sampleDensity_le_turan {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (c : CliquePair n → CappedColor)
    (hfree : (configurationGraph c).CliqueFree (k + 1)) :
    sampleDensity c ≤ (1 - 1 / (k : ℝ)) / 2 := by
  classical
  have he : (configurationGraph c).edgeSet.ncard =
      (configurationGraph c).edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hcount : (configurationGraph c).edgeSet.ncard ≤
      SimpleGraph.turanNumber n k := by
    rw [he]
    simpa using hfree.card_edgeFinset_le
  have hnat : 2 * k * (configurationGraph c).edgeSet.ncard ≤
      (k - 1) * n ^ 2 :=
    (Nat.mul_le_mul_left (2 * k) hcount).trans SimpleGraph.mul_turanNumber_le
  have hreal : (2 : ℝ) * k * (configurationGraph c).edgeSet.ncard ≤
      ((k : ℝ) - 1) * (n : ℝ) ^ 2 := by
    have hcast : ((2 * k * (configurationGraph c).edgeSet.ncard : ℕ) : ℝ) ≤
        (((k - 1) * n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_sub hk,
      Nat.cast_succ, Nat.cast_zero, zero_add] using hcast
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  rw [sampleDensity, configuration_adjacency_sum]
  rw [div_le_iff₀ (sq_pos_of_pos hnreal)]
  have hden : (1 - 1 / (k : ℝ)) / 2 * (n : ℝ) ^ 2 =
      ((k : ℝ) - 1) * (n : ℝ) ^ 2 / (2 * k) := by
    field_simp
  rw [hden]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)).2
  nlinarith [hreal]

/-- Finite samples satisfy the Turán bound in expectation with the exact
diagonal bias from sampling `n` independent latent vertices. -/
theorem sampled_density_le_turan (W : Model Ω μ) (k n : ℕ)
    (hk : 0 < k) (hn : 0 < n)
    (hzero : (∫ c, cliquePresence c
      ∂(sampledColorLaw W (k + 1) : Measure (CliquePair (k + 1) → CappedColor))) = 0) :
    (1 - 1 / (n : ℝ)) * density W ≤ (1 - 1 / (k : ℝ)) / 2 := by
  let A : C(CliquePair n → CappedColor, ℝ) :=
    ⟨sampleDensity, by unfold sampleDensity; fun_prop⟩
  have hA : Integrable A (sampledColorLaw W n : Measure _) :=
    Integrable.of_bound A.continuous.aestronglyMeasurable ‖A‖
      (Filter.Eventually.of_forall fun c => A.norm_coe_le_norm c)
  have hsample : ∀ᵐ c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)),
      A c ≤ (1 - 1 / (k : ℝ)) / 2 := by
    filter_upwards [ae_sampled_cliqueFree W k n hzero] with c hc
    exact sampleDensity_le_turan hn hk c hc
  have h := integral_mono_ae hA (integrable_const _) hsample
  change (∫ c, sampleDensity c ∂(sampledColorLaw W n :
    Measure (CliquePair n → CappedColor))) ≤ _ at h
  rw [integral_sampleDensity W n hn] at h
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

/-- Zero sampled `(k+1)`-clique density bounds the unhalved adjacency
mean by the Turán constant `1-1/k`. -/
theorem density_le_turan_of_zero_clique (W : Model Ω μ) (k : ℕ) (hk : 0 < k)
    (hzero : (∫ c, cliquePresence c
      ∂(sampledColorLaw W (k + 1) : Measure (CliquePair (k + 1) → CappedColor))) = 0) :
    2 * density W ≤ 1 - 1 / (k : ℝ) := by
  have hlim : Filter.Tendsto (fun n : ℕ =>
      (1 - 1 / ((n + 1 : ℕ) : ℝ)) * density W) Filter.atTop
      (nhds (density W)) := by
    have hzero' : Filter.Tendsto (fun n : ℕ =>
        (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [sub_zero, one_mul] using (hone.sub hzero').mul_const (density W)
  have hbound : density W ≤ (1 - 1 / (k : ℝ)) / 2 :=
    le_of_tendsto hlim (Filter.Eventually.of_forall fun n =>
      sampled_density_le_turan W k (n + 1) hk (Nat.succ_pos n) hzero)
  linarith

end Erdos1017.CappedModel
