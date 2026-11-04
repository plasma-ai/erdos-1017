module

public import Erdos1017.Models.Decorated.DecoratedSamplingMoments
public import Erdos1017.Models.Capped.CappedDensityRestoration
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Concentration of the sampled density

Only overlapping pairs, whose number is cubic, contribute to the second moment
beyond the independent-pair value, so the sampled density of a colored sample
has uniformly vanishing mean squared and expected absolute error.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Two unordered pairs overlap when their sampled latent vertices share an index. -/
def pairOverlap {n : ℕ} (e f : CliquePair n) : Prop :=
  e.val.1 = f.val.1 ∨ e.val.1 = f.val.2 ∨ e.val.2 = f.val.1 ∨ e.val.2 = f.val.2

instance {n : ℕ} : DecidableRel (pairOverlap (n := n)) := fun e f => by
  unfold pairOverlap
  infer_instance

private theorem card_left_endpoint (n : ℕ) (v : Fin n) :
    ((Finset.univ : Finset (CliquePair n)).filter (fun f => f.val.1 = v)).card ≤ n := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (CliquePair n)).filter (fun f => f.val.1 = v))
    (t := Finset.univ) (fun f : CliquePair n => f.val.2)
    (by intro f hf; simp)
    (by
      intro f hf g hg h
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp hf).2.trans (Finset.mem_filter.mp hg).2.symm
      · exact h)
  simpa using h

private theorem card_right_endpoint (n : ℕ) (v : Fin n) :
    ((Finset.univ : Finset (CliquePair n)).filter (fun f => f.val.2 = v)).card ≤ n := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (CliquePair n)).filter (fun f => f.val.2 = v))
    (t := Finset.univ) (fun f : CliquePair n => f.val.1)
    (by intro f hf; simp)
    (by
      intro f hf g hg h
      apply Subtype.ext
      apply Prod.ext
      · exact h
      · exact (Finset.mem_filter.mp hf).2.trans (Finset.mem_filter.mp hg).2.symm)
  simpa using h

/-- For each pair, at most four vertex-coordinate classes can overlap it. -/
theorem card_overlap_le (n : ℕ) (e : CliquePair n) :
    ((Finset.univ : Finset (CliquePair n)).filter (pairOverlap e)).card ≤ 4 * n := by
  classical
  let A := (Finset.univ : Finset (CliquePair n)).filter (fun f => f.val.1 = e.val.1)
  let B := (Finset.univ : Finset (CliquePair n)).filter (fun f => f.val.2 = e.val.1)
  let C := (Finset.univ : Finset (CliquePair n)).filter (fun f => f.val.1 = e.val.2)
  let D := (Finset.univ : Finset (CliquePair n)).filter (fun f => f.val.2 = e.val.2)
  have hsub : (Finset.univ : Finset (CliquePair n)).filter (pairOverlap e) ⊆
      A ∪ B ∪ C ∪ D := by
    intro f hf
    rcases (Finset.mem_filter.mp hf).2 with h | h | h | h
    · simp [A, h.symm]
    · simp [B, h.symm]
    · simp [C, h.symm]
    · simp [D, h.symm]
  have hA : A.card ≤ n := card_left_endpoint n e.val.1
  have hB : B.card ≤ n := card_right_endpoint n e.val.1
  have hC : C.card ≤ n := card_left_endpoint n e.val.2
  have hD : D.card ≤ n := card_right_endpoint n e.val.2
  have hcard := Finset.card_le_card hsub
  have hAB := Finset.card_union_le A B
  have hABC := Finset.card_union_le (A ∪ B) C
  have hABCD := Finset.card_union_le (A ∪ B ∪ C) D
  omega

/-- The number of ordered pairs of sampled edges sharing a vertex is cubic. -/
theorem overlap_count_le (n : ℕ) :
    (∑ e : CliquePair n,
      ((Finset.univ : Finset (CliquePair n)).filter (pairOverlap e)).card) ≤ 4 * n ^ 3 := by
  classical
  have hcard : Fintype.card (CliquePair n) ≤ n * n := by
    have h := Fintype.card_subtype_le
      (fun p : Fin n × Fin n => p.1 < p.2)
    simpa using h
  calc
    (∑ e : CliquePair n,
      ((Finset.univ : Finset (CliquePair n)).filter (pairOverlap e)).card) ≤
        ∑ _e : CliquePair n, 4 * n :=
      Finset.sum_le_sum (fun e _ => card_overlap_le n e)
    _ = Fintype.card (CliquePair n) * (4 * n) := by simp
    _ ≤ (n * n) * (4 * n) := Nat.mul_le_mul_right _ hcard
    _ = 4 * n ^ 3 := by ring

/-- The second moment differs from the independent-pair value only on overlapping pairs. -/
theorem integral_adjacency_sum_sq_le (W : Model Ω μ) (n : ℕ) :
    (∫ c : CliquePair n → CappedColor,
      (∑ e : CliquePair n, CappedColor.adjacency (c e)) ^ 2
        ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) ≤
      (Fintype.card (CliquePair n) : ℝ) ^ 2 *
        (∫ p, W.moment CappedColor.adjacency p ∂μ.prod μ) ^ 2 + (4 * n ^ 3 : ℕ) := by
  let ν := sampledColorLaw W n
  let m : ℝ := ∫ p, W.moment CappedColor.adjacency p ∂μ.prod μ
  have hint (e f : CliquePair n) : Integrable
      (fun c : CliquePair n → CappedColor =>
        CappedColor.adjacency (c e) * CappedColor.adjacency (c f)) (ν : Measure _) := by
    let F : C(CliquePair n → CappedColor, ℝ) :=
      ⟨fun c => CappedColor.adjacency (c e) * CappedColor.adjacency (c f), by fun_prop⟩
    exact Integrable.of_bound F.continuous.aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall fun c => F.norm_coe_le_norm c)
  have hterm (e f : CliquePair n) :
      (∫ c : CliquePair n → CappedColor,
        CappedColor.adjacency (c e) * CappedColor.adjacency (c f) ∂(ν : Measure _)) ≤
        m ^ 2 + if pairOverlap e f then 1 else 0 := by
    by_cases h : pairOverlap e f
    · simp only [ite_eq_left h]
      have hle : (∫ c : CliquePair n → CappedColor,
          CappedColor.adjacency (c e) * CappedColor.adjacency (c f) ∂(ν : Measure _)) ≤ 1 := by
        have hi := integral_mono (hint e f) (integrable_const 1) (fun c => by
          have he := CappedColor.adjacency_mem (c e)
          have hf := CappedColor.adjacency_mem (c f)
          calc
            CappedColor.adjacency (c e) * CappedColor.adjacency (c f) ≤
                1 * CappedColor.adjacency (c f) :=
              mul_le_mul_of_nonneg_right he.2 hf.1
            _ ≤ 1 := by simpa using hf.2)
        simpa using hi
      nlinarith [sq_nonneg m]
    · simp only [ite_eq_right h, add_zero]
      have hdis : e.val.1 ≠ f.val.1 ∧ e.val.1 ≠ f.val.2 ∧
          e.val.2 ≠ f.val.1 ∧ e.val.2 ≠ f.val.2 := by
        simp only [pairOverlap, not_or] at h
        exact h
      have heq := integral_sampledColorLaw_disjoint_pairs W n e f
        hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2
        ⟨CappedColor.adjacency, CappedColor.continuous_adjacency⟩
        ⟨CappedColor.adjacency, CappedColor.continuous_adjacency⟩
      change (∫ c : CliquePair n → CappedColor,
        CappedColor.adjacency (c e) * CappedColor.adjacency (c f)
        ∂(ν : Measure _)) = m * m at heq
      nlinarith [heq]
  have hsum_sq (c : CliquePair n → CappedColor) :
      (∑ e : CliquePair n, CappedColor.adjacency (c e)) ^ 2 =
        ∑ e : CliquePair n, ∑ f : CliquePair n,
          CappedColor.adjacency (c e) * CappedColor.adjacency (c f) := by
    rw [sq, Finset.sum_mul_sum]
  have hcount : (∑ e : CliquePair n, ∑ f : CliquePair n,
      if pairOverlap e f then (1 : ℝ) else 0) ≤ (4 * n ^ 3 : ℕ) := by
    have h := overlap_count_le n
    have heq : (∑ e : CliquePair n, ∑ f : CliquePair n,
        if pairOverlap e f then (1 : ℝ) else 0) =
        (∑ e : CliquePair n,
          ((Finset.univ : Finset (CliquePair n)).filter (pairOverlap e)).card : ℕ) := by
      simp
    rw [heq]
    exact_mod_cast h
  calc
    (∫ c : CliquePair n → CappedColor,
      (∑ e : CliquePair n, CappedColor.adjacency (c e)) ^ 2 ∂(ν : Measure _)) =
        ∑ e : CliquePair n, ∑ f : CliquePair n,
          ∫ c : CliquePair n → CappedColor,
            CappedColor.adjacency (c e) * CappedColor.adjacency (c f) ∂(ν : Measure _) := by
      simp_rw [hsum_sq]
      rw [integral_finsetSum Finset.univ (fun e _ =>
        integrable_finsetSum _ (fun f _ => hint e f))]
      apply Finset.sum_congr rfl
      intro e _
      rw [integral_finsetSum Finset.univ (fun f _ => hint e f)]
    _ ≤ ∑ e : CliquePair n, ∑ f : CliquePair n,
        (m ^ 2 + if pairOverlap e f then 1 else 0) := by
      apply Finset.sum_le_sum
      intro e _
      exact Finset.sum_le_sum (fun f _ => hterm e f)
    _ = (Fintype.card (CliquePair n) : ℝ) ^ 2 * m ^ 2 +
        ∑ e : CliquePair n, ∑ f : CliquePair n,
          if pairOverlap e f then (1 : ℝ) else 0 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      dsimp [m]
      linarith

/-- The actual sampled density has uniformly vanishing squared error. -/
theorem sampleDensity_sq_error_le (W : Model Ω μ) (n : ℕ) (hn : 0 < n) :
    (∫ c : CliquePair n → CappedColor, (sampleDensity c - density W) ^ 2
      ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) ≤ 5 / (n : ℝ) := by
  let ν := sampledColorLaw W n
  let d := density W
  let S : C(CliquePair n → CappedColor, ℝ) :=
    ⟨fun c => ∑ e : CliquePair n, CappedColor.adjacency (c e), by fun_prop⟩
  let A : C(CliquePair n → CappedColor, ℝ) :=
    ⟨sampleDensity, by unfold sampleDensity; fun_prop⟩
  have hSsq : Integrable (fun c => (S c) ^ 2) (ν : Measure _) := by
    let F : C(CliquePair n → CappedColor, ℝ) := S ^ 2
    exact Integrable.of_bound F.continuous.aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall fun c => F.norm_coe_le_norm c)
  have hAsq : Integrable (fun c => (A c) ^ 2) (ν : Measure _) := by
    let F : C(CliquePair n → CappedColor, ℝ) := A ^ 2
    exact Integrable.of_bound F.continuous.aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall fun c => F.norm_coe_le_norm c)
  have hA : Integrable (fun c => A c) (ν : Measure _) := by
    exact Integrable.of_bound A.continuous.aestronglyMeasurable ‖A‖
      (Filter.Eventually.of_forall fun c => A.norm_coe_le_norm c)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hmean := integral_sampleDensity W n hn
  change (∫ c, A c ∂(ν : Measure _)) = (1 - 1 / (n : ℝ)) * d at hmean
  have hsecond := integral_adjacency_sum_sq_le W n
  have hm : (∫ p, W.moment CappedColor.adjacency p ∂μ.prod μ) = 2 * d := by
    dsimp [d, density]
    ring
  rw [hm] at hsecond
  change (∫ c, (S c) ^ 2 ∂(ν : Measure _)) ≤
    (Fintype.card (CliquePair n) : ℝ) ^ 2 * (2 * d) ^ 2 + (4 * n ^ 3 : ℕ) at hsecond
  have hAsq_bound : (∫ c, (A c) ^ 2 ∂(ν : Measure _)) ≤
      ((Fintype.card (CliquePair n) : ℝ) ^ 2 * (2 * d) ^ 2 + (4 * n ^ 3 : ℕ)) /
        (n : ℝ) ^ 4 := by
    have hAeq (c : CliquePair n → CappedColor) : (A c) ^ 2 =
        (S c) ^ 2 / (n : ℝ) ^ 4 := by
      dsimp [A, S, sampleDensity]
      ring
    simp_rw [hAeq, div_eq_mul_inv, integral_mul_const]
    exact mul_le_mul_of_nonneg_right hsecond (by positivity)
  have hexpand : (∫ c : CliquePair n → CappedColor, (A c - d) ^ 2 ∂(ν : Measure _)) =
      (∫ c, (A c) ^ 2 ∂(ν : Measure _)) -
        2 * d * (∫ c, A c ∂(ν : Measure _)) + d ^ 2 := by
    have heq (c : CliquePair n → CappedColor) : (A c - d) ^ 2 =
        (A c) ^ 2 - 2 * d * A c + d ^ 2 := by ring
    simp_rw [heq]
    rw [integral_add, integral_sub, integral_const_mul, integral_const]
    · simp
    · exact hAsq
    · exact hA.const_mul _
    · exact (hAsq.sub (hA.const_mul _))
    · exact integrable_const _
  have hcard : (Fintype.card (CliquePair n) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [card_cliquePair]
    exact Nat.cast_choose_two ℝ n
  have hdal : 0 ≤ d ∧ d ≤ 1 / 2 := density_mem W
  change (∫ c : CliquePair n → CappedColor, (A c - d) ^ 2 ∂(ν : Measure _)) ≤ _
  rw [hexpand]
  calc
    (∫ c, (A c) ^ 2 ∂(ν : Measure _)) -
        2 * d * (∫ c, A c ∂(ν : Measure _)) + d ^ 2 ≤
        ((Fintype.card (CliquePair n) : ℝ) ^ 2 * (2 * d) ^ 2 + (4 * n ^ 3 : ℕ)) /
          (n : ℝ) ^ 4 - 2 * d * ((1 - 1 / (n : ℝ)) * d) + d ^ 2 := by
      rw [hmean]
      linarith [hAsq_bound]
    _ = 4 / (n : ℝ) + d ^ 2 / (n : ℝ) ^ 2 := by
      rw [hcard]
      push_cast
      field_simp
      ring
    _ ≤ 5 / (n : ℝ) := by
      have hd2 : d ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (d - 1 / 2)]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hn2 : (0 : ℝ) < n ^ 2 := by positivity
      have hfrac : d ^ 2 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := by
        apply (div_le_iff₀ hn2).mpr
        have heq : (1 / (n : ℝ)) * (n : ℝ) ^ 2 = n := by
          field_simp
        rw [heq]
        linarith
      calc
        4 / (n : ℝ) + d ^ 2 / (n : ℝ) ^ 2 ≤
            4 / (n : ℝ) + 1 / (n : ℝ) := by linarith
        _ = 5 / (n : ℝ) := by ring

/-- The mean squared error of the actual colored sample tends to zero. -/
theorem sampleDensity_sq_error_tendsto (W : Model Ω μ) :
    Tendsto (fun n => ∫ c : CliquePair n → CappedColor,
      (sampleDensity c - density W) ^ 2
        ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)))
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => integral_nonneg (fun c => sq_nonneg _))
    (Filter.eventually_ge_atTop 1 |>.mono fun n hn =>
      sampleDensity_sq_error_le W n (by omega))
  simpa [div_eq_mul_inv] using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 5

/-- The expected absolute density error of the actual colored sample tends to zero. -/
theorem sampleDensity_abs_error_tendsto (W : Model Ω μ) :
    Tendsto (fun n => ∫ c : CliquePair n → CappedColor,
      |sampleDensity c - density W|
        ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (sampleDensity_sq_error_tendsto W)
    (ε ^ 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  let ν := sampledColorLaw W n
  let A : C(CliquePair n → CappedColor, ℝ) :=
    ⟨sampleDensity, by unfold sampleDensity; fun_prop⟩
  let F : C(CliquePair n → CappedColor, ℝ) :=
    ⟨fun c => |A c - density W|, by fun_prop⟩
  let G : C(CliquePair n → CappedColor, ℝ) :=
    ⟨fun c => (A c - density W) ^ 2, by fun_prop⟩
  have hF : Integrable (fun c => F c) (ν : Measure _) :=
    Integrable.of_bound F.continuous.aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall fun c => F.norm_coe_le_norm c)
  have hG : Integrable (fun c => G c) (ν : Measure _) :=
    Integrable.of_bound G.continuous.aestronglyMeasurable ‖G‖
      (Filter.Eventually.of_forall fun c => G.norm_coe_le_norm c)
  have hpoint (c : CliquePair n → CappedColor) :
      F c ≤ ε / 2 + G c / (2 * ε) := by
    dsimp [F, G]
    calc
      |A c - density W| ≤
          (ε ^ 2 + (A c - density W) ^ 2) / (2 * ε) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε)).mpr
        nlinarith [sq_nonneg (|A c - density W| - ε),
          sq_abs (A c - density W)]
      _ = ε / 2 + (A c - density W) ^ 2 / (2 * ε) := by
        field_simp
  have hupper : (∫ c, F c ∂(ν : Measure _)) ≤
      ε / 2 + (∫ c, G c ∂(ν : Measure _)) / (2 * ε) := by
    calc
      (∫ c, F c ∂(ν : Measure _)) ≤
          ∫ c, ε / 2 + G c / (2 * ε) ∂(ν : Measure _) := by
        apply integral_mono hF
          ((integrable_const _).add (hG.div_const _))
        exact hpoint
      _ = ε / 2 + (∫ c, G c ∂(ν : Measure _)) / (2 * ε) := by
        rw [integral_add (integrable_const _) (hG.div_const _)]
        simp only [integral_div, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hGsmall : (∫ c, G c ∂(ν : Measure _)) < ε ^ 2 := by
    have h := hN n hn
    change |(∫ c, G c ∂(ν : Measure _)) - 0| < ε ^ 2 at h
    rw [sub_zero, abs_of_nonneg (integral_nonneg (fun c => sq_nonneg _))] at h
    exact h
  have hfrac : (∫ c, G c ∂(ν : Measure _)) / (2 * ε) < ε / 2 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  change |(∫ c, F c ∂(ν : Measure _)) - 0| < ε
  have hFnonneg : 0 ≤ ∫ c, F c ∂(ν : Measure _) :=
    integral_nonneg (fun c => by dsimp [F]; exact abs_nonneg _)
  rw [sub_zero, abs_of_nonneg hFnonneg]
  linarith

end Erdos1017.CappedModel
