module

public import Erdos1017.Models.Capped.CappedSelectedLimit

/-!
# Shifted-color determinism in the cap limit

Squared-L2 convergence of selected shifted kernels preserves their squared
integrals, and weak color laws with strong squared-L2 kernels keep shifted-color
determinism and edge complementarity on the same limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual squared shifted kernel is integrable under its selected bound. -/
theorem integrable_shiftedMoment_sq (W : Model Ω μ) (m : ℝ)
    (hmem : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Set.Icc 0 4) :
    Integrable (fun p => (shiftedMoment W m p)^2) (μ.prod μ) := by
  apply Integrable.of_bound ((shiftedKernel_measurable W m).pow 2) 16
  filter_upwards [hmem] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (shiftedMoment W m p)^2 ≤ 16
  nlinarith [hp.1, hp.2, mul_nonneg hp.1 (sub_nonneg.mpr hp.2)]

/-- Actual squared-L2 convergence of uniformly selected shifted kernels
preserves their squared integrals. -/
theorem shiftedMoment_sq_integral_tendsto (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (m : ℕ → ℝ) (m₀ : ℝ)
    (hmem : ∀ n, ∀ᵐ p ∂μ.prod μ, shiftedMoment (W n) (m n) p ∈ Set.Icc 0 4)
    (hVmem : ∀ᵐ p ∂μ.prod μ, shiftedMoment V m₀ p ∈ Set.Icc 0 4)
    (hL2 : Tendsto (fun n => ∫ p, (shiftedMoment (W n) (m n) p - shiftedMoment V m₀ p)^2 ∂μ.prod μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p, (shiftedMoment (W n) (m n) p)^2 ∂μ.prod μ) atTop
      (𝓝 (∫ p, (shiftedMoment V m₀ p)^2 ∂μ.prod μ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsmall := hL2.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε^2 / 64))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨N, fun n hn => ?_⟩
  let f := shiftedMoment (W n) (m n)
  let g := shiftedMoment V m₀
  have hfs := integrable_shiftedMoment_sq (W n) (m n) (hmem n)
  have hgs := integrable_shiftedMoment_sq V m₀ hVmem
  have hq : Integrable (fun p => (f p - g p)^2) (μ.prod μ) := by
    apply Integrable.of_bound (((shiftedKernel_measurable (W n) (m n)).sub
      (shiftedKernel_measurable V m₀)).pow 2) 16
    filter_upwards [hmem n, hVmem] with p hp hq
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (shiftedMoment (W n) (m n) p - shiftedMoment V m₀ p)^2 ≤ 16
    have h₁ : 0 ≤ 4 - (shiftedMoment (W n) (m n) p - shiftedMoment V m₀ p) := by
      linarith [hp.2, hq.1]
    have h₂ : 0 ≤ 4 + (shiftedMoment (W n) (m n) p - shiftedMoment V m₀ p) := by
      linarith [hp.1, hq.2]
    nlinarith [mul_nonneg h₁ h₂]
  have hpoint : ∀ᵐ p ∂μ.prod μ, |f p^2 - g p^2| ≤ ε / 2 + (32 / ε) * (f p - g p)^2 := by
    filter_upwards [hmem n, hVmem] with p hp hq
    change shiftedMoment (W n) (m n) p ∈ Set.Icc 0 4 at hp
    change shiftedMoment V m₀ p ∈ Set.Icc 0 4 at hq
    have hp' : f p ∈ Set.Icc 0 4 := hp
    have hq' : g p ∈ Set.Icc 0 4 := hq
    rcases hp' with ⟨hf0, hf4⟩
    rcases hq' with ⟨hg0, hg4⟩
    have hfac : |f p^2 - g p^2| ≤ 8 * |f p - g p| := by
      rw [show f p^2 - g p^2 = (f p - g p) * (f p + g p) by ring, abs_mul,
        abs_of_nonneg (by linarith : 0 ≤ f p + g p)]
      nlinarith [abs_nonneg (f p - g p)]
    apply hfac.trans
    rw [show ε / 2 + (32 / ε) * (f p - g p)^2 =
      (ε^2 / 2 + 32 * (f p - g p)^2) / ε by field_simp]
    apply (le_div_iff₀ hε).2
    nlinarith [sq_nonneg (8 * |f p - g p| - ε), sq_abs (f p - g p)]
  have hbound := integral_mono_ae (hfs.sub hgs).abs
    ((integrable_const (ε / 2)).add (hq.const_mul (32 / ε))) hpoint
  change (∫ p, |f p^2 - g p^2| ∂μ.prod μ) ≤
    ∫ p, ε / 2 + (32 / ε) * (f p - g p)^2 ∂μ.prod μ at hbound
  rw [integral_add (integrable_const (ε / 2)) (hq.const_mul (32 / ε)), integral_const_mul] at hbound
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hbound
  rw [Real.dist_eq, ← integral_sub hfs hgs]
  apply lt_of_le_of_lt (le_trans abs_integral_le_integral_abs hbound)
  have hqsmall := hN n hn
  change (∫ p, (f p - g p)^2 ∂μ.prod μ) < ε^2 / 64 at hqsmall
  have hpos : 0 < 32 / ε := div_pos (by norm_num) hε
  have hmul := mul_lt_mul_of_pos_left hqsmall hpos
  have heq : (32 / ε) * (ε^2 / 64) = ε / 2 := by field_simp; ring
  rw [heq] at hmul
  linarith

/-- The fixed continuous second-moment test used at the limiting multiplier. -/
def shiftedSquareTest (m : ℝ) : C(CappedColor, ℝ) :=
  ⟨fun z => (shiftedColor m z)^2, (continuous_shiftedColor m).pow 2⟩

theorem shiftedColor_sq_sub_abs_le (m m' : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1)
    (z : CappedColor) (hz : shiftedColor m' z ∈ Set.Icc 0 4) :
    |(shiftedColor m z)^2 - (shiftedColor m' z)^2| ≤ 10 * |m - m'| := by
  have hmabs : ‖m‖ ≤ 3 := by rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨hm.1, hm.2.trans (by norm_num)⟩
  have hs : |shiftedColor m z| ≤ 6 := by
    simpa only [Real.norm_eq_abs] using (shiftedColor_norm_le m z).trans (by linarith)
  have ht : |shiftedColor m' z| ≤ 4 := by rw [abs_of_nonneg hz.1]; exact hz.2
  have hsum : |shiftedColor m z + shiftedColor m' z| ≤ 10 :=
    (abs_add_le _ _).trans (by linarith)
  rw [show (shiftedColor m z)^2 - (shiftedColor m' z)^2 =
    (shiftedColor m z - shiftedColor m' z) * (shiftedColor m z + shiftedColor m' z) by ring, abs_mul]
  calc
    _ ≤ |shiftedColor m z - shiftedColor m' z| * 10 :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ _ := by nlinarith [shiftedColor_sub_abs_le m m' z]

omit [IsProbabilityMeasure μ] in
/-- Determinism identifies each actual conditional second moment with the
square of the actual shifted mean, up to the changing multiplier error. -/
theorem shiftedSquareTest_moment_sub_abs_le (W : Model Ω μ) (m m₀ : ℝ)
    (hm₀ : m₀ ∈ Set.Icc (-3 : ℝ) 1)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p, shiftedColor m z = shiftedMoment W m p)
    (hmem : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Set.Icc 0 4) :
    ∀ᵐ p ∂μ.prod μ, |W.moment (shiftedSquareTest m₀) p - (shiftedMoment W m p)^2| ≤ 10 * |m₀ - m| := by
  filter_upwards [hdet, hmem] with p hp hmp
  let f := shiftedSquareTest m₀
  have hif : Integrable f (W.kernel p) := Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Eventually.of_forall f.norm_coe_le_norm)
  have heq : W.moment f p - (shiftedMoment W m p)^2 =
      ∫ z, f z - (shiftedMoment W m p)^2 ∂W.kernel p := by
    rw [integral_sub hif (integrable_const _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, DecoratedKernel.moment]
  rw [heq]
  have hbound : ∀ᵐ z ∂W.kernel p, ‖f z - (shiftedMoment W m p)^2‖ ≤ 10 * |m₀ - m| := by
    filter_upwards [hp] with z hz
    change |(shiftedColor m₀ z)^2 - (shiftedMoment W m p)^2| ≤ _
    rw [← hz]
    exact shiftedColor_sq_sub_abs_le m₀ m hm₀ z (hz.symm ▸ hmp)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hbound

omit [IsProbabilityMeasure μ] in
/-- The actual conditional variance is the actual second moment minus
the square of the actual conditional mean. -/
theorem shifted_variance_identity (W : Model Ω μ) (m : ℝ) (p : Ω × Ω) :
    (∫ z, (shiftedColor m z - shiftedMoment W m p)^2 ∂W.kernel p) =
      W.moment (shiftedSquareTest m) p - (shiftedMoment W m p)^2 := by
  let M := shiftedMoment W m p
  let f := shiftedSquareTest m
  have hi : Integrable (shiftedColor m) (W.kernel p) :=
    Integrable.of_bound (continuous_shiftedColor m).aestronglyMeasurable (3 + ‖m‖)
      (Eventually.of_forall (shiftedColor_norm_le m))
  have hisq : Integrable f (W.kernel p) := Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Eventually.of_forall f.norm_coe_le_norm)
  calc
    _ = ∫ z, (f z - (2 * M) * shiftedColor m z) + M^2 ∂W.kernel p := by
      apply integral_congr_ae
      filter_upwards with z
      change (shiftedColor m z - M)^2 = (shiftedColor m z)^2 - (2 * M) * shiftedColor m z + M^2
      ring
    _ = _ := by
      rw [integral_add (f := fun z => f z - (2 * M) * shiftedColor m z) (g := fun _ => M^2)
        (hisq.sub (hi.const_mul (2 * M))) (integrable_const _),
        integral_sub (f := fun z => f z) (g := fun z => (2 * M) * shiftedColor m z)
          hisq (hi.const_mul (2 * M)), integral_const_mul]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      change W.moment f p - (2 * M) * M + M^2 = W.moment f p - M^2
      ring

omit [IsProbabilityMeasure μ] in
/-- Actual shifted-color determinism also gives edge complementarity,
using the actual absent-or-present capped color space. -/
theorem shifted_complementary_of_deterministic (W : Model Ω μ) (m : ℝ)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p, shiftedColor m z = shiftedMoment W m p) :
    ∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0 := by
  have hcolor (z : CappedColor) : (1 - CappedColor.adjacency z) * shiftedColor m z = 0 := by
    change (1 - z.val.1) * (z.val.2 - m * z.val.1) = 0
    rcases z.property with h | h
    · have h₁ : z.val.1 = 0 := h.1
      have h₂ : z.val.2 = 0 := h.2
      simp [h₁, h₂]
    · have h₁ : z.val.1 = 1 := h.1
      simp [h₁]
  filter_upwards [hdet] with p hp
  calc
    _ = ∫ z, (1 - CappedColor.adjacency z) * shiftedMoment W m p ∂W.kernel p := by
      rw [integral_mul_const, integral_sub (integrable_const _) (integrable_color_adjacency W p)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, DecoratedKernel.moment]
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hp] with z hz
      rw [← hz]
      exact hcolor z

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Actual weak color laws and actual strong squared-L2 kernels retain
shifted-color determinism on that same model limit. -/
theorem shifted_deterministic_of_jointLaw_L2_limit (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (m : ℕ → ℝ) (m₀ : ℝ) (hm₀ : m₀ ∈ Set.Icc (-3 : ℝ) 1)
    (hweak : Tendsto (fun n => (W n).jointLaw) atTop (𝓝 V.jointLaw))
    (hm : Tendsto m atTop (𝓝 m₀))
    (hdet : ∀ n, ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂(W n).kernel p,
      shiftedColor (m n) z = shiftedMoment (W n) (m n) p)
    (hmem : ∀ n, ∀ᵐ p ∂μ.prod μ, shiftedMoment (W n) (m n) p ∈ Set.Icc 0 4)
    (hVmem : ∀ᵐ p ∂μ.prod μ, shiftedMoment V m₀ p ∈ Set.Icc 0 4)
    (hL2 : Tendsto (fun n => ∫ p, (shiftedMoment (W n) (m n) p - shiftedMoment V m₀ p)^2 ∂μ.prod μ)
      atTop (𝓝 0)) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂V.kernel p, shiftedColor m₀ z = shiftedMoment V m₀ p := by
  let f := shiftedSquareTest m₀
  have hif (X : Model Ω μ) : Integrable (X.moment f) (μ.prod μ) :=
    integrable_bounded_moment X f f.continuous.stronglyMeasurable ‖f‖ f.norm_coe_le_norm
  have hisq (n : ℕ) := integrable_shiftedMoment_sq (W n) (m n) (hmem n)
  have hdiffbound (n : ℕ) :
      |(∫ p, (W n).moment f p ∂μ.prod μ) - (∫ p, (shiftedMoment (W n) (m n) p)^2 ∂μ.prod μ)| ≤
        10 * |m₀ - m n| := by
    rw [← integral_sub (hif (W n)) (hisq n)]
    have hb := shiftedSquareTest_moment_sub_abs_le (W n) (m n) m₀ hm₀ (hdet n) (hmem n)
    have hb' : ∀ᵐ p ∂μ.prod μ, ‖(W n).moment f p - (shiftedMoment (W n) (m n) p)^2‖ ≤ 10 * |m₀ - m n| := by
      simpa only [Real.norm_eq_abs] using hb
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb'
  have hdiffzero : Tendsto (fun n => (∫ p, (W n).moment f p ∂μ.prod μ) -
      (∫ p, (shiftedMoment (W n) (m n) p)^2 ∂μ.prod μ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [Real.norm_eq_abs]
    apply squeeze_zero (fun _ => abs_nonneg _) hdiffbound
    simpa using (((tendsto_const_nhds : Tendsto (fun _ : ℕ => m₀) atTop (𝓝 m₀)).sub hm).abs.const_mul 10)
  have hsecond := DecoratedKernel.integral_moment_tendsto_of_jointLaw W V hweak f
  have hsq := shiftedMoment_sq_integral_tendsto W V m m₀ hmem hVmem hL2
  have heq : (∫ p, V.moment f p ∂μ.prod μ) = ∫ p, (shiftedMoment V m₀ p)^2 ∂μ.prod μ :=
    sub_eq_zero.mp (tendsto_nhds_unique (hsecond.sub hsq) hdiffzero)
  have hiV := integrable_shiftedMoment_sq V m₀ hVmem
  have hvarnonneg (p : Ω × Ω) : 0 ≤ V.moment f p - (shiftedMoment V m₀ p)^2 := by
    rw [← shifted_variance_identity]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hvarzero : (∫ p, V.moment f p - (shiftedMoment V m₀ p)^2 ∂μ.prod μ) = 0 := by
    rw [integral_sub (hif V) hiV, heq, sub_self]
  have hpzero := (integral_eq_zero_iff_of_nonneg hvarnonneg ((hif V).sub hiV)).mp hvarzero
  filter_upwards [hpzero] with p hp
  have hinner : Integrable (fun z => (shiftedColor m₀ z - shiftedMoment V m₀ p)^2) (V.kernel p) := by
    let g : C(CappedColor, ℝ) :=
      ⟨fun z => (shiftedColor m₀ z - shiftedMoment V m₀ p)^2,
        ((continuous_shiftedColor m₀).sub continuous_const).pow 2⟩
    exact Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖
      (Eventually.of_forall g.norm_coe_le_norm)
  have hz : (∫ z, (shiftedColor m₀ z - shiftedMoment V m₀ p)^2 ∂V.kernel p) = 0 :=
    (shifted_variance_identity V m₀ p).trans hp
  have hc := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hinner).mp hz
  exact hc.mono (fun _ hc => sub_eq_zero.mp (sq_eq_zero_iff.mp hc))

end Erdos1017.CappedModel
